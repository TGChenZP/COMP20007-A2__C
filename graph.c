/*
graph.c

Set of vertices and edges implementation.

Implementations for helper functions for graph construction and manipulation.

Skeleton written by Grady Fitzpatrick for COMP20007 Assignment 1 2021
*/
#include <stdlib.h>
#include <assert.h>
#include <limits.h>
#include "graph.h"
#include "utils.h"
#include "pq.h"
#include <math.h>

#define INITIALEDGES 32

struct edge;

/* Definition of a graph. */
struct graph {
  int numVertices;
  int numEdges;
  int allocedEdges;
  struct edge **edgeList;
};

/* Definition of an edge. */
struct edge {
  int start;
  int end;
};

void swap(int*, int*);

void insertion_sort(int*, int);

void preprocess(int*,int*, int, int, int, int*, int*);

void diekstra(int*, int, int*, int, int*, int*, int);

void
swap(int*p1, int*p2){
	int tmp;
	tmp = *p1;
	*p1 = *p2;
	*p2 = tmp;
}

void
insertion_sort(int final[],int currmax){
	int i, j;
	
    for (i=0; i < currmax; i++){
    	j = i-1;
    	while ((j>=0) && final[j+1] < final[j]){
    		swap(&final[j], &final[j+1]);
    		j--;
    	}
    }
}

struct graph *newGraph(int numVertices){
  struct graph *g = (struct graph *) malloc(sizeof(struct graph));
  assert(g);
  /* Initialise edges. */
  g->numVertices = numVertices;
  g->numEdges = 0;
  g->allocedEdges = 0;
  g->edgeList = NULL;
  return g;
}

/* Adds an edge to the given graph. */
void addEdge(struct graph *g, int start, int end){
  assert(g);
  struct edge *newEdge = NULL;
  /* Check we have enough space for the new edge. */
  if((g->numEdges + 1) > g->allocedEdges){
    if(g->allocedEdges == 0){
      g->allocedEdges = INITIALEDGES;
    } else {
      (g->allocedEdges) *= 2;
    }
    g->edgeList = (struct edge **) realloc(g->edgeList,
      sizeof(struct edge *) * g->allocedEdges);
    assert(g->edgeList);
  }

  /* Create the edge */
  newEdge = (struct edge *) malloc(sizeof(struct edge));
  assert(newEdge);
  newEdge->start = start;
  newEdge->end = end;

  /* Add the edge to the list of edges. */
  g->edgeList[g->numEdges] = newEdge;
  (g->numEdges)++;
}

/* Frees all memory used by graph. */
void freeGraph(struct graph *g){
  int i;
  for(i = 0; i < g->numEdges; i++){
    free((g->edgeList)[i]);
  }
  if(g->edgeList){
    free(g->edgeList);
  }
  free(g);
}

/* Finds:
  - Number of connected subnetworks (before outage) (Task 2)
  - Number of servers in largest subnetwork (before outage) (Task 3)
  - SIDs of servers in largest subnetwork (before outage) (Task 3)
  - Diameter of largest subnetworks (after outage) (Task 4)
  - Number of servers in path with largest diameter - should be one more than
    Diameter if a path exists (after outage) (Task 4)
  - SIDs in path with largest diameter (after outage) (Task 4)
  - Number of critical servers (before outage) (Task 7)
  - SIDs of critical servers (before outage) (Task 7)
*/
struct solution *graphSolve(struct graph *g, enum problemPart part,
  int numServers, int numOutages, int *outages){
  struct solution *solution = (struct solution *)
    malloc(sizeof(struct solution));
  assert(solution);
  /* Initialise solution values */
  initaliseSolution(solution);
  if(part == TASK_2){
    /* IMPLEMENT TASK 2 SOLUTION HERE */
    int marker = 0, subnetworks = 0, i, j, c, strt, en, stackcontrol=0;
    int *inserted, *Marked, *M, *stack;
    	
    inserted = (int*)malloc(sizeof(int)*numServers);
    Marked = (int*)malloc(sizeof(int)*numServers);
    M = (int*)malloc(sizeof(int)*numServers*numServers);
    stack = (int*)malloc(sizeof(int)*numServers);
    
    if (numServers != 0){
    	subnetworks = 1;
    }
    
    for (i=0; i<numServers; i++){
    	Marked[i] = 0;	
    	stack[i] = -1;
    	inserted[i] = 0;
    }
    
    /* initiate the adjacency matrix */
    for (i=0; i<numServers*numServers; i++){
    	M[i] = 0;
    }

    /* setup the adjacency matrix */
    for (i=0; i<g->numEdges; i++){
    	strt = g->edgeList[i]->start;
    	en = g->edgeList[i]->end;
    	M[strt*numServers+en] = 1;
    	M[en*numServers+strt] = 1;
    }
    
    stack[0] = 0;
    inserted[0] = 1;
    
    while (marker != numServers){
    	if (stackcontrol < 0) {
    		subnetworks++;
    		for (j=0; j<numServers; j++){
    			if (Marked[j] == 0){
    				c = j;
    				inserted[c] = 1;
    				break;
    			}
    		}
    	} else {
    		c = stack[stackcontrol];
    		stack[stackcontrol] = -1;
    		stackcontrol--;
    	}
    	
    	marker ++;
    	Marked[c] = marker;

    	for (j=c*numServers; j < (c+1)*numServers; j++){
    		if (M[j] == 1 && inserted[j%numServers] ==0){
    			stackcontrol++;
    			stack[stackcontrol]=(j%numServers);
    			inserted[j%numServers] = 1;
    		}
    	}
    }
    
    solution->connectedSubnets = subnetworks;
    
    free(Marked);
    free(inserted);
    free(stack);
    free(M);
    
  } else if(part == TASK_3) {
    /* IMPLEMENT TASK 3 SOLUTION HERE */
    int marker = 0, i, j, c, strt, en, stackcontrol=0,
    	count=0, currmax=0, *Marked, *M, *stack, *inserted, *final, *order;
    
    Marked = (int*)malloc(sizeof(int)*numServers);
    M = (int*)malloc(sizeof(int)*numServers*numServers);
	stack = (int*)malloc(sizeof(int)*numServers);
	inserted = (int*)malloc(sizeof(int)*numServers);
	final = (int*)malloc(sizeof(int)*numServers);
    order = (int*)malloc(sizeof(int)*numServers);
    	
    for (i=0; i<numServers; i++){
    	Marked[i] = 0;	
    	stack[i] = -1;
    	inserted[i] = 0;
    	final[i]=0;
    	order[i]=0;
    }
    
    /* initiate the adjacency matrix */
    for (i=0; i<numServers*numServers; i++){
    	M[i] = 0;
    }

    /* setup the adjacency matrix */
    for (i=0; i<g->numEdges; i++){
    	strt = g->edgeList[i]->start;
    	en = g->edgeList[i]->end;
    	M[strt*numServers+en] = 1;
    	M[en*numServers+strt] = 1;
    }
    
    stack[0] = 0;
    inserted[0] = 1;
    
    while (marker != numServers){
    	if (stackcontrol < 0) {
    		if (count > currmax){
    			currmax = count;
    			j=0;
    			for (i= marker-count; i<marker; i++){
    				final[j] = order[i];
    				j++;
    			}
    		}
    		count=0;
    		for (j=0; j<numServers; j++){
    			if (Marked[j] == 0){
    				c = j;
    				inserted[c] = 1;
    				break;
    			}
    		}
    	} else {
    		c = stack[stackcontrol];
    		stack[stackcontrol] = -1;
    		stackcontrol--;
    	}
    	
    	count++;
    	order[marker] = c;
    	marker++;
    	Marked[c] = marker;
    	
    	for (j=c*numServers; j < (c+1)*numServers; j++){
    		if (M[j] == 1 && inserted[j%numServers] ==0){
    			stackcontrol++;
    			stack[stackcontrol]=(j%numServers);
    			inserted[j%numServers] = 1;
    		}
    	}
    }
    if (count > currmax){
    	currmax = count;
    	j=0;
    	for (i= marker-count; i<marker; i++){
    		final[j] = order[i];
    		j++;
    	}
    }
    
    insertion_sort(final,currmax);
    
    solution->largestSubnet = currmax;
    solution->largestSubnetSIDs = final;
    
    free(Marked);
    free(M);
    free(stack);
    free(inserted);
    free(order);
    
  } else if(part == TASK_4) {
    /* IMPLEMENT TASK 4 SOLUTION HERE */
     int marker = 0, i, j, c, strt, en, stackcontrol=0, tmp,
    	count=0, globmax=0, *Marked, *M, *stack, *inserted, *final, *order;
    
    Marked = (int*)malloc(sizeof(int)*numServers);
    M = (int*)malloc(sizeof(int)*numServers*numServers);
	stack = (int*)malloc(sizeof(int)*numServers);
	inserted = (int*)malloc(sizeof(int)*numServers);
	final = (int*)malloc(sizeof(int)*numServers);
    order = (int*)malloc(sizeof(int)*numServers);
    	
    for (i=0; i<numServers; i++){
    	Marked[i] = 0;	
    	stack[i] = -1;
    	inserted[i] = 0;
    	final[i]=0;
    	order[i]=0;
    }
    
    /* initiate the adjacency matrix */
    for (i=0; i<numServers*numServers; i++){
    	M[i] = 0;
    }

    /* setup the adjacency matrix */
    for (i=0; i<g->numEdges; i++){
    	strt = g->edgeList[i]->start;
    	en = g->edgeList[i]->end;
    	M[strt*numServers+en] = 1;
    	M[en*numServers+strt] = 1;
    }
    
    for (i=0; i<numOutages; i++){
    	tmp = outages[i];
    	inserted[tmp]=1;
    	Marked[tmp]=-1;
    	
    	for (j=tmp*numServers; j<(tmp+1)*numServers; j++){
    		M[j] = 0;	
    	}
    	for (j=0; j<numServers; j++){
    		M[j*numServers+tmp] = 0;	
    	}
    }

    for (i=0; i<numServers; i++){
    	if 	(Marked[i] == 0){
    		/*printf("%d\n", i);*/
    		stack[0] = i;
    		inserted[i] = 1;
    		break;
    	}
    }
    		
    while (marker != numServers-numOutages){
    	if (stackcontrol < 0) {
    		
    		preprocess(M, order, count, marker, numServers, final, &globmax);

    		count=0;
    		for (j=0; j<numServers; j++){
    			if (Marked[j] == 0){
    				c = j;
    				inserted[c] = 1;
    				break;
    			}
    		}
  
    	} else {
    		c = stack[stackcontrol];
    		stack[stackcontrol] = -1;
    		stackcontrol--;
    	}
    	
    	count++;
    	order[marker] = c;
    	marker++;
    	Marked[c] = marker;
    	
    	for (j=c*numServers; j < (c+1)*numServers; j++){
    		if (M[j] == 1 && inserted[j%numServers] ==0){
    			stackcontrol++;
    			stack[stackcontrol]=(j%numServers);
    			inserted[j%numServers] = 1;
    		}
    	}
    }
    
    preprocess(M, order, count, marker, numServers, final, &globmax);
    
    solution->postOutageDiameter = globmax;
    solution->postOutageDiameterCount = globmax+1;
    solution->postOutageDiameterSIDs = final;
    
    free(Marked);
    free(M);
    free(stack);
    free(inserted);
    free(order);
    
  } else if(part == TASK_7) {
    /* IMPLEMENT TASK 7 SOLUTION HERE */
    int marker = 0, i, j, c, strt, en, stackcontrol=0, pushorder = 0, 
    	ncrit = 0, count = 0, prev=-1, *Marked, *M, *stack, *PO, *final, *order, 
    	*daddy, *sons, *HRA;
    
    Marked = (int*)malloc(sizeof(int)*numServers);
    M = (int*)malloc(sizeof(int)*numServers*numServers);
	stack = (int*)malloc(sizeof(int)*numServers);
	PO = (int*)malloc(sizeof(int)*numServers);
	final = (int*)malloc(sizeof(int)*numServers);
    order = (int*)malloc(sizeof(int)*numServers);
    daddy = (int*)malloc(sizeof(int)*numServers);
    sons =  (int*)malloc(sizeof(int)*numServers);
    HRA = (int*)malloc(sizeof(int)*numServers);
    	
    for (i=0; i<numServers; i++){
    	Marked[i] = 0;	
    	stack[i] = -1;
    	PO[i] = -1;
    	final[i] = 0;
    	order[i] = 0;
    	sons[i] = 0;
    	daddy[i] = -1;
    	HRA[i] = -1;
    }
    
    /* initiate the adjacency matrix */
    for (i=0; i<numServers*numServers; i++){
    	M[i] = 0;
    }

    /* setup the adjacency matrix */
    for (i=0; i<g->numEdges; i++){
    	strt = g->edgeList[i]->start;
    	en = g->edgeList[i]->end;
    	M[strt*numServers+en] = 1;
    	M[en*numServers+strt] = 1;
    }
    
    stack[0] = 0;
    PO[0] = pushorder;
    pushorder++;
    
    while (marker != numServers){
    	if (stackcontrol < 0) {
    		for (i= marker-1; i>=marker-count; i--){
				for (j=0; j<numServers; j++){
					if (daddy[j] == order[i] && PO[HRA[order[i]]] > PO[HRA[j]]){
						HRA[order[i]] = HRA[j];
					}
				}
			}
			
    		for (i=marker-count; i<marker; i++){
    			if (daddy[order[i]] != -1){
					sons[daddy[order[i]]]++;

				}
    		}
    		
    		for (i=marker-count; i<marker; i++){
				if (i == marker-count){
					if (sons[order[i]]>1){
						final[ncrit] = order[i];
						ncrit++;
					}
				} else if (sons[order[i]] != 0){
					for (j=0; j<numServers; j++){
						if (daddy[j] == order[i] && PO[HRA[j]] >= PO[order[i]]){
							final[ncrit] = order[i];
							ncrit++;
						}
					}
				}
			}
    		
    		count = 0;
    		for (j=0; j<numServers; j++){
    			if (Marked[j] == 0){
    				c = j;
    				PO[c] = pushorder;
    				pushorder++;
    				break;
    			}
    		}
    	} else {
    		c = stack[stackcontrol];
    		stack[stackcontrol] = -1;
    		stackcontrol--;
    	}
    	
    	count++;
    	order[marker] = c;
    	
    	marker++;
    	
    	Marked[c] = marker;
    	HRA[c] = c;
    	
    	for (j=c*numServers; j < (c+1)*numServers; j++){
    		if (M[j] == 1 && Marked[j%numServers] == 0){
    			if (PO[j%numServers] ==-1){
					stackcontrol++;
					stack[stackcontrol]=(j%numServers);
					PO[j%numServers] = pushorder;
					pushorder++;
					daddy[j%numServers] = c;
				} else{
					daddy[j%numServers] = c;
				}
    		}
    		if (M[j] == 1 && Marked[j%numServers] != 0){
    			if (j%numServers != prev && Marked[ HRA[c] ] > Marked[j%numServers]){
    				HRA[c] = j%numServers; 
    			}
    		}
    	}
    	prev = c;
    }
    
    for (i= marker-1; i>=marker-count; i--){
		for (j=0; j<numServers; j++){
   			if (daddy[j] == order[i] && PO[HRA[order[i]]] > PO[HRA[j]]){
   				HRA[order[i]] = HRA[j];
			}
  		}	
   	}
   	
    for (i=marker-count; i<marker; i++){
    	if (daddy[order[i]] != -1){
			sons[daddy[order[i]]]++;
		}
    }
    
    for (i=marker-count; i<marker; i++){
    	if (i == marker-count){
    		if (sons[order[i]]>1){
    			final[ncrit] = order[i];
    			ncrit++;
    		}
    	} else if (sons[order[i]] != 0){
    		for (j=0; j<numServers; j++){
    			if (daddy[j] == order[i] && PO[HRA[j]] >= PO[order[i]]){
    				final[ncrit] = order[i];
    				ncrit++;
    			}
    		}
    	}
    }
    
    solution->criticalServerCount = ncrit;
    solution->criticalServerSIDs = final;
    
    free(Marked);
    free(M);
    free(stack);
    free(PO);
    free(order);
    free(daddy);
    free(sons);
    free(HRA);
    
  }
  return solution;
}



void 
preprocess(int M[], int order[], int count, int marker, int numServers, int final[], int *globmax){
    int i, j, localmax=0;
    int *subnetwork, *localarr;
    
    subnetwork = (int*)malloc(sizeof(int)*count);
    localarr = (int*)malloc(sizeof(int)*count);
    			    			
    for (i=0; i<count; i++){
    	localarr[i]=0;
    }
    			
    j=0;
    for (i=marker-count; i<marker; i++){
    	subnetwork[j] = order[i];
    	j++;
    }
    insertion_sort(subnetwork, count);
    
    for (i=0; i<count; i++){
    	diekstra(M, count, subnetwork, numServers, &localmax, localarr, i);
    }
    if (localmax > *globmax){
    	*globmax = localmax;
    	for (i=0; i<=localmax; i++){
    		final[i] = localarr[i];	
    	}
    }
}

void diekstra(int M[], int count, int subnetwork[], int numServers, int *localmax, int localarr[], int index){
    int *tick, *last, *currval, *newsubnetwork;
    int i, j, c, counter=1, max=0, currmaxindex, currindex=0;
    
    tick = (int*)malloc(sizeof(int)*count);
    last = (int*)malloc(sizeof(int)*count);
    currval = (int*)malloc(sizeof(int)*count);
    newsubnetwork = (int*)malloc(sizeof(int)*count);
    					
    for (i=0; i<count; i++){
    	tick[i] = 0;
    	last[i] = -1;
    	currval[i] = INT_MAX;
   	}
   	
   	for (i=0; i<count; i++){
    	newsubnetwork[i] = subnetwork[i];
    }
   	
	swap(&newsubnetwork[0], &newsubnetwork[index]); 
    c = newsubnetwork[0];
    tick[0] = 1;
    currval[0] = 0;
					
    while (counter != count){
    	for (i=0; i<count; i++){
    		if ((M[c*numServers + newsubnetwork[i]] == 1) && (tick[i] == 0) && 
    			(currval[currindex]+1<currval[i])){
    			currval[i] = currval[currindex]+ 1;
    			last[i] = c;	
    		}
    	}
    					
    	for (i=0; i<count; i++){
    		if ((tick[i]==0) && (last[i] != -1)){
    			c = newsubnetwork[i];
    			currindex = i;
    			tick[i] = 1;
    			break;
    		}
    	}
    	counter++;
    }
    				
    for (i=0; i<count; i++){
    	if (currval[i]>max){
    		max = currval[i];
    		currmaxindex = i;
    	}
    }

	if (max > *localmax){	
		*localmax = max;
		localarr[max]=newsubnetwork[currmaxindex];
    	for (i=max-1; i>-1; i--){
			localarr[i] = last[currmaxindex];
			
			for (j=0; j<count; j++){
				if (newsubnetwork[j] == last[currmaxindex]){
					currmaxindex = j;
					break;
				}
			}
		}
	}
}