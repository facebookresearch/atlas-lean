# List model of breadth-first search

Given a finite directed graph $G$ with ordered
adjacency lists and a source vertex $s$, the list model keeps a list of processed pairs and a
queue of pairs $(v, d)$ of a vertex and a distance, starting with no processed pairs and the
queue $[(s, 0)]$. It performs one round per vertex of $G$: if the queue is empty, nothing
changes; otherwise the front pair $(u, d)$ is removed from the queue and recorded as processed,
and then each entry $w$ of the adjacency list of $u$, from left to right, is appended to the
queue as $(w, d + 1)$ unless $w$ already occurs in a processed or queued pair. The reported
distance of a vertex $v$ is the distance in the first pair for $v$ in the list of processed pairs
in processing order followed by the queue, or none if there is no such pair; the reported order
lists the processed vertices in processing order.

The model can be evaluated by kernel reduction, which is used to check concrete results.
