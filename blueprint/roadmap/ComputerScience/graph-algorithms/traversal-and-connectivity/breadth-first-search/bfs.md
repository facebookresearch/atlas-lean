# Breadth-first search

Given a finite directed graph $G$ with ordered adjacency lists and a
source vertex $s$, breadth-first search keeps a FIFO queue of pairs $(v, d)$ of a vertex and a
distance and a table of discovered vertices with their distances, starting with the queue
$[(s, 0)]$ and $s$ discovered at distance $0$. It performs one round per vertex of $G$: if the
queue is empty, nothing changes; otherwise it dequeues the front pair $(u, d)$, records $u$ as
processed, and scans the adjacency list of $u$ from left to right, enqueueing each entry $w$ that
is not yet discovered as $(w, d + 1)$ and discovering it at distance $d + 1$. The result reports
for each vertex its discovered distance, or none if it was never discovered, and lists the
processed vertices in processing order.

The table is a hash map, so the search runs in expected time linear in the number of vertices
plus the total length of the adjacency lists.
