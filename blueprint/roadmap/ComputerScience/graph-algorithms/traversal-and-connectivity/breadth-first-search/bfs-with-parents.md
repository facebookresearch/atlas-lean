# Breadth-first search with parent pointers

Given a finite directed graph $G$ on a vertex
type $V$, with ordered adjacency lists, and a source vertex $s$, this runs first-in-first-out
breadth-first search from $s$ for $|V|$ rounds. The queue starts with $s$ at distance $0$. Each
round tries to dequeue a vertex $u$; if it succeeds, it scans the neighbors of $u$ in
adjacency-list order, and each neighbor not yet discovered gets distance one more than $u$,
records $u$ as its parent and is enqueued. An already discovered vertex keeps its distance and
parent. The result is the search forest: the distance of each discovered vertex, the vertices in
the order they were dequeued, and the parent of each discovered vertex other than $s$. The cost
counts one unit for each dequeue attempt, each check of an adjacency entry against the
discovered set, each enqueue (including that of $s$) and each parent write.
