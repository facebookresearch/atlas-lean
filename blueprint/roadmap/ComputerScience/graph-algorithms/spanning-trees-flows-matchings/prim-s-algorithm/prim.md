# Prim's algorithm with an indexed binary heap

Let $W$ be a linearly ordered type with a
zero element, let $W \cup \{\top\}$ be $W$ with a new greatest element $\top$ adjoined, let $D$
be a directed adjacency structure on the vertices $0, \dots, n-1$, with vertex list $L$ and
adjacency lists $A(u)$, let $w$ assign a weight $w(\{u, v\}) \in W$ to every unordered pair
$\{u, v\}$ of vertices, not necessarily distinct, and let $r$ be a vertex. Prim's algorithm
starts with no vertex having a parent and inserts the vertices, in the order of $L$, into an
empty indexed minimum queue over the identities $0, \dots, n-1$, with key $0$ for $r$ and key
$\top$ for every other vertex. It then repeats the following at most $n$ times, stopping early
when the queue is empty: it extracts the entry of minimum key, ties broken by the smaller
vertex, say with vertex $u$, and for each entry $v$ of $A(u)$ in order, if $v$ is still in the
queue and $w(\{u, v\})$ is strictly smaller than the current key of $v$, it sets the parent of
$v$ to $u$ and decreases the key of $v$ to $w(\{u, v\})$. It returns, for each vertex, its
parent or nothing.

Costs are counted as seven numbers: the five event counts of the queue operations (comparisons,
swaps, reads of the position vector, writes to the position vector, and entry appends, pops or
replacements), the number of adjacency entries inspected, and the number of inspected entries
found still in the queue, which is the number of key comparisons. On a disconnected graph every
vertex is still extracted and the parents form a forest.
