# Skip-list insertion

To insert key $k$ with value $v$ and requested height $h$ into a
skip list, scan its bottom-level nodes in order, keeping every node whose key is less than $k$.
At the first node whose key is not less than $k$: if its key equals $k$, its value is replaced
by $v$ and its tower height is kept; if its key is greater than $k$, a new node with key $k$,
value $v$ and tower height $\max(1, h)$ is placed before it. If every key is less than $k$, the
new node is appended at the end.
