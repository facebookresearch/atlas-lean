# Treap insertion

For a key $k$ of a linearly ordered key type, a value $v$, a priority
$p$ and a tree $t$, inserting $k$ with value $v$ and priority $p$ into $t$ splits $t$ at $k$,
drops the entry the split finds at $k$ if any, merges the part below $k$ with the single node
$(k, v, p)$, and then merges the result with the part above $k$; all merges are
priority-guided.
