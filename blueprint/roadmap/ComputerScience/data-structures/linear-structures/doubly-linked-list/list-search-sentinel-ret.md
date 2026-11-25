# Sentinel search returns the first matching node

If a store circularly represents the list
$L$ of data nodes with sentinel $s$, then sentinel search for a key $k$ returns the first node of
$L$ (in list order, which starts at the successor of $s$) whose key in the input store is $k$, and
returns no node if no node of $L$ has key $k$. In particular, the sentinel is never returned.
