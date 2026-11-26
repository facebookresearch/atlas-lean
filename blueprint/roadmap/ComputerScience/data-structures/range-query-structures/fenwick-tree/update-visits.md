# Fenwick point-update visits

For a natural array length $n$ and one-indexed input
position $i$, list the one-indexed stored entries visited in order, starting from $i$ and
repeatedly adding the current index's lowest set bit. Only indices in $[1,n]$ are visited:
if $i=0$ or $i>n$ (including all inputs when $n=0$), the list is empty. An update at a
zero-indexed array position $p$ uses $i=p+1$.
