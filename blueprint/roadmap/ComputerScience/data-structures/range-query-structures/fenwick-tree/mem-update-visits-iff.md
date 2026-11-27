# Exact membership in the Fenwick update walk

For natural length $n$, one-indexed
input position $i$, and candidate stored endpoint $j$, the update walk visits $j$ if and only
if $j \le n$ and $j-\operatorname{lowbit}(j)< i\le j$ (the one-indexed block ending at $j$
contains $i$). This condition excludes the dummy endpoint $0$ and is impossible for
$i=0$ or $i>n$, including every input when $n=0$.
