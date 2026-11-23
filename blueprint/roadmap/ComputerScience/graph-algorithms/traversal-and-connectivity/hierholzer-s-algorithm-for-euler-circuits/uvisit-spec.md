# Invariant of the undirected Hierholzer recursion

Let $R$ be a list of edges, $v$, $t$
vertices such that exactly $v$ and $t$ have odd degree in $R$ (no vertex when $v = t$), $A$ a list
of vertices, and $f > |R|$ a fuel bound. Run the undirected Hierholzer recursion with fuel $f$
from $v$ on $R$ with accumulator $A$, and let $R'$ be the remaining edge list it returns and $c$
its cost. Then there is a vertex sequence $W$ starting at $v$ and ending at $t$ such that the
returned vertex list is $W$ followed by $A$; the edges of $R$, as unordered pairs, are a
permutation of the consecutive pairs of $W$ followed by the edges of $R'$, all as unordered pairs;
every vertex has even degree in $R'$; every vertex of $W$ has degree $0$ in $R'$; $R'$ is a
sublist of $R$; and $c + |R'| = |R|$.
