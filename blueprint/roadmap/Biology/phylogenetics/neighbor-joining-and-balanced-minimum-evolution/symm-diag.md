# Neighbor joining preserves symmetry and zero diagonal

Let $d$ be a symmetric dissimilarity on a finite set $X$ with $d(x, x) = 0$, and let a [run of neighbor joining](../neighbor-joining/njrun.md) on $d$ reach the cluster set $S$ with cluster dissimilarity $D$. Then $D(u, v) = D(v, u)$ for all clusters $u, v$, and $D(u, u) = 0$ for every $u \in S$.
