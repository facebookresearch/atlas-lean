# A weak directed low-diameter decomposition with overhead O(log^2 n) in near-linear time

There is a randomized algorithm $\mathrm{LowDiamDecomposition}(G,D)$ that, given a directed graph $G=(V,E,w)$ with $n$ vertices, $m$ edges and nonnegative integer weights and a positive integer $D$, outputs $E^{rem}\subseteq E$ such that every strongly connected component of $G\setminus E^{rem}$ has weak diameter at most $D$ (that is, $\mathrm{dist}_G(u,v)\le D$ and $\mathrm{dist}_G(v,u)\le D$ for $u,v$ in the same component), and for every $e\in E$,

$$
\Pr[e\in E^{rem}]=O\Big(\frac{w(e)\log^2 n}{D}+n^{-10}\Big).
$$

Its running time is $O(m\log^2 n+n\log^3 n)$. In the terminology of directed LDDs this is a weak LDD with overhead $O(\log^2 n)$.

## Proof sketch

Estimate, by sampling $O(\log n)$ random vertices and running Dijkstra from and to them, which vertices are in-light or out-light, meaning their in-ball or out-ball of radius $D/4$ contains at most a constant fraction of the vertices. Around each light vertex carve a ball of geometrically distributed radius with mean $\Theta(D/\log n)$, delete its boundary edges, and recurse on both the ball and the rest. The memoryless property gives cut probability $O(w(e)\log n/D)$ per recursion level and the shrinking vertex count gives $O(\log n)$ levels; once only heavy vertices remain, any two of them have overlapping large balls and hence weak distance at most $D$.

## Depends on

- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
