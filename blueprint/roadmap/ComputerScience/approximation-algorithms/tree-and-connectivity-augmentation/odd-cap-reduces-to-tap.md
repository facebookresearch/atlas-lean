# Augmenting odd edge-connectivity reduces to tree augmentation

Let $G=(V,E)$ be $k$-edge-connected with $k$ odd and $n=|V|$. Then the family of minimum cuts $\{S : |\delta_G(S)|=k\}$ is cross-free, and there is a tree $H$ on $O(n)$ nodes, computable in polynomial time, together with a map $\phi:V \to V(H)$ such that the minimum cuts of $G$ correspond bijectively to the edges of $H$. A link set $F$ makes $G$ $(k+1)$-edge-connected if and only if the mapped links $\{\phi(u)\phi(v) : uv \in F\}$ cover every edge of $H$. Hence WCAP with odd $k$ is equivalent to WTAP with the same weights. For even $k$ the minimum cuts form a cactus, which reduces WCAP to cactus augmentation.

## Proof sketch

Suppose minimum cuts $S,S'$ cross, with corners $A=S \cap S'$, $B=S \setminus S'$, $C=S' \setminus S$, $D=V \setminus (S \cup S')$. Submodularity and posimodularity of $|\delta(\cdot)|$ make all four corners minimum cuts and force $d(A,D)=d(B,C)=0$, where $d(X,Y)$ counts edges between $X$ and $Y$. Then $|\delta(A)|+|\delta(B)|=2d(A,B)+|\delta(S)|$ gives $2k=2d(A,B)+k$, so $k=2d(A,B)$ is even, a contradiction. A cross-free family of at most $2n$ sets is represented by a tree. For general $k$ the cactus representation of Dinits, Karzanov and Lomonosov applies, and the number of minimum cuts is at most $\binom{n}{2}$.

## Depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Weighted connectivity augmentation problem (WCAP)](connectivity-augmentation.md)
- [Minimum cut size](../../randomized-algorithms/karger-s-algorithm/is-min-cut.md)
- [Cactus representations of all minimum cuts](../../../GraphTheory/paths-cycles-connectivity/cactus-representation-and-sparse-certificates/cactus-representation-of-minimum-cuts.md)

## Proof depends on

- [At most $n(n-1)/2$ minimum cuts](../../randomized-algorithms/karger-s-algorithm/two-mul-length-min-cuts-le.md)

## Sources

- Efim A. Dinits, Alexander V. Karzanov, Michael V. Lomonosov, "On the Structure of a Family of Minimal Weighted Cuts in a Graph", Studies in Discrete Optimization (1976).
- Joseph Cheriyan, Tibor Jordan, R. Ravi, "On 2-Coverings and 2-Packings of Laminar Families", ESA (1999).
