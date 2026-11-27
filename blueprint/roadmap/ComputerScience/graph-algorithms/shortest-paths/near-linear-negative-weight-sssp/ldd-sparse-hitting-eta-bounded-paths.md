# A directed LDD hits eta-bounded shortest paths O(log^2 n) times in expectation

Let $G=(V,E,w)$ have integer weights, let $B\ge 1$ with $w(e)\ge -2B$ for all $e$, and let $\Delta\ge 2$ be such that $\eta(G^B)\le\Delta$. Let $G^B_{\ge 0}$ carry the weights $\max\{0,w^B(e)\}$ and let $E^{rem}=\mathrm{LowDiamDecomposition}(G^B_{\ge 0},\Delta B/2)$ be the edge set output by a weak directed low-diameter decomposition with overhead $O(\log^2 n)$ and diameter parameter $\Delta B/2$, with strongly connected components $V_1,V_2,\dots$ of $G^B\setminus E^{rem}$. Then

1. $\mathrm{dist}_G(u,v)\le \Delta B/2$ for all $u,v$ in a common $V_i$, and
2. for every $v\in V$, $\mathbb{E}\big[|P_{G^B}(v)\cap E^{rem}|\big]=O(\log^2 n)$.

## Proof sketch

Item 1 holds because $w\le \max\{0,w^B\}$ edgewise, so distances in $G$ are at most those in $G^B_{\ge 0}$, which are at most $\Delta B/2$ inside a component by the weak-diameter guarantee. For item 2, the path $P=P_{G^B}(v)$ starts at the dummy source with a weight-$0$ edge and has $w^B(P)\le 0$; raising each of its at most $\eta_{G^B}(v)\le\Delta$ negative edges by at most $B$ gives $\sum_{e\in P}\max\{0,w^B(e)\}\le \Delta B$. Summing the hitting probabilities $O(\max\{0,w^B(e)\}\log^2 n/(\Delta B/2)+n^{-10})$ over the at most $n$ edges of $P$ gives $O(\log^2 n)$.

## Depends on

- [The negative-edge count eta of shortest paths and the B-shifted graph](negative-edge-count-eta.md)
- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)

## Proof depends on

- [A weak directed low-diameter decomposition with overhead O(log^2 n) in near-linear time](bnw-weak-directed-ldd.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
