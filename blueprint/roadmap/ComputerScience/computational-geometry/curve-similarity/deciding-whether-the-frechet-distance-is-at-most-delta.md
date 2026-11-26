# Deciding whether the Fréchet distance is at most δ

Let $\pi$ and $\sigma$ be polygonal curves in $\mathbb{R}^d$ with $n$ and $m$ segments and let $\delta \ge 0$. The free space of $\pi$ and $\sigma$ is the set of $(x, y)$ in the parameter rectangle with $\|\pi(x) - \sigma(y)\| \le \delta$; it is convex in each of the $nm$ cells formed by pairs of segments. One can decide whether $d_F(\pi, \sigma) \le \delta$, and if so compute a pair of monotone parameterizations realizing leash length at most $\delta$, in $O(nm)$ time, by propagating through the cells, in increasing order, the intervals of their boundaries reachable from $(0,0)$ by a monotone path in the free space. Moreover an optimal walk crosses each cell along a straight segment.

## Depends on

- [Fréchet distance of curves](frechet-distance-of-curves.md)

## Proof depends on

- [The free space of two segments is convex](the-free-space-of-two-segments-is-convex.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Lemma 33.2.6 (the optimal walk is polygonal, straight in each cell) and Lemma 33.2.8 (deciding $d_F(\pi, \sigma) \le \delta$ in time linear in the number of reachable free-space cells)
