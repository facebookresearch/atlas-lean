# Deciding whether the Fréchet distance is at most δ

Let $\pi$ and $\sigma$ be polygonal curves in $\mathbb{R}^d$ with $n$ and $m$ segments and let $\delta \ge 0$. The free space of $\pi$ and $\sigma$ is the set of $(x, y)$ in the parameter rectangle with $\|\pi(x) - \sigma(y)\| \le \delta$; it is convex in each of the $nm$ cells formed by pairs of segments. Then $d_F(\pi, \sigma) \le \delta$ if and only if the free space contains a path from $(0,0)$ to $(n,m)$ that is monotone (non-decreasing in both coordinates), and one can decide this, and compute such a path, in $O(nm)$ time by propagating through the cells, in increasing order, the intervals of their boundaries reachable from $(0,0)$. If such a path exists, one exists that crosses each cell along a straight segment. A monotone path corresponds to non-decreasing surjective parameterizations, which need not be bijective: the infimum in the definition need not be attained by reparameterizations.

## Depends on

- [Fréchet distance of curves](frechet-distance-of-curves.md)

## Proof depends on

- [The free space of two segments is convex](the-free-space-of-two-segments-is-convex.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Lemma 33.2.6 (a walk can be taken polygonal, straight in each cell) and Lemma 33.2.8 (deciding $d_F(\pi, \sigma) \le \delta$ in time linear in the number of reachable free-space cells)
