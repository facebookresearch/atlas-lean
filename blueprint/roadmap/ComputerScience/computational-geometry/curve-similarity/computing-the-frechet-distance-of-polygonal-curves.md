# Computing the Fréchet distance of polygonal curves

The Fréchet distance between two polygonal curves of total complexity $n$ in $\mathbb{R}^d$, for fixed $d$, can be computed in $O(n^2 \log n)$ time (Alt and Godau). The algorithm in the cited chapter searches over the critical values of $\delta$, at which the free-space structure changes, with the decision procedure as an oracle; its running-time bound holds with high probability.

## Depends on

- [Fréchet distance of curves](frechet-distance-of-curves.md)

## Proof depends on

- [Deciding whether the Fréchet distance is at most δ](deciding-whether-the-frechet-distance-is-at-most-delta.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Theorem 33.2.12 (the algorithm computes the Fréchet distance in $O(n^2 \log n)$ time, with high probability)
- K. Bringmann, "Why walking the dog takes time: Fréchet distance has no strongly subquadratic algorithms unless SETH fails", arXiv:1404.1448, <https://arxiv.org/abs/1404.1448>: abstract (Alt and Godau's algorithm computes the Fréchet distance of two polygonal curves with $n$ vertices in $O(n^2 \log n)$ time)
