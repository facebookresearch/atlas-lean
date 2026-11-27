# The free space of two segments is convex

Let $\pi, \sigma : [0, 1] \to \mathbb{R}^d$ be two segments parameterized at constant speed, and let $\operatorname{elev}(x, y) = \|\pi(x) - \sigma(y)\|$ on $[0,1]^2$. Then $\operatorname{elev}$ is a convex function, since it is the norm of the affine map $(x, y) \mapsto \pi(x) - \sigma(y)$. Hence for every $\delta \ge 0$ the *free space* $\{(x, y) \in [0,1]^2 : \operatorname{elev}(x, y) \le \delta\}$ is convex; when the affine map is injective it is an ellipse clipped to the unit square. For a fixed $x_0$ the set of $y$ with $\operatorname{elev}(x_0, y) \le \delta$ is an interval computable in constant time for fixed $d$.

## Depends on

- [Fréchet distance of curves](frechet-distance-of-curves.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Lemma 33.2.1 (the sublevel set is an ellipse clipped to the unit square), Corollary 33.2.3 (the elevation function is convex) and Observation 33.2.4
