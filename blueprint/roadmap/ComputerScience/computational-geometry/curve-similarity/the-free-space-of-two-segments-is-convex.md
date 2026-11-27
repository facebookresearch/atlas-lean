# The free space of two segments is convex

Let $\pi, \sigma : [0, 1] \to \mathbb{R}^d$ be two segments parameterized at constant speed, and let $\operatorname{elev}(x, y) = \|\pi(x) - \sigma(y)\|$ on $[0,1]^2$. Then $\operatorname{elev}$ is a convex function, since it is the norm of the affine map $(x, y) \mapsto \pi(x) - \sigma(y)$. Hence for every $\delta \ge 0$ the *free space* $\{(x, y) \in [0,1]^2 : \operatorname{elev}(x, y) \le \delta\}$ is convex; when the affine map is injective, with image the plane $F$, the set $A = \{(x, y) \in \mathbb{R}^2 : \pi(x) - \sigma(y) \in F,\ \|\pi(x) - \sigma(y)\| \le \delta\}$ of the whole parameter plane, with $\pi$ and $\sigma$ extended affinely to $\mathbb{R}$, is empty, a single point or a filled ellipse according as $\delta$ is less than, equal to or greater than the distance from the origin to $F$, and the free space is $A \cap [0,1]^2$, which can be empty even when $A$ is not. For a fixed $x_0$ the set of $y \in [0,1]$ with $\operatorname{elev}(x_0, y) \le \delta$ is a closed interval, possibly empty, computable in constant time for fixed $d$.

## Depends on

- [Fréchet distance of curves](frechet-distance-of-curves.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Lemma 33.2.1 (the sublevel set is an ellipse clipped to the unit square), Corollary 33.2.3 (the elevation function is convex) and Observation 33.2.4
