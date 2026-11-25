# The proximal map of a lower semicontinuous convex function

Let $H$ be a real Hilbert space, $f : H \to (-\infty, \infty]$ convex, lower semicontinuous and not identically $+\infty$, and $\lambda > 0$. For every $v \in H$ the function $x \mapsto f(x) + \|x - v\|^2/(2\lambda)$ has a unique minimizer, written $\operatorname{prox}_{\lambda f}(v)$, and $x = \operatorname{prox}_{\lambda f}(v)$ exactly when $(v - x)/\lambda \in \partial f(x)$. For the indicator function of a nonempty closed convex set $C \subseteq H$, $\operatorname{prox}_{\lambda f}$ is the nearest-point projection onto $C$; for a constant $f$ it is the identity. On $H = \mathbb{R}^n$ these are the proximal maps of proximal algorithms.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Subdifferential of a convex function on a real Hilbert space, and the equality case $f(x) + f^*(y) = \langle x, y\rangle \iff y \in \partial f(x)$ of the Fenchel–Young inequality.

## Background

- [Variational inequality for the convex projection](../../hilbert-spaces/hilbert-projection-theorem/convex-projection-variational.md): the indicator case: variational inequality for the projection onto a closed convex set.
- [Nearest points coincide with the convex projection](../../hilbert-spaces/hilbert-projection-theorem/convex-projection-eq-of-is-nearest-point.md): the indicator case: nearest points coincide with the projection.

## Sources

- J.-J. Moreau, "Proximité et dualité dans un espace hilbertien", *Bulletin de la Société Mathématique de France* 93:273–299, 1965, <http://www.numdam.org/item/BSMF_1965__93__273_0/>, §3.a (Proposition: strict minimum), §3.b (notation $\operatorname{prox}_f$), §3.d (projection example) and §4.a (Proposition: $z = x + y$ with $f(x) + f^*(y) = \langle x, y\rangle$ iff $x = \operatorname{prox}_f z$)
- N. Parikh and S. Boyd, "Proximal algorithms", *Foundations and Trends in Optimization* 1(3), 2014, author version <https://web.stanford.edu/~boyd/papers/prox_algs.html>, §1.1, formulas (1.1)–(1.2), and §3.2 (finite-dimensional case)
