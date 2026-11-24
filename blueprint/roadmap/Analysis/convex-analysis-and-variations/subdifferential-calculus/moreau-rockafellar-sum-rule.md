# Moreau–Rockafellar sum rule

Let $X$ be a real normed space and $f, g : X \to (-\infty, \infty]$ convex functions. For every $x$ at which both are finite, $\partial f(x) + \partial g(x) \subseteq \partial (f + g)(x)$. If some point of $\operatorname{dom} f \cap \operatorname{dom} g$ is a point of continuity of $g$ (the Moreau–Rockafellar qualification condition), equality holds for every $x$. In $\mathbb R^n$ it suffices that the relative interiors of the domains meet.

Without a qualification condition the inclusion can be strict. In $\mathbb R^2$, let $f$ be the indicator function of the closed disk of radius $1$ centred at $(0, 1)$ and $g$ the indicator function of the half-plane $\{z_2 \le 0\}$. The two sets meet only at the origin, so $\partial(f + g)(0) = \mathbb R^2$, while $\partial f(0) + \partial g(0) = \{0\} \times (-\infty, 0] + \{0\} \times [0, \infty) = \{0\} \times \mathbb R$.

## Depends on

- [Subdifferential of a convex function](convex-subdifferential.md)

## Expansion

This page becomes ready once:

- the equality is proved from the [Hahn–Banach separation theorem](../../banach-spaces/duality-and-weak-topologies/hahn-banach-theorem/hahn-banach-separation.md), separating the epigraph of $f - x^*$ from the hypograph of $-g$, with the qualification condition ruling out a vertical separating hyperplane (proof obligation)

## Sources

- R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, Section 23 (subgradients) and Theorem 23.8 (sum rule)
- H. H. Bauschke and P. L. Combettes, *Convex Analysis and Monotone Operator Theory in Hilbert Spaces*, 2nd ed., Springer, 2017, Chapter 16
