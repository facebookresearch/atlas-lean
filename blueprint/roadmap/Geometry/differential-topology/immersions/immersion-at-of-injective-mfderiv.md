# Injective differential gives an immersion

Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $n \ge 1$ be a smoothness degree (possibly $\infty$ or $\omega$), and let
$M$ and $N$ be $C^n$ manifolds without boundary over $\mathbb{K}$, modelled on
finite-dimensional normed $\mathbb{K}$-vector spaces. If a map $f \colon M \to N$ is $C^n$ at
every point of some neighbourhood of a point $x \in M$ and its differential $df_x$ at $x$ is
injective, then $f$ is a $C^n$ immersion at $x$.

Proof: Choose a complement to the differential's range, apply the inverse function theorem to
the resulting product map in extended charts, and use its local inverse as a target chart.

## Sources

- Mathlib `Mathlib/Geometry/Manifold/Immersion.lean` TODO (finite-dimensional injective-`mfderiv` criterion); J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.
