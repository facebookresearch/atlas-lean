# Hausdorff dimension function

A Hausdorff dimension function, or gauge, is a continuous non-decreasing function
$\psi : [0,\infty) \to [0,\infty)$ with $\psi(0) = 0$ and $\psi(r) > 0$ for every $r > 0$.

## Idea

The $s$-dimensional Hausdorff measure gives a small set of diameter $r$ the weight $r^s$.
Replacing $r^s$ by a general gauge $\psi(r)$ gives the generalised Hausdorff measure
$\mathcal{H}^\psi$, which can tell apart sets of the same Hausdorff dimension: a gauge with
$\psi(r)/r^s \to \infty$ as $r \to 0$, such as $r^s \log(1/r)$ for small $r$ and $s > 0$, can give positive
measure to a set whose $s$-dimensional Hausdorff measure is $0$. The
defining conditions say that sets of positive diameter get positive weight and that the weight
tends to $0$ with the diameter. The other statements of this card are these basic facts, read off
the definition.

## Statements

- [Hausdorff dimension function](hausdorff-dimension-function.md)
- [Continuity of a Hausdorff dimension function](continuous.md): a defining property, restated.
- [Monotonicity of a Hausdorff dimension function](monotone.md): a defining property, restated.
- [A Hausdorff dimension function vanishes at zero](map-zero.md): a defining property, restated.
- [A Hausdorff dimension function is positive at positive radii](map-pos.md): a defining property, restated.
- [A Hausdorff dimension function vanishes only at zero](map-eq-zero-iff.md): a basic fact: $\psi$ vanishes exactly at $0$.
- [A Hausdorff dimension function tends to zero at zero](tendsto-zero.md): a basic fact, from continuity at $0$.
