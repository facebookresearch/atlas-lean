# Existence for the fixed-fixed problem under a continuous load

Let $L > 0$ and $k > 0$, and let $f \colon \mathbb{R} \to \mathbb{R}$ be continuous on $[0, L]$.
Then the [fixed-fixed problem](is-fixed-fixed-solution.md) $-k\, u'' = f$ on $[0, L]$,
$u(0) = u(L) = 0$, has a solution $u$.

Proof: by the [rescaling to the unit interval](is-fixed-fixed-solution-scale.md) it is the Dirichlet
problem $-v'' = g$ on $[0, 1]$ with $g(\xi) = \frac{L^2}{k} f(L \xi)$ continuous, which has a
solution by
[existence for the Sturm–Liouville Dirichlet problem](../../../Analysis/ordinary-differential-equations/sturm-liouville-dirichlet-problem/sturm-liouville-existence.md)
with zero potential.
