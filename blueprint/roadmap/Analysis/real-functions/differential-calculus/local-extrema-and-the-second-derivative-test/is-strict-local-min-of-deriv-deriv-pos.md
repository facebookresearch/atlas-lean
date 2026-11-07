# Strict second-derivative test, minimum version

Let $f : \mathbb{R} \to \mathbb{R}$ and
$x_0 \in \mathbb{R}$. If $f''(x_0) > 0$, $f'(x_0) = 0$, and $f$ is continuous at $x_0$, then $f$
has a strict local minimum at $x_0$.

## Sources

- `v1/Atlas/RealAnalysis/targets.yaml`, Theorem (Second Derivative Test), as strengthened in this file's header: the v1 `ContDiffAt ℝ 2` hypothesis is weakened to `ContinuousAt`, and `iteratedDeriv 2` is written in Mathlib's `deriv (deriv f)` form.
