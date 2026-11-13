# Asymptotic normality from a linearization

**Asymptotic normality from a linearization** of the cluster estimating equation.

Let `A` be invertible (the sensitivity matrix), let `βhat n` solve `∑_{i<n} U i (βhat n) = 0`
with probability tending to one, and suppose the averaged estimating function is
differentiable at `β₀` along the estimator in probability, with derivative `A`:
for every `ε > 0`, with probability tending to one,
`‖n⁻¹ • (∑ U i (βhat n) - ∑ U i β₀) - A (βhat n - β₀)‖ ≤ ε ‖βhat n - β₀‖`.
If the cluster sums `-A⁻¹ ((√n)⁻¹ • ∑_{i<n} U i β₀)` converge in distribution to `W`, then so
does `√n • (βhat n - β₀)`.

The limit is fed through the cluster sums themselves: this theorem only transfers the cluster
CLT for `U i β₀` to the estimator.
