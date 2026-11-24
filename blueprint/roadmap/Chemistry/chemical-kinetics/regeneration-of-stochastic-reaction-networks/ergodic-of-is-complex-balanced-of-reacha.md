# Ergodic theorem for complex-balanced stochastic reaction networks, with the forward equation and the regeneration proved

**Ergodic theorem for complex-balanced stochastic reaction networks, with the forward
equation and the regeneration proved.** Let `c > 0` be complex balanced for the rate constants
`κ ≥ 0`, let the stochastic mass-action chain satisfy a Foster–Lyapunov drift bound
`L V ≤ a V + b` with `∑_s x_s ≤ V(x)` (non-explosion, `StochasticCRNNonExplosion`), and let every
state be reachable from `x₀` along reactions with positive propensity. Then for the chain built
by the jump–hold construction:

* it returns to `x₀` almost surely, and the mean return time to `x₀` is finite (positive
  recurrence);
* from every initial state `x`, the time averages `t⁻¹ ∫₀ᵗ f (X s) ds` of every bounded
  observable converge almost surely to the product-form mean `∑_y π_c(y) f(y)`.

Compared with `StochasticCRNErgodicity.ergodic_of_isComplexBalanced`, the transfer of the
stationary master equation to the chain (in Laplace form, `tsum_mul_lintegral_abelSum`) and the
regeneration at `x₀` (recurrence `measure_return_eq_one`, i.i.d. cycles
`identDistrib_cycleSum`, `indepFun_cycleSum_of_lt`) are proved, not assumed.
