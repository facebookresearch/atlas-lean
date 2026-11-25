# For nonnegative means, the Poisson weights sum to one over all states

Let `S` be a finite set and `c ∈ ℝ^S` with `c_s ≥ 0` for every `s`. Then the
[product-form Poisson weights](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)
`π_c(x) = ∏_s c_s^{x_s} e^{-c_s} / x_s!` (natural powers, with `0^0 = 1`) are summable over the
whole infinite state space `ℕ^S`, with

`∑_{x ∈ ℕ^S} π_c(x) = 1`.

As the weights are nonnegative, `π_c` is a probability mass function on `ℕ^S`: the joint law of
independent Poisson counts with means `c_s`, a species with `c_s = 0` having count `0` with
probability one. The sum runs over all of `ℕ^S`, not over a single stoichiometric compatibility
class, and no complex balance is involved.
