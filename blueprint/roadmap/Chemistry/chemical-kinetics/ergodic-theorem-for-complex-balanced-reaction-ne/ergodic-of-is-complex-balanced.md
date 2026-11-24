# Ergodic theorem for complex-balanced stochastic reaction networks

Let the concentrations `c > 0` be complex balanced for the nonnegative rate constants `κ`
(`_hκ`, so that the propensities `propensity N κ r x` are nonnegative jump rates), and let `X`
be the stochastic mass-action chain of the network on `ℕ^S`, started from the product-form
Poisson law `π_c` (`hinit`). Assume

* `hnonexp`: the chain does not explode (`NoExplosion`);
* `htransfer`: for this chain, non-explosion makes every probability solution of the
  stationary master equation, used as the initial law, a stationary law of the chain (the
  forward-equation step `π Q = 0 ⇒ π P(t) = π` of Norris 1997, Theorem 3.5.5, which fails for
  explosive chains);
* `hreg`: the chain regenerates at a state `x₀` (the strong Markov property at the
  successive entrance times `R k` into `x₀`).

Then the chain is positive recurrent (finite mean return time to `x₀`), and for every bounded
observable `f` the time averages `t⁻¹ ∫₀ᵗ f (X s) ds` converge almost surely to the
product-form mean `∑ₓ π_c(x) f(x)`. The proof does not use `_hκ`; it restricts the statement to
stochastic reaction networks, whose rate constants are nonnegative.

The product-form law enters through `isStationaryMasterSolution_poissonWeight` (Anderson,
Craciun & Kurtz 2010, Theorem 4.1); positive recurrence and the limit come from
`IsRegenerative.ergodic` (renewal–reward and the strong law of large numbers).
