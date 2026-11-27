# On a finite set, the conditioned law is the normalized Poisson law

Let `S` be a finite set, `c ∈ ℝ^S` and `Ω ⊆ ℕ^S` a finite set of states. At every `x ∈ Ω` the
[conditioned law](conditioned-law.md) equals the
[normalized Poisson weight](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/class-stationary-law.md)
on `Ω`: `π_c(x | Ω) = π_c(x) / ∑_{y ∈ Ω} π_c(y)`. This holds for every real `c`; when the finite sum
is `0` both sides are `0`, by the convention `y / 0 = 0`. For nonnegative rate constants, a positive
complex-balanced `c` and a nonempty reaction-closed `Ω`, this is the law that the
[finite-class theorem](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/class-stationary-law-spec.md)
shows to be invariant under the transition semigroup of the chain on `Ω`.
