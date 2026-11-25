# For κ > 0, all positive complex-balanced c give the same class law

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finite reaction set `ρ`, and let `κ_r > 0` be rate constants. If
`c, d ∈ ℝ^S` are positive (`c_s > 0` and `d_s > 0` for every `s`) and both
[complex balanced](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
for `κ`, then for every state `x₀ ∈ ℕ^S` they give the same [conditioned law](conditioned-law.md) on
the [compatibility class](compat-class.md) `Γ` of `x₀`: `π_d(· | Γ) = π_c(· | Γ)`. So on each class
the law does not depend on which positive complex-balanced equilibrium is used. By
[Horn and Jackson](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/positive-equilibria-eq.md),
`log d - log c` is orthogonal to the
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md), and the
[orthogonal case](conditioned-law-compat-class-eq-of-ortho.md) applies.

Positive rate constants are needed. For the single reaction `A → B` with rate constant `0`, every
`c` is complex balanced, and on the class `{(1, 0), (0, 1)}` the means `c = (1, 1)` and `d = (1, 2)`
give the laws `(1/2, 1/2)` and `(1/3, 2/3)`.
