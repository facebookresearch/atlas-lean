# Complex balance at c > 0: a stationary law on each compatibility class

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finite reaction set `ρ`, let `κ ∈ ℝ^ρ` be rate constants of any sign, and
let `c ∈ ℝ^S`, with `c_s > 0` for every `s`, be
[complex balanced](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
for `κ`. For a state `x₀ ∈ ℕ^S`, let `Γ = {x ∈ ℕ^S : x - x₀ ∈ 𝒮}`, where `𝒮` is the
[stoichiometric subspace](../../../Dynamics/smooth-dynamics/stoichiometric-subspace.md), be its
[stoichiometric compatibility class](compat-class.md), which contains `x₀`. Then the
[conditioned law](conditioned-law.md) `π_c(· | Γ)`, equal to `π_c(x) / π_c(Γ)` on `Γ` and to `0` off
`Γ`, is positive at every state of `Γ`, sums to `1` over `ℕ^S`, and solves the
[stationary master equation](../ergodic-theorem-for-complex-balanced-reaction-ne/is-stationary-master-solution.md)
for `κ` at every state of `ℕ^S` (Anderson, Craciun & Kurtz 2010, Theorems 4.1–4.2). In the
stochastic model `κ ≥ 0`, which makes the equation the master equation of the chain; the statement
allows any real `κ`.

Stationary means here a solution of the stationary master equation; the statement says nothing about
the transition probabilities of the chain. It does not say that this law is the only one: a
compatibility class can contain smaller reaction-closed sets, and the law conditioned on each of
them is a [solution as well](is-stationary-master-solution-conditione.md). For `2A ⇌ 0` the class of
every state is all of `ℕ`, while the even counts and the odd counts form two reaction-closed sets.
