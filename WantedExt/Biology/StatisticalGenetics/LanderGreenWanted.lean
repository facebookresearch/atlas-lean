/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lander–Green multipoint likelihood via the inheritance-vector hidden Markov chain

In a pedigree with `n` meioses, the inheritance vector at a locus records, for each meiosis,
whether the grandpaternal or grandmaternal allele was transmitted: a vector `v : Fin n → Bool`.
Lander and Green (1987, p. 2365) observe that with no interference the inheritance vectors at
ordered loci `M₁, …, Mₘ` form an inhomogeneous Markov chain: between `Mᵢ` and `Mᵢ₊₁` each
coordinate changes independently with probability `θᵢ` (the recombination fraction), so the
transition matrix `T(θᵢ)` is the Kronecker product of `n` copies of the `2 × 2` matrix
`[[1 - θ, θ], [θ, 1 - θ]]`, that is `T(θ)_{vw} = θᵈ (1 - θ)ⁿ⁻ᵈ` with `d` the Hamming distance
(the Hamming form is derived from the Kronecker form; recombination fractions lie in
`[0, 1/2]`). With a uniform law for `v₁` and marker
data conditionally independent given the inheritance vectors, with likelihood vectors `qᵢ`, the
pedigree likelihood is computed by the forward recursion of this hidden Markov chain
(pp. 2365–2366).

Recorded here: the Hamming/Kronecker form of the transition, its stochasticity, symmetry and
uniform stationarity. The inheritance vectors, the transition, the uniform prior, the path
weight, the path-sum likelihood, the forward recursion and the equality of the path-sum
likelihood with the forward recursion are proved in
`Domains.Biology.StatisticalGenetics.LanderGreenLikelihoodEqForward`.
The expectation-maximization search, complexity claims, the phenotype emission computation and
interference are not formalized.

Sources: E. S. Lander and P. Green, "Construction of multilocus genetic linkage maps in humans",
Proc. Natl. Acad. Sci. USA 84 (1987) 2363–2367, pp. 2365–2366.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.InformationTheory.Hamming
public import Domains.Biology.StatisticalGenetics.LanderGreenLikelihoodEqForward

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.LanderGreenWanted

open Finset

/-- **The Kronecker form and stochasticity of the transition** (Lander and Green 1987, p. 2365):
for a recombination fraction `θ` with `0 ≤ θ ≤ 1/2` and any number `n` of meioses, the
transition is the product over meioses of `1 - θ` (no change) or `θ` (change); its rows sum to
`1`; it is symmetric; and the uniform law is stationary.

Source: Lander and Green (1987), p. 2365. -/
public theorem_wanted transition_kronecker_stochastic (n : ℕ) (θ : ℝ) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1 / 2) :
    (∀ v w : InheritanceVector n,
        transition θ v w = ∏ i, if v i = w i then 1 - θ else θ) ∧
      (∀ v : InheritanceVector n, ∑ w, transition θ v w = 1) ∧
      (∀ v w : InheritanceVector n, transition θ v w = transition θ w v) ∧
      (∀ w : InheritanceVector n, ∑ v, uniformPrior n * transition θ v w = uniformPrior n)

end WantedExt.Biology.StatisticalGenetics.LanderGreenWanted
