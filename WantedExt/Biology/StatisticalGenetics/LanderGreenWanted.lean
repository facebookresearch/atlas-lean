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
(the Hamming form is derived from the Kronecker form). With a uniform law for `v₁` and marker
data conditionally independent given the inheritance vectors, with likelihood vectors `qᵢ`, the
pedigree likelihood is computed by the forward recursion of this hidden Markov chain
(pp. 2365–2366).

Recorded here: the Hamming/Kronecker form of the transition, its stochasticity, symmetry and
uniform stationarity, and the equality of the path-sum likelihood with the forward recursion.
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

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.LanderGreenWanted

open Finset

/-- An inheritance vector for `n` meioses. -/
abbrev InheritanceVector (n : ℕ) := Fin n → Bool

/-- Hamming distance between two inheritance vectors: the number of meioses whose transmitted
grandparental origin differs. -/
def hamming {n : ℕ} (v w : InheritanceVector n) : ℕ := #{i | v i ≠ w i}

/-- The Lander–Green transition probability between inheritance vectors at adjacent loci with
recombination fraction `θ` and no interference: `θᵈ (1 - θ)ⁿ⁻ᵈ`, `d` the Hamming distance. -/
noncomputable def transition {n : ℕ} (θ : ℝ) (v w : InheritanceVector n) : ℝ :=
  θ ^ hamming v w * (1 - θ) ^ (n - hamming v w)

/-- The uniform law of the inheritance vector at the first locus. -/
noncomputable def uniformPrior (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

/-- The joint weight of a path `v₀, …, vₘ` of inheritance vectors at `m + 1` ordered loci and of
the marker data: the uniform prior of `v₀`, the transitions with recombination fractions `θ i`
between loci `i` and `i + 1`, and the likelihoods `q i (v i)` of the data at each locus. -/
noncomputable def pathWeight {n m : ℕ} (θ : ℕ → ℝ) (q : ℕ → InheritanceVector n → ℝ)
    (v : Fin (m + 1) → InheritanceVector n) : ℝ :=
  uniformPrior n * (∏ i : Fin (m + 1), q i (v i)) *
    ∏ i : Fin m, transition (θ i) (v i.castSucc) (v i.succ)

/-- The pedigree likelihood of the marker data at `m + 1` loci: the sum of `pathWeight` over all
paths of inheritance vectors. -/
noncomputable def likelihood {n : ℕ} (m : ℕ) (θ : ℕ → ℝ) (q : ℕ → InheritanceVector n → ℝ) :
    ℝ :=
  ∑ v : Fin (m + 1) → InheritanceVector n, pathWeight θ q v

/-- The forward vectors of the hidden Markov chain: `α₀(w) = 2⁻ⁿ q₀(w)` and
`αᵢ₊₁(w) = qᵢ₊₁(w) ∑ᵥ αᵢ(v) T(θᵢ)_{vw}`. -/
noncomputable def forward {n : ℕ} (θ : ℕ → ℝ) (q : ℕ → InheritanceVector n → ℝ) :
    ℕ → InheritanceVector n → ℝ
  | 0, w => uniformPrior n * q 0 w
  | i + 1, w => q (i + 1) w * ∑ v, forward θ q i v * transition (θ i) v w

/-- **The Kronecker form and stochasticity of the transition** (Lander and Green 1987, p. 2365):
for `0 ≤ θ ≤ 1`, the transition is the product over meioses of `1 - θ` (no change) or `θ`
(change); its rows sum to `1`; it is symmetric; and the uniform law is stationary.

Source: Lander and Green (1987), p. 2365. -/
public theorem_wanted transition_kronecker_stochastic (n : ℕ) (θ : ℝ) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) :
    (∀ v w : InheritanceVector n,
        transition θ v w = ∏ i, if v i = w i then 1 - θ else θ) ∧
      (∀ v : InheritanceVector n, ∑ w, transition θ v w = 1) ∧
      (∀ v w : InheritanceVector n, transition θ v w = transition θ w v) ∧
      (∀ w : InheritanceVector n, ∑ v, uniformPrior n * transition θ v w = uniformPrior n)

/-- **The Lander–Green forward recursion** (Lander and Green 1987, pp. 2365–2366): for any
recombination fractions `θ i` and data likelihood vectors `q i`, the pedigree likelihood of the
data at `m + 1` loci, a sum over all `2^(n(m + 1))` paths of inheritance vectors, equals the sum
of the last forward vector, which the recursion computes one locus at a time.

Source: Lander and Green (1987), pp. 2365–2366. -/
public theorem_wanted likelihood_eq_forward (n m : ℕ) (θ : ℕ → ℝ)
    (q : ℕ → InheritanceVector n → ℝ) :
    likelihood m θ q = ∑ w, forward θ q m w

end WantedExt.Biology.StatisticalGenetics.LanderGreenWanted
