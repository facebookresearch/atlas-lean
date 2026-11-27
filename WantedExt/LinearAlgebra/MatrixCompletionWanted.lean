/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.LinearAlgebra.Matrix.LowRankRecovery
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Powerset

/-!
# Exact matrix completion by nuclear norm minimization

E. J. Candès and B. Recht (*Exact matrix completion via convex optimization*, Found. Comput.
Math. 9 (2009) 717-772, arXiv:0805.4471) show that a rank-`r` matrix `M` whose row and column
spaces are incoherent with the standard basis is, with high probability, the unique minimizer of
the nuclear norm among all matrices that agree with it on `m` entries sampled uniformly at random,
as soon as `m ≳ n^{6/5} r log n` (and `m ≳ n r log n` up to coherence factors when the incoherence
parameters are small). Their Theorem 1.3 is recorded here; its proof (a dual certificate built
with a noncommutative Khintchine / Rudelson-type concentration bound) is deferred.

The matrix `M` is given by a compact singular value decomposition `M = U diag(σ) Vᵀ` with
orthonormal columns and positive singular values, so that its column and row spaces are those of
`U` and `V`, `‖P_U eᵢ‖² = ∑ₖ U_{ik}²`, and `∑ₖ uₖ vₖ* = U Vᵀ`. The uniformly random set of
observed locations is represented by counting: the probability of an event is the number of
`m`-element sets of locations where it holds, divided by `C(n₁ n₂, m)`.
-/

@[expose] public section

open Matrix Finset MathlibExt.LinearAlgebra.Matrix.LowRankRecovery

namespace MathlibExt.LinearAlgebra.MatrixCompletionWanted

open Classical in
/-- **Exact matrix completion (Candès–Recht).** There are numerical constants `C, c > 0` such that
the following holds. Let `M = U diag(σ) Vᵀ` be an `n₁ × n₂` matrix of rank `r ≥ 1`, with `U`, `V`
having orthonormal columns and `σ > 0`, and put `n = max n₁ n₂`. Assume

* **A0**: the coherences of the column and row spaces obey `max (μ(U), μ(V)) ≤ μ₀`, where
  `μ(U) = (n₁ / r) maxᵢ ‖P_U eᵢ‖²` (Definition 1.2);
* **A1**: every entry of `U Vᵀ = ∑ₖ uₖ vₖ*` is at most `μ₁ √(r / (n₁ n₂))` in absolute value,
  with `μ₁ ≥ 1`.

If `m ≥ C max(μ₁², μ₀^{1/2} μ₁, μ₀ n^{1/4}) n r (β log n)` for some `β > 2`, then, for a set `Ω`
of `m` locations drawn uniformly at random, `M` is the unique minimizer of the nuclear norm over
`{X : X_{ij} = M_{ij} for (i, j) ∈ Ω}` with probability at least `1 - c n^{-β}`.

Source: E. J. Candès and B. Recht, *Exact matrix completion via convex optimization*,
Found. Comput. Math. 9 (2009) 717-772, arXiv:0805.4471, Theorem 1.3 (first part), with
Definition 1.2 and assumptions A0, A1 of Section 1.2; the standing assumption `μ₁ ≥ 1` is stated
there just before the theorem. The improvement `m ≥ C μ₀ n^{6/5} r (β log n)` for
`r ≤ μ₀⁻¹ n^{1/5}` (second part) is not recorded. -/
theorem_wanted exists_card_filter_unique_nuclearNorm_min :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (n₁ n₂ r : ℕ) (U : Matrix (Fin n₁) (Fin r) ℝ) (V : Matrix (Fin n₂) (Fin r) ℝ)
        (σ : Fin r → ℝ) (μ₀ μ₁ β : ℝ) (m : ℕ),
        1 ≤ r → Uᵀ * U = 1 → Vᵀ * V = 1 → (∀ k, 0 < σ k) →
        (∀ i, (n₁ : ℝ) / r * ∑ k, U i k ^ 2 ≤ μ₀) →
        (∀ j, (n₂ : ℝ) / r * ∑ k, V j k ^ 2 ≤ μ₀) →
        1 ≤ μ₁ → (∀ i j, |(U * Vᵀ) i j| ≤ μ₁ * √((r : ℝ) / (n₁ * n₂))) →
        2 < β →
        C * max (max (μ₁ ^ 2) (√μ₀ * μ₁)) (μ₀ * ((max n₁ n₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 4)) *
            ((max n₁ n₂ : ℕ) : ℝ) * r * (β * Real.log (max n₁ n₂ : ℕ)) ≤ m →
        (1 - c * ((max n₁ n₂ : ℕ) : ℝ) ^ (-β)) * ((n₁ * n₂).choose m : ℝ) ≤
          ((univ.filter fun Ω : Finset (Fin n₁ × Fin n₂) => Ω.card = m ∧
            ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
              (∀ p ∈ Ω, X p.1 p.2 = (U * diagonal σ * Vᵀ) p.1 p.2) →
              X ≠ U * diagonal σ * Vᵀ → nuclearNorm (U * diagonal σ * Vᵀ) < nuclearNorm X).card :
            ℝ)

end MathlibExt.LinearAlgebra.MatrixCompletionWanted
