/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrinciple

/-!
# Tests for the maximum principle for compact self-adjoint operators

* The zero operator on `ℓ²(ℕ, ℝ)` has ordered eigenvalue sequence
  identically `0`.
* The orthogonal projection onto the span of the first basis vector of
  `ℓ²(ℕ, ℝ)` is compact and self-adjoint; its ordered eigenvalue sequence
  starts at `1`, is nonnegative, and decays below `1 / 2` eventually.
-/

open ContinuousLinearMap InnerProductSpace
open scoped lp
open MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrinciple

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrincipleTests

set_option linter.style.haveILetI false in
/-- `ℓ²(ℕ, ℝ)` is infinite-dimensional: its default Hilbert basis is an
infinite linearly independent family. -/
theorem not_finiteDimensional_lp_nat :
    ¬ FiniteDimensional ℝ ℓ²(ℕ, ℝ) := by
  intro h
  have hli := (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)).orthonormal.linearIndependent
  haveI := h
  exact (not_finite_iff_infinite.mpr inferInstance) (LinearIndependent.finite hli)

/-- For the zero operator on `ℓ²(ℕ, ℝ)`, every eigenvalue in the ordered
sequence is `0`. -/
example : ∃ (s : ℕ → ℝ) (u : ℕ → ℓ²(ℕ, ℝ)),
    (∀ n, (0 : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ)) (u n) =
      (s n : ℝ) • u n) ∧
    Orthonormal ℝ u ∧ (∀ n, |s (n + 1)| ≤ |s n|) ∧
    Filter.Tendsto (fun n => |s n|) Filter.atTop (nhds 0) ∧
    ∀ n, s n = 0 := by
  obtain ⟨s, u, heig, horth, hmono, htend, hvar⟩ :=
    exists_ordered_eigenvalue_sequence (T := (0 : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ)))
      (by simp [IsSelfAdjoint])
      (isCompactOperator_zero) not_finiteDimensional_lp_nat
  refine ⟨s, u, heig, horth, hmono, htend, ?_⟩
  intro n
  have hatt := (hvar n).2
  simp only [zero_apply, inner_zero_left, norm_zero] at hatt
  exact abs_eq_zero.mp hatt.symm

set_option linter.style.haveILetI false in
/-- The orthogonal projection onto the span of the first basis vector of
`ℓ²(ℕ, ℝ)` has first eigenvalue `1`, nonnegative eigenvalues, and the
eigenvalue moduli decay below `1 / 2`. -/
example : ∃ (s : ℕ → ℝ) (u : ℕ → ℓ²(ℕ, ℝ)),
    Orthonormal ℝ u ∧ s 0 = 1 ∧ (∀ n, 0 ≤ s n) ∧
    ∃ N, |s N| < 1 / 2 := by
  classical
  set e : ℓ²(ℕ, ℝ) := (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) 0 with he
  have he_norm : ‖e‖ = 1 := by
    rw [he]
    exact (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)).orthonormal.norm_eq_one 0
  set S : Submodule ℝ ℓ²(ℕ, ℝ) :=
    Submodule.span ℝ (({e} : Finset ℓ²(ℕ, ℝ)) : Set ℓ²(ℕ, ℝ))
    with hS
  have heS : e ∈ S := Submodule.subset_span (by simp)
  haveI : FiniteDimensional ℝ ↥S := by
    rw [hS]
    infer_instance
  have hTsa : IsSelfAdjoint S.starProjection := isSelfAdjoint_starProjection S
  have hTcomp : IsCompactOperator (S.starProjection : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
    -- `orthogonalProjectionOnto` lands in the finite-dimensional subspace
    -- `S`, which is locally compact, so it is a compact operator; composing
    -- with the inclusion `subtypeL` gives `starProjection`.
    have hco : IsCompactOperator (S.orthogonalProjectionOnto :
        ℓ²(ℕ, ℝ) → ↥S) := isCompactOperator_of_locallyCompactSpace_dom _
    have hcomp := hco.clm_comp S.subtypeL
    have heq : (⇑S.subtypeL) ∘ (⇑S.orthogonalProjectionOnto : ℓ²(ℕ, ℝ) → ↥S) =
        (⇑S.starProjection : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
      ext x
      rfl
    rw [heq] at hcomp
    exact hcomp
  obtain ⟨s, u, heig, horth, hmono, htend, hvar⟩ :=
    exists_ordered_eigenvalue_sequence
      (T := S.starProjection) hTsa hTcomp not_finiteDimensional_lp_nat
  have hPe : S.starProjection e = e := Submodule.starProjection_eq_self_iff.mpr heS
  have hRayleigh_pos : ∀ x : ℓ²(ℕ, ℝ), 0 ≤ ⟪S.starProjection x, x⟫_ℝ := by
    intro x
    have horth' : ⟪S.starProjection x, x - S.starProjection x⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem x)
        (Submodule.sub_starProjection_mem_orthogonal x)
    have hpos : 0 ≤ ⟪S.starProjection x, S.starProjection x⟫_ℝ := by
      rw [inner_self_eq_norm_sq_to_K]
      positivity
    have h1 : ⟪S.starProjection x, x⟫_ℝ =
        ⟪S.starProjection x, S.starProjection x⟫_ℝ :=
      sub_eq_zero.mp (by rw [← inner_sub_right]; exact horth')
    rw [h1]
    exact hpos
  have hs_nonneg : ∀ n, 0 ≤ s n := by
    intro n
    have hn1 : ‖u n‖ = 1 := horth.norm_eq_one n
    have h1 : ⟪S.starProjection (u n), u n⟫_ℝ = s n := by
      rw [heig n, inner_smul_left, RCLike.conj_ofReal,
        inner_self_eq_norm_sq_to_K, hn1]
      simp
    rw [← h1]
    exact hRayleigh_pos (u n)
  have hs0_abs : |s 0| = 1 := by
    apply le_antisymm
    · have hatt := (hvar 0).2
      have hu0 : ‖u 0‖ = 1 := horth.norm_eq_one 0
      have hPle : ‖S.starProjection (u 0)‖ ≤ ‖S.starProjection‖ := by
        have h1 := ContinuousLinearMap.le_opNorm S.starProjection (u 0)
        rw [hu0, mul_one] at h1
        exact h1
      calc |s 0| = ‖⟪S.starProjection (u 0), u 0⟫_ℝ‖ := hatt.symm
        _ ≤ ‖S.starProjection (u 0)‖ * ‖u 0‖ := norm_inner_le_norm _ _
        _ ≤ ‖S.starProjection‖ * ‖u 0‖ :=
            mul_le_mul_of_nonneg_right hPle (norm_nonneg _)
        _ = ‖S.starProjection‖ := by rw [hu0, mul_one]
        _ ≤ 1 := Submodule.starProjection_norm_le S
    · have hmax := (hvar 0).1 e he_norm (by intro j hj; exact absurd hj (Nat.not_lt_zero j))
      have h1 : ‖⟪S.starProjection e, e⟫_ℝ‖ = 1 := by
        rw [hPe, inner_self_eq_norm_sq_to_K, he_norm]
        simp
      rw [h1] at hmax
      exact hmax
  have hs0 : s 0 = 1 := by
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hs0_abs
    rcases hs0_abs with h | h
    · exact h
    · have h2 := hs_nonneg 0
      rw [h] at h2
      norm_num at h2
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend (1 / 2) (by norm_num)
  have hN' : |s N| < 1 / 2 := by
    have h2 := hN N (le_refl N)
    rw [dist_eq_norm, sub_zero] at h2
    simpa using h2
  exact ⟨s, u, horth, hs0, hs_nonneg, N, hN'⟩

end MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointMaximumPrincipleTests
