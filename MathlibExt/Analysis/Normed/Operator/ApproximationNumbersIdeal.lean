/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Normed.Operator.ApproximationNumbers
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Composition, scaling and addition of approximation numbers

For bounded operators between normed spaces over a nontrivially normed field, use `a_n(T)=inf
{‖T-R‖ : dim(range R)≤n}`. Composition satisfies `a_n(BTA)≤‖B‖ a_n(T) ‖A‖`, and scalar
multiplication gives `a_n(cT)=‖c‖a_n(T)`.

The rank allowances add under sums: `a_(n+m)(T+S)≤a_n(T)+a_m(S)`. These inequalities apply to
incomplete and infinite-dimensional spaces and do not assume a minimizing finite-rank
approximant.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {D : Type u} {E : Type v} {F : Type w} {G : Type z}
variable [NormedAddCommGroup D] [NormedAddCommGroup E]
variable [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [NormedSpace 𝕜 D] [NormedSpace 𝕜 E]
variable [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

private theorem rank_precomp_budget (R : E →L[𝕜] F) (A : D →L[𝕜] E)
    {n : ℕ} (hR : R.toLinearMap.rank ≤ (n : Cardinal)) :
    (R.comp A).toLinearMap.rank ≤ (n : Cardinal) := by
  exact (LinearMap.rank_comp_le_left A.toLinearMap R.toLinearMap).trans hR

private theorem rank_postcomp_budget (R : E →L[𝕜] F) (B : F →L[𝕜] G)
    {n : ℕ} (hR : R.toLinearMap.rank ≤ (n : Cardinal)) :
    (B.comp R).toLinearMap.rank ≤ (n : Cardinal) := by
  have h := (LinearMap.lift_rank_comp_le_right R.toLinearMap B.toLinearMap).trans
    (Cardinal.lift_le.mpr hR)
  have h' : Cardinal.lift.{w} ((B.comp R).toLinearMap.rank) ≤
      Cardinal.lift.{w} (n : Cardinal.{z}) := by
    simpa only [Cardinal.lift_natCast, toLinearMap_comp] using h
  exact Cardinal.lift_le.mp h'

private theorem le_mul_approximationNumber_of_le_errors (T : E →L[𝕜] F) (n : ℕ)
    (a c : ℝ) (hc : 0 ≤ c)
    (h : ∀ R : E →L[𝕜] F, R.toLinearMap.rank ≤ (n : Cardinal) → a ≤ c * ‖T - R‖) :
    a ≤ c * approximationNumber T n := by
  by_cases hzero : c = 0
  · subst c
    simpa using h 0 (by simp)
  · have hpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hzero)
    have hbound : a / c ≤ approximationNumber T n := by
      apply le_csInf (approximationErrorSet_nonempty T n)
      rintro r ⟨R, hR, rfl⟩
      exact (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using h R hR)
    simpa only [mul_comm] using (div_le_iff₀ hpos).mp hbound

/-- **Two-sided operator ideal inequality for approximation numbers.** Let `𝕜` be a
nontrivially normed field and `D,E,F,G` normed `𝕜`-spaces in independent universes. For
bounded `A : D → E`, `T : E → F`, `B : F → G` and `n : ℕ`, `a_n(B∘T∘A)≤‖B‖ a_n(T) ‖A‖`,
where `a_n` is the infimum of errors over approximants of cardinal range dimension at most
`n`. -/
theorem approximationNumber_comp_le (B : F →L[𝕜] G) (T : E →L[𝕜] F)
    (A : D →L[𝕜] E) (n : ℕ) :
    approximationNumber (B.comp (T.comp A)) n ≤ ‖B‖ * approximationNumber T n * ‖A‖ := by
  have hbound : approximationNumber (B.comp (T.comp A)) n ≤
      (‖B‖ * ‖A‖) * approximationNumber T n := by
    apply le_mul_approximationNumber_of_le_errors T n _ _
      (mul_nonneg (norm_nonneg B) (norm_nonneg A))
    intro R hR
    have hRank := rank_postcomp_budget (R.comp A) B (rank_precomp_budget R A hR)
    calc
      _ ≤ ‖B.comp (T.comp A) - B.comp (R.comp A)‖ :=
        approximationNumber_le_norm_sub _ n _ hRank
      _ = ‖B.comp ((T - R).comp A)‖ := by rw [sub_comp, comp_sub]
      _ ≤ ‖B‖ * ‖(T - R).comp A‖ := opNorm_comp_le _ _
      _ ≤ ‖B‖ * (‖T - R‖ * ‖A‖) :=
        mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg B)
      _ = (‖B‖ * ‖A‖) * ‖T - R‖ := by ac_rfl
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hbound

private theorem approximationNumber_smul_le (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber (c • T) n ≤ ‖c‖ * approximationNumber T n := by
  apply le_mul_approximationNumber_of_le_errors T n _ _ (norm_nonneg c)
  intro R hR
  have hRank : (c • R).toLinearMap.rank ≤ (n : Cardinal) := by
    simpa only [smul_comp, id_comp] using
      rank_postcomp_budget R (c • ContinuousLinearMap.id 𝕜 F) hR
  have h := approximationNumber_le_norm_sub (c • T) n (c • R) hRank
  simpa only [← smul_sub, norm_smul] using h

/-- **Scalar homogeneity of approximation numbers.** Let `𝕜` be a nontrivially normed field
and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set `a_n(T)=inf
{‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n : ℕ`. for
every `c : 𝕜`, `a_n(c • T)=‖c‖*a_n(T)`, including `c=0`. -/
@[simp] theorem approximationNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber (c • T) n = ‖c‖ * approximationNumber T n := by
  apply le_antisymm (approximationNumber_smul_le c T n)
  by_cases hc : c = 0
  · subst c
    simp
  · have h := approximationNumber_smul_le c⁻¹ (c • T) n
    have hcancel : c⁻¹ • (c • T) = T := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hcancel, norm_inv] at h
    have hnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have h' := mul_le_mul_of_nonneg_left h (norm_nonneg c)
    simpa only [← mul_assoc, mul_inv_cancel₀ hnorm, one_mul] using h'

private theorem rank_add_budget (R S : E →L[𝕜] F) {n m : ℕ}
    (hR : R.toLinearMap.rank ≤ (n : Cardinal))
    (hS : S.toLinearMap.rank ≤ (m : Cardinal)) :
    (R + S).toLinearMap.rank ≤ ((n + m : ℕ) : Cardinal) := by
  calc
    _ ≤ R.toLinearMap.rank + S.toLinearMap.rank := LinearMap.rank_add_le _ _
    _ ≤ (n : Cardinal) + (m : Cardinal) := add_le_add hR hS
    _ = ((n + m : ℕ) : Cardinal) := (Nat.cast_add n m).symm

/-- **Additive rank allowance for approximation numbers.** Let `𝕜` be a nontrivially normed
field and `E,F` normed `𝕜`-spaces, possibly incomplete. For `T : E →L[𝕜] F`, set
`a_n(T)=inf {‖T-R‖ : R : E →L[𝕜] F, dim_𝕜(range R)≤n}`, using cardinal dimension and `n :
ℕ`. for bounded `S : E → F` and `n,m : ℕ`, `a_(n+m)(T+S)≤a_n(T)+a_m(S)`. -/
theorem approximationNumber_add_le (T S : E →L[𝕜] F) (n m : ℕ) :
    approximationNumber (T + S) (n + m) ≤ approximationNumber T n + approximationNumber S m := by
  have hbound : approximationNumber (T + S) (n + m) - approximationNumber T n ≤
      approximationNumber S m := by
    apply le_csInf (approximationErrorSet_nonempty S m)
    rintro r ⟨R₂, hR₂, rfl⟩
    have hinner : approximationNumber (T + S) (n + m) - ‖S - R₂‖ ≤
        approximationNumber T n := by
      apply le_csInf (approximationErrorSet_nonempty T n)
      rintro r ⟨R₁, hR₁, rfl⟩
      have ha := approximationNumber_le_norm_sub (T + S) (n + m) (R₁ + R₂)
        (rank_add_budget R₁ R₂ hR₁ hR₂)
      have hn : ‖T + S - (R₁ + R₂)‖ ≤ ‖T - R₁‖ + ‖S - R₂‖ := by
        rw [add_sub_add_comm]
        exact norm_add_le _ _
      linarith
    linarith
  linarith

end ContinuousLinearMap
