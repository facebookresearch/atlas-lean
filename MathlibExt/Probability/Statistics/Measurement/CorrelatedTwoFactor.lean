/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.FactorAnalysis
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Identification of a correlated two-factor model -/

@[expose] public section

open Matrix

namespace MathlibExt.Probability.Statistics.Measurement

/-- Covariance of a confirmatory model with two variance-one factors of correlation `ρ`.
Indicators `0`, `1`, and `2` load only on the first factor; indicators `3` and `4` load only
on the second. The vector `l` gives these five loadings and `ψ` gives the five error variances.
The formula is algebraic; the correlation range is `|ρ| ≤ 1` and valid variances are nonnegative. -/
def correlatedTwoFactorCov (l ψ : Fin 5 → ℝ) (ρ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  factorModelCov (Matrix.of fun (i : Fin 5) (j : Fin 2) =>
    if j = (if i.val < 3 then 0 else 1) then l i else 0) !![1, ρ; ρ, 1] (diagonal ψ)

private theorem cov_entry (l ψ : Fin 5 → ℝ) (ρ : ℝ) (i j : Fin 5) :
    correlatedTwoFactorCov l ψ ρ i j =
      l i * l j * (if (i.val < 3 ↔ j.val < 3) then 1 else ρ) + (if i = j then ψ i else 0) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [correlatedTwoFactorCov, factorModelCov, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply] <;> ring

private def firstBlock : Fin 3 → Fin 5 := Fin.castLE (by decide)

private theorem cov_firstBlock (l ψ : Fin 5 → ℝ) (ρ : ℝ) :
    (correlatedTwoFactorCov l ψ ρ).submatrix firstBlock firstBlock =
      oneFactorCovariance (l ∘ firstBlock) (ψ ∘ firstBlock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cov_entry, firstBlock, oneFactorCovariance, Matrix.vecMulVec_apply,
      Matrix.diagonal_apply]

private theorem recover_three (l ψ : Fin 5 → ℝ) (ρ : ℝ) (h₀ : l 0 ≠ 0)
    (h₁ : l 1 ≠ 0) (h₂ : l 2 ≠ 0) :
    let C := correlatedTwoFactorCov l ψ ρ
    l 0 ^ 2 = C 0 1 * C 0 2 / C 1 2 ∧ l 1 ^ 2 = C 1 0 * C 1 2 / C 0 2 ∧
      l 2 ^ 2 = C 2 0 * C 2 1 / C 0 1 := by
  intro C
  have h := cov_firstBlock l ψ ρ
  have sq (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hj : l (firstBlock j) ≠ 0) (hk : l (firstBlock k) ≠ 0) :=
    sq_loading_of_oneFactorCovariance (l ∘ firstBlock) (ψ ∘ firstBlock) i j k hij hik hjk hj hk
  rw [← h] at sq
  have hb₀ : firstBlock 0 = 0 := rfl
  have hb₁ : firstBlock 1 = 1 := rfl
  have hb₂ : firstBlock 2 = 2 := rfl
  dsimp only [C]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pow_two, Function.comp_apply, Matrix.submatrix_apply, hb₀, hb₁, hb₂] using
      sq 0 1 2 (by decide) (by decide) (by decide) h₁ h₂
  · simpa only [pow_two, Function.comp_apply, Matrix.submatrix_apply, hb₀, hb₁, hb₂] using
      sq 1 0 2 (by decide) (by decide) (by decide) h₀ h₂
  · simpa only [pow_two, Function.comp_apply, Matrix.submatrix_apply, hb₀, hb₁, hb₂] using
      sq 2 0 1 (by decide) (by decide) (by decide) h₀ h₁

private theorem same_first_three {l ψ l' ψ' : Fin 5 → ℝ} {ρ ρ' : ℝ} (h₀ : 0 < l 0)
    (h₁ : l 1 ≠ 0) (h₂ : l 2 ≠ 0) (h₀' : 0 < l' 0)
    (hC : correlatedTwoFactorCov l' ψ' ρ' = correlatedTwoFactorCov l ψ ρ) :
    l' 0 = l 0 ∧ l' 1 = l 1 ∧ l' 2 = l 2 := by
  have hs := congrArg (fun C : Matrix (Fin 5) (Fin 5) ℝ => C.submatrix firstBlock firstBlock) hC
  rw [cov_firstBlock, cov_firstBlock] at hs
  have h := (eq_of_oneFactorCovariance_eq_of_pos (l ∘ firstBlock) (ψ ∘ firstBlock)
    (l' ∘ firstBlock) (ψ' ∘ firstBlock) 0 1 2 (by decide) (by decide) (by decide)
    h₁ h₂ h₀ h₀' hs).1
  exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩

private theorem recover_last (l ψ : Fin 5 → ℝ) (ρ : ℝ) (h₀ : l 0 ≠ 0) (hρ : ρ ≠ 0) :
    let C := correlatedTwoFactorCov l ψ ρ
    l 3 = C 0 3 / (l 0 * ρ) ∧ l 4 = C 0 4 / (l 0 * ρ) := by
  intro C
  dsimp only [C]
  constructor <;> rw [cov_entry] <;> norm_num <;> rw [eq_div_iff (mul_ne_zero h₀ hρ)] <;> ring

private theorem recover_corr_sq (l ψ : Fin 5 → ℝ) (ρ : ℝ) (h₀ : l 0 ≠ 0)
    (h₃ : l 3 ≠ 0) (h₄ : l 4 ≠ 0) :
    let C := correlatedTwoFactorCov l ψ ρ
    ρ ^ 2 = C 0 3 * C 0 4 / (l 0 ^ 2 * C 3 4) := by
  intro C
  dsimp only [C]
  simp only [cov_entry]
  norm_num
  rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ h₀) (mul_ne_zero h₃ h₄))]
  ring

private theorem rescale_cov (l ψ : Fin 5 → ℝ) (ρ t : ℝ) (h₄ : l 4 = 0) (ht : t ≠ 0) :
    correlatedTwoFactorCov (Function.update l 3 (t * l 3))
      (Function.update ψ 3 (ψ 3 + (1 - t ^ 2) * l 3 ^ 2)) (ρ / t) =
        correlatedTwoFactorCov l ψ ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cov_entry, h₄] <;> field_simp [ht]
  ring

/-- **Identification of a correlated two-factor model.** The first three nonzero loadings
are determined by the first covariance block once the first loading is positive. With known
nonzero correlation, the two remaining loadings are recovered from the cross-block entries,
even when one is zero. With unknown nonzero correlation and both second-factor loadings
nonzero, the two cross-block covariances `C 0 3` and `C 0 4` together with the within-factor
covariance `C 3 4` recover the squared correlation. Fixing the sign of the fourth loading
then determines the remaining parameters. If the fifth loading is zero and
the fourth is nonzero, rescaling by `t` with `|ρ| < t ≤ 1` preserves the covariance and keeps
the new correlation and error variances admissible. Taking `t < 1` changes the fourth loading.
See Kenny, *Identification: Overview*, Condition B2a, for the role of correlated factors. -/
theorem correlated_two_factor_identification (l ψ : Fin 5 → ℝ) (ρ : ℝ)
    (h₀ : 0 < l 0) (h₁ : l 1 ≠ 0) (h₂ : l 2 ≠ 0) :
    let C := correlatedTwoFactorCov l ψ ρ
    (l 0 ^ 2 = C 0 1 * C 0 2 / C 1 2 ∧ l 1 ^ 2 = C 1 0 * C 1 2 / C 0 2 ∧
      l 2 ^ 2 = C 2 0 * C 2 1 / C 0 1) ∧
    (∀ i, ψ i = C i i - l i ^ 2) ∧
    (ρ ≠ 0 → l 3 = C 0 3 / (l 0 * ρ) ∧ l 4 = C 0 4 / (l 0 * ρ)) ∧
    (l 3 ≠ 0 → l 4 ≠ 0 → ρ ^ 2 = C 0 3 * C 0 4 / (l 0 ^ 2 * C 3 4)) ∧
    (∀ (l' ψ' : Fin 5 → ℝ) (ρ' : ℝ), 0 < l' 0 → correlatedTwoFactorCov l' ψ' ρ' = C →
      (l' 0 = l 0 ∧ l' 1 = l 1 ∧ l' 2 = l 2) ∧
      (ρ ≠ 0 → ρ' = ρ → l' = l ∧ ψ' = ψ) ∧
      (ρ ≠ 0 → l 3 ≠ 0 → l 4 ≠ 0 → 0 < l 3 * l' 3 → ρ' = ρ ∧ l' = l ∧ ψ' = ψ)) ∧
    (l 4 = 0 → l 3 ≠ 0 → (∀ i, 0 ≤ ψ i) → ∀ t : ℝ, |ρ| < t → t ≤ 1 →
      let l' := Function.update l 3 (t * l 3)
      let ψ' := Function.update ψ 3 (ψ 3 + (1 - t ^ 2) * l 3 ^ 2)
      correlatedTwoFactorCov l' ψ' (ρ / t) = C ∧ |ρ / t| < 1 ∧
        (∀ i, 0 ≤ ψ' i) ∧ (t < 1 → l' ≠ l)) := by
  intro C
  have h₀ne := ne_of_gt h₀
  have hdiag (l ψ : Fin 5 → ℝ) (ρ : ℝ) (i : Fin 5) :
      ψ i = correlatedTwoFactorCov l ψ ρ i i - l i ^ 2 := by
    simp [cov_entry, pow_two]
  refine ⟨recover_three l ψ ρ h₀ne h₁ h₂, hdiag l ψ ρ, recover_last l ψ ρ h₀ne,
    recover_corr_sq l ψ ρ h₀ne, ?_, ?_⟩
  · intro l' ψ' ρ' h₀' hC
    obtain ⟨h₀eq, h₁eq, h₂eq⟩ := same_first_three h₀ h₁ h₂ h₀' hC
    have known (hρ : ρ ≠ 0) (hρeq : ρ' = ρ) : l' = l ∧ ψ' = ψ := by
      obtain ⟨hA, hB⟩ := recover_last l' ψ' ρ' (ne_of_gt h₀') (hρeq ▸ hρ)
      rw [hC, h₀eq, hρeq] at hA hB
      obtain ⟨ha, hb⟩ := recover_last l ψ ρ h₀ne hρ
      have hL : l' = l := by
        funext i
        fin_cases i
        · exact h₀eq
        · exact h₁eq
        · exact h₂eq
        · exact hA.trans ha.symm
        · exact hB.trans hb.symm
      refine ⟨hL, funext fun i => ?_⟩
      rw [hdiag l' ψ' ρ' i, hdiag l ψ ρ i, hC, hL]
    refine ⟨⟨h₀eq, h₁eq, h₂eq⟩, known, ?_⟩
    intro hρ h₃ h₄ hsign
    have cross (i : Fin 5) (hi : 3 ≤ i.val) : l' i * ρ' = l i * ρ := by
      have h := congrFun (congrFun hC 0) i
      change correlatedTwoFactorCov l' ψ' ρ' 0 i = correlatedTwoFactorCov l ψ ρ 0 i at h
      have hne : (0 : Fin 5) ≠ i := by intro he; subst i; simp at hi
      simp only [cov_entry, h₀eq, hne, ite_false, add_zero, Fin.val_zero, Nat.zero_lt_succ,
        true_iff, not_lt_of_ge hi] at h
      exact mul_left_cancel₀ h₀ne (by simpa only [mul_assoc] using h)
    have hc₃ := cross 3 (by decide)
    have hc₄ := cross 4 (by decide)
    have h₃' : l' 3 ≠ 0 := fun h => mul_ne_zero h₃ hρ (hc₃.symm.trans (by rw [h, zero_mul]))
    have h₄' : l' 4 ≠ 0 := fun h => mul_ne_zero h₄ hρ (hc₄.symm.trans (by rw [h, zero_mul]))
    have hsq := recover_corr_sq l' ψ' ρ' (ne_of_gt h₀') h₃' h₄'
    rw [hC, h₀eq] at hsq
    have hρeq : ρ' = ρ := by
      have hs := hsq.trans (recover_corr_sq l ψ ρ h₀ne h₃ h₄).symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
      · exact he
      · rw [he, mul_neg, ← neg_mul] at hc₃
        have hl : -l' 3 = l 3 := mul_right_cancel₀ hρ hc₃
        rw [← hl] at hsign
        nlinarith [sq_nonneg (l' 3)]
    exact ⟨hρeq, known hρ hρeq⟩
  · intro h₄ h₃ hψ t ht ht₁ l' ψ'
    have ht₀ : 0 < t := (abs_nonneg ρ).trans_lt ht
    refine ⟨rescale_cov l ψ ρ t h₄ ht₀.ne', ?_, ?_, ?_⟩
    · rw [abs_div, abs_of_pos ht₀, div_lt_iff₀ ht₀, one_mul]
      exact ht
    · intro i
      by_cases hi : i = 3
      · subst i
        simp only [ψ', Function.update_self]
        exact add_nonneg (hψ 3) (mul_nonneg (sub_nonneg.mpr (by nlinarith)) (sq_nonneg _))
      · simpa [ψ', Function.update_of_ne hi] using hψ i
    · intro ht' heq
      have h := congrFun heq 3
      change Function.update l 3 (t * l 3) 3 = l 3 at h
      rw [Function.update_self, ← one_mul (l 3)] at h
      exact ht'.ne (mul_right_cancel₀ h₃ (by simpa only [one_mul] using h))

end MathlibExt.Probability.Statistics.Measurement
