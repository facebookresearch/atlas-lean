/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LinearBandit.EllipticalPotential
import MathlibExt.LinearAlgebra.Matrix.LogDetTrace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Log-determinant potential of Online Newton Step -/

@[expose] public section

open scoped Matrix

namespace Cslib.MachineLearning.OnlineNewtonStep

open LinearBandit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma quadratic_le_log_det_increment {A : Matrix ι ι ℝ} (u : ι → ℝ)
    (hA : A.PosDef) (hB : (A + Matrix.vecMulVec u u).PosDef) :
    u ⬝ᵥ ((A + Matrix.vecMulVec u u)⁻¹ *ᵥ u) ≤
      Real.log (A + Matrix.vecMulVec u u).det - Real.log A.det := by
  let B := A + Matrix.vecMulVec u u
  have hBunit : IsUnit B.det := hB.det_pos.ne'.isUnit
  have hinv : (B⁻¹).det = 1 / B.det := by
    apply (eq_div_iff hB.det_pos.ne').mpr
    exact B.det_nonsing_inv_mul_det hBunit
  have ht := hB.inv.log_det_mul_le_trace hA
  rw [hinv, one_div, inv_mul_eq_div, Real.log_div hA.det_pos.ne' hB.det_pos.ne'] at ht
  have htr := congrArg Matrix.trace (B.nonsing_inv_mul hBunit)
  change (B⁻¹ * (A + Matrix.vecMulVec u u)).trace = (1 : Matrix ι ι ℝ).trace at htr
  rw [mul_add, Matrix.trace_add, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm (B⁻¹ *ᵥ u) u, Matrix.trace_one] at htr
  change u ⬝ᵥ (B⁻¹ *ᵥ u) ≤ Real.log B.det - Real.log A.det
  linarith

private lemma det_smul_one (ε : ℝ) :
    (ε • (1 : Matrix ι ι ℝ)).det = ε ^ Fintype.card ι := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]

/-- **Online Newton Step log-determinant potential.** Start with `ε • 1` for `ε > 0` and
add `g t * (g t)ᵀ` at round `t`. For every round `0 ≤ t < T`, assume the Euclidean norm
`√(g t ⬝ᵥ g t)` is at most `G`. The sum of the quadratic forms using the **post-update**
inverses is bounded by the log-determinant ratio, which is at most
`d * log (1 + T * G ^ 2 / ε)` in dimension `d`.

Source: Hazan, *Introduction to Online Convex Optimization*, 2nd ed., §4.4,
proof of Theorem 4.5 and Lemma 4.7. This is the matrix potential bound, not a regret guarantee. -/
lemma logDetPotential (ε : ℝ) (hε : 0 < ε) (g : ℕ → ι → ℝ) (T : ℕ) (G : ℝ)
    (hg : ∀ t < T, Real.sqrt (g t ⬝ᵥ g t) ≤ G) :
    let A := ellipticalGram (ε • (1 : Matrix ι ι ℝ)) g
    (∑ t ∈ Finset.range T, g t ⬝ᵥ ((A (t + 1))⁻¹ *ᵥ g t)) ≤
      Real.log ((A T).det / (A 0).det) ∧
      Real.log ((A T).det / (A 0).det) ≤
        (Fintype.card ι : ℝ) * Real.log (1 + (T : ℝ) * G ^ 2 / ε) := by
  let V : Matrix ι ι ℝ := ε • (1 : Matrix ι ι ℝ)
  let A := ellipticalGram V g
  change (∑ t ∈ Finset.range T, g t ⬝ᵥ ((A (t + 1))⁻¹ *ᵥ g t)) ≤
      Real.log ((A T).det / (A 0).det) ∧
      Real.log ((A T).det / (A 0).det) ≤
        (Fintype.card ι : ℝ) * Real.log (1 + (T : ℝ) * G ^ 2 / ε)
  have hV : V.PosDef := by
    have hdiag : V = Matrix.diagonal (fun _ : ι => ε) := by
      ext i j
      by_cases h : i = j
      · subst j
        simp [V, Matrix.smul_apply]
      · simp [V, Matrix.smul_apply, h]
    rw [hdiag, Matrix.posDef_diagonal_iff]
    exact fun _ => hε
  have hA (t : ℕ) : (A t).PosDef := ellipticalGram_posDef hV g t
  have hnext (t : ℕ) : A (t + 1) = A t + Matrix.vecMulVec (g t) (g t) :=
    ellipticalGram_succ V g t
  have hzero : A 0 = V := ellipticalGram_zero V g
  constructor
  · rw [Real.log_div (hA T).det_pos.ne' (hA 0).det_pos.ne',
      ← Finset.sum_range_sub (fun t : ℕ => Real.log (A t).det) T]
    apply Finset.sum_le_sum
    intro t _
    have hstep := quadratic_le_log_det_increment (g t) (hA t) ((hnext t) ▸ hA (t + 1))
    simpa only [← hnext t] using hstep
  · rw [hzero]
    by_cases hd : 0 < Fintype.card ι
    · let d : ℝ := Fintype.card ι
      have hd1 : 1 ≤ d := Nat.one_le_cast.mpr hd
      have hd0 : 0 < d := Nat.cast_pos.mpr hd
      have hdne : d ≠ 0 := hd0.ne'
      have htr : V.trace = ε * d := by simp [V, d, Matrix.trace_smul, Matrix.trace_one]
      have hdet : V.det ^ d⁻¹ = ε := by
        change (ε • (1 : Matrix ι ι ℝ)).det ^ d⁻¹ = ε
        rw [det_smul_one, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
        change ε ^ (d * d⁻¹) = ε
        rw [mul_inv_cancel₀ hdne, Real.rpow_one]
      have hg' : ∀ t < T, g t ⬝ᵥ g t ≤ |G| ^ 2 := by
        intro t ht
        have hdot : 0 ≤ g t ⬝ᵥ g t := by
          unfold dotProduct
          exact Finset.sum_nonneg fun i _ => mul_self_nonneg (g t i)
        have hnorm := hg t ht
        have hG := (Real.sqrt_nonneg _).trans hnorm
        have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) hG).mpr hnorm
        rw [Real.sq_sqrt hdot] at hs
        simpa only [sq_abs] using hs
      have h := log_det_ellipticalGram_ratio_le hV g (abs_nonneg G) T hg' hd
      change Real.log ((A T).det / V.det) ≤ d * Real.log ((V.trace + T * |G| ^ 2) /
        (d * V.det ^ d⁻¹)) at h
      rw [htr, hdet, sq_abs] at h
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ hd0.le
      apply Real.log_le_log
      · positivity
      · rw [div_le_iff₀ (mul_pos hd0 hε)]
        have heq : (1 + (T : ℝ) * G ^ 2 / ε) * (d * ε) =
            ε * d + d * ((T : ℝ) * G ^ 2) := by
          field_simp
        rw [heq]
        linarith only [mul_le_mul_of_nonneg_right hd1 (show 0 ≤ (T : ℝ) * G ^ 2 by positivity)]
    · have hd0 : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos hd
      have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd0
      simp [Matrix.det_isEmpty]

end Cslib.MachineLearning.OnlineNewtonStep
