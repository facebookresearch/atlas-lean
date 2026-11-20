/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Probability.FSPerEdge
import Code.Probability.KKLLogOptimisation
import Code.Probability.ConvexGapHC

open scoped BigOperators
open Finset

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]



theorem nhb_var_le_damped_add [Nonempty E] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace E → Bool) :
    OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ≤
      (∑ S ∈ (univ.erase (∅ : Finset E)),
          ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p)))
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        + (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2
            * totalInfl (OSSS.bernoulliWeight p)
              (fun ω => if φ ω then (1 : ℝ) else 0) := by
  let f : ConfigSpace E → ℝ := fun ω => if φ ω then 1 else 0
  let A : ℝ := 4 * p * (1 - p)
  let c : Finset E → ℝ := fun S => (ptn_coeff p f S) ^ 2
  have hA0 : 0 < A := by dsimp [A]; nlinarith
  have hA1 : A ≤ 1 := by dsimp [A]; nlinarith [sq_nonneg (1 - 2 * p)]
  have hc (S : Finset E) : 0 ≤ c S := sq_nonneg _
  have hterm : ∀ S ∈ (univ.erase (∅ : Finset E)),
      c S ≤ (A ^ (S.card - 1) / A) * c S + (1 - A) * (S.card : ℝ) * c S := by
    intro S hS
    have hSne : S ≠ ∅ := (Finset.mem_erase.mp hS).1
    have hcard : 1 ≤ S.card := (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne))
    by_cases h1 : S.card = 1
    · rw [h1]
      simp only [Nat.cast_one, Nat.reduceSubDiff, pow_zero, one_div]
      have hAle : A ≤ 1 := hA1
      have hdiv : c S ≤ A⁻¹ * c S := by
        have hinv : (1 : ℝ) ≤ A⁻¹ := (one_le_inv₀ hA0).2 hAle
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv (hc S)
      nlinarith [mul_nonneg (sub_nonneg.mpr hA1) (hc S)]
    · have hcard2 : 2 ≤ S.card := by omega
      have hdamp := klo_one_sub_pow_le A hA0.le hA1 (S.card - 2)
      have hpow : A ^ (S.card - 1) / A = A ^ (S.card - 2) := by
        rw [show S.card - 1 = (S.card - 2) + 1 by omega, pow_succ, mul_div_cancel_right₀]
        exact hA0.ne'
      rw [hpow]
      have hcoef : 1 ≤ A ^ (S.card - 2) + (1 - A) * (S.card : ℝ) := by
        have hcast : ((S.card - 2 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Nat.sub_le _ _
        have hnon : 0 ≤ 1 - A := sub_nonneg.mpr hA1
        nlinarith [mul_le_mul_of_nonneg_left hcast hnon]
      nlinarith [mul_le_mul_of_nonneg_right hcoef (hc S)]
  have hsum := Finset.sum_le_sum hterm
  rw [ptn_var_eq_fourierWeight hp0 hp1 f]
  have hweighted :
      (∑ S ∈ univ.erase (∅ : Finset E), (S.card : ℝ) * c S) =
        (ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) f := by
    have htot := ptn_totalInfl_eq_fourierWeight hp0 hp1 φ
    change totalInfl (OSSS.bernoulliWeight p) f = _ at htot
    have hall : (∑ S : Finset E, (S.card : ℝ) * c S) =
        ∑ S ∈ univ.erase (∅ : Finset E), (S.card : ℝ) * c S := by
      rw [← Finset.add_sum_erase univ (fun S => (S.card : ℝ) * c S)
        (Finset.mem_univ (∅ : Finset E))]
      simp
    rw [hall] at htot
    have hspos : 0 < (ptn_sigma p) ^ 2 := sq_pos_of_pos (ptn_sigma_pos hp0 hp1)
    rw [htot]
    rw [← mul_assoc, show (ptn_sigma p) ^ 2 * (1 / (ptn_sigma p) ^ 2) = 1 by
      field_simp [ne_of_gt (ptn_sigma_pos hp0 hp1)], one_mul]
  calc
    (∑ S ∈ univ.erase (∅ : Finset E), c S)
        ≤ ∑ S ∈ univ.erase (∅ : Finset E),
          ((A ^ (S.card - 1) / A) * c S + (1 - A) * (S.card : ℝ) * c S) := hsum
    _ = (∑ S ∈ univ.erase (∅ : Finset E), (A ^ (S.card - 1) / A) * c S)
          + (1 - A) * (∑ S ∈ univ.erase (∅ : Finset E), (S.card : ℝ) * c S) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro S _
        ring
    _ = (∑ S ∈ univ.erase (∅ : Finset E), (A ^ (S.card - 1) / A) * c S)
          + (1 - A) * ((ptn_sigma p) ^ 2 * totalInfl (OSSS.bernoulliWeight p) f) := by
        rw [hweighted]
    _ = _ := by simp only [f, A, c]; ring



theorem nhb_nearHalf_kkl [Nonempty E] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace E → Bool) :
    2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)) ≤
      (1 + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2
          * Real.log (1 / maxInfl (OSSS.bernoulliWeight p)
            (fun ω => if φ ω then (1 : ℝ) else 0)))
        * totalInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) := by
  let f : ConfigSpace E → ℝ := fun ω => if φ ω then 1 else 0
  let Q := ∑ S ∈ (univ.erase (∅ : Finset E)),
    ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p))) * (ptn_coeff p f S) ^ 2
  let L := Real.log (1 / maxInfl (OSSS.bernoulliWeight p) f)
  let T := totalInfl (OSSS.bernoulliWeight p) f
  have hQ : 2 * Q * L ≤ T := fpe_dampedVarLogGain hp0 hp1 φ
  have hV := nhb_var_le_damped_add hp0 hp1 φ
  change OSSS.var (OSSS.bernoulliWeight p) f ≤
    Q + (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * T at hV
  change 2 * OSSS.var (OSSS.bernoulliWeight p) f * L ≤
    (1 + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * L) * T
  have hL : 0 ≤ L := by
    have hmaxle : maxInfl (OSSS.bernoulliWeight p) f ≤ 1 :=
      cvg_maxInfl_le_one hp0.le hp1.le φ
    have hmax0 := kkl_maxInfl_nonneg
      (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
    by_cases hz : maxInfl (OSSS.bernoulliWeight p) f = 0
    · simp [L, hz]
    · have hpos : 0 < maxInfl (OSSS.bernoulliWeight p) f := lt_of_le_of_ne hmax0 (Ne.symm hz)
      exact Real.log_nonneg ((one_le_div hpos).2 hmaxle)
  calc
    2 * OSSS.var (OSSS.bernoulliWeight p) f * L
        ≤ 2 * (Q + (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * T) * L := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hV (by norm_num)) hL
    _ = 2 * Q * L + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * L * T := by ring
    _ ≤ T + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * L * T := by
      linarith [hQ]
    _ = (1 + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * L) * T := by ring








theorem nhb_nearHalf_kkl_absorbed [Nonempty E] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace E → Bool)
    (hcorr : 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)) ≤ 1) :
    OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) := by
  let f : ConfigSpace E → ℝ := fun ω => if φ ω then 1 else 0
  let L := Real.log (1 / maxInfl (OSSS.bernoulliWeight p) f)
  let T := totalInfl (OSSS.bernoulliWeight p) f
  have h := nhb_nearHalf_kkl hp0 hp1 φ
  have hT : 0 ≤ T := kkl_totalInfl_nonneg
    (OSSS.bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le) f
  change 2 * OSSS.var (OSSS.bernoulliWeight p) f * L ≤
    (1 + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * L) * T at h
  change 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * L ≤ 1 at hcorr
  change OSSS.var (OSSS.bernoulliWeight p) f * L ≤ T
  have hfactor :
      (1 + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * L) * T ≤ 2 * T := by
    exact mul_le_mul_of_nonneg_right (by linarith) hT
  nlinarith [h, hfactor]

end StatMech.Probability
