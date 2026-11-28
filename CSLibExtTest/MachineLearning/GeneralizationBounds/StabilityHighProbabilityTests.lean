/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.StabilityHighProbability
import Mathlib.Probability.UniformOn

open MeasureTheory Real ProbabilityTheory

namespace CSLibExt.MachineLearning.GeneralizationBounds

-- T1: a constant algorithm family is `0`-remove-one stable.
example {𝒵 H : Type*} (L : H → 𝒵 → ℝ) (h : H) (n : ℕ) :
    IsRemoveOneUniformlyStable L (fun _ _ => h) n 0 := by
  intro S i z
  simp

-- T1b: at `β = 0` the main bound keeps only the `M` square-root term.
example (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin (n + 1) => ν).real
      {S | risk (fun (w : ℝ) (z : ℝ) => min 1 |w - z|) ν 0 ≤
        empiricalRisk (fun (w : ℝ) (z : ℝ) => min 1 |w - z|) S 0 +
        √(log (1 / δ) / (2 * ((n : ℝ) + 1)))} := by
  have hstab : IsRemoveOneUniformlyStable (fun (w : ℝ) (z : ℝ) => min 1 |w - z|)
      (fun _ _ => (0 : ℝ)) n 0 := by
    intro S i z
    simp
  have hmeas : Measurable fun _p : (Fin (n + 1) → ℝ) × ℝ =>
      (fun (w : ℝ) (z : ℝ) => min 1 |w - z|)
        ((fun _ _ => (0 : ℝ)) (n + 1) _p.1) _p.2 := by
    fun_prop
  have hbdd : ∀ (S : Fin (n + 1) → ℝ) (z : ℝ),
      0 ≤ (fun (w : ℝ) (z : ℝ) => min 1 |w - z|)
        ((fun _ _ => (0 : ℝ)) (n + 1) S) z ∧
      (fun (w : ℝ) (z : ℝ) => min 1 |w - z|)
        ((fun _ _ => (0 : ℝ)) (n + 1) S) z ≤ 1 := by
    intro S z
    show 0 ≤ min 1 |(0 : ℝ) - z| ∧ min 1 |(0 : ℝ) - z| ≤ 1
    exact ⟨le_min zero_le_one (abs_nonneg _), min_le_left _ _⟩
  have hmain := one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable (ν := ν)
    (M := 1) hmeas hbdd hstab hδ0 hδ1
  simp only [mul_zero, zero_add, add_zero, one_mul] at hmain
  exact hmain

-- Loss for the Bool mean test.
private def boolTestLoss : ℝ → Bool → ℝ :=
  fun h b => min 1 ‖h - (if b then 1 else 0)‖

-- Empirical-mean algorithm family on Bool samples; the size-`0` value is `0`.
private noncomputable def boolTestMean : (k : ℕ) → (Fin k → Bool) → ℝ :=
  fun k S => (1 / (k : ℝ)) * ∑ i, (if S i then (1 : ℝ) else 0)

private theorem abs_min_one_sub_le (a b : ℝ) : |min 1 a - min 1 b| ≤ |a - b| := by
  rcases le_total a 1 with ha | ha <;> rcases le_total b 1 with hb | hb
  · rw [min_eq_right ha, min_eq_right hb]
  · rw [min_eq_right ha, min_eq_left hb, abs_of_nonpos (by linarith : a - 1 ≤ 0),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · rw [min_eq_left ha, min_eq_right hb, abs_of_nonneg (by linarith : 0 ≤ 1 - b),
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    linarith
  · rw [min_eq_left ha, min_eq_left hb, sub_self, abs_zero]
    exact abs_nonneg _

private theorem boolTestLoss_lip (a b : ℝ) (z : Bool) :
    |boolTestLoss a z - boolTestLoss b z| ≤ |a - b| := by
  simp only [boolTestLoss]
  refine (abs_min_one_sub_le _ _).trans ?_
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have hsub : (a - (if z then (1 : ℝ) else 0)) - (b - (if z then (1 : ℝ) else 0)) =
      a - b := by ring
  rw [hsub, Real.norm_eq_abs]

private theorem ind_sum_split (n : ℕ) (S : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    (∑ j, (if S j then (1 : ℝ) else 0)) = (if S i then (1 : ℝ) else 0) +
      ∑ _j : Fin n, (if Fin.removeNth i S _j then (1 : ℝ) else 0) :=
  Fin.sum_univ_succAbove _ i

private theorem ind_nonneg (b : Bool) : (0 : ℝ) ≤ (if b then 1 else 0) := by
  cases b <;> simp

private theorem ind_le_one (b : Bool) : (if b then (1 : ℝ) else 0) ≤ 1 := by
  cases b <;> simp

private theorem ind_sum_nonneg (n : ℕ) (S : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    0 ≤ ∑ _j : Fin n, (if Fin.removeNth i S _j then (1 : ℝ) else 0) :=
  Finset.sum_nonneg fun _j _ => ind_nonneg _

private theorem ind_sum_le (n : ℕ) (S : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    ∑ _j : Fin n, (if Fin.removeNth i S _j then (1 : ℝ) else 0) ≤ (n : ℝ) := by
  calc ∑ _j : Fin n, (if Fin.removeNth i S _j then (1 : ℝ) else 0)
      ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun _j _ => ind_le_one _
    _ = (n : ℝ) := by simp

private theorem boolTestMean_stable (n : ℕ) :
    IsRemoveOneUniformlyStable boolTestLoss boolTestMean n (1 / ((n : ℝ) + 1)) := by
  cases n with
  | zero =>
    intro S i z
    have hT : (∑ _j : Fin 0, (if Fin.removeNth i S _j then (1 : ℝ) else 0)) = 0 := by
      simp
    have hsplit := ind_sum_split 0 S i
    rw [hT, add_zero] at hsplit
    have hxi0 : (0 : ℝ) ≤ (if S i then 1 else 0) := ind_nonneg _
    have hxi1 : (if S i then (1 : ℝ) else 0) ≤ 1 := ind_le_one _
    have c1 : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
    have hmeans : |boolTestMean (0 + 1) S - boolTestMean 0 (Fin.removeNth i S)| ≤
        1 / (((0 : ℕ) : ℝ) + 1) := by
      simp only [boolTestMean, hsplit, hT]
      rw [Nat.cast_zero, c1, zero_add, div_one, div_zero, mul_zero, sub_zero, one_mul,
        abs_of_nonneg hxi0]
      exact hxi1
    have hLip := boolTestLoss_lip (boolTestMean (0 + 1) S)
      (boolTestMean 0 (Fin.removeNth i S)) z
    exact hLip.trans hmeans
  | succ m =>
    intro S i z
    have hsplit := ind_sum_split (m + 1) S i
    have hT0 := ind_sum_nonneg (m + 1) S i
    have hTn := ind_sum_le (m + 1) S i
    have hxi : (if S i then (1 : ℝ) else 0) = 0 ∨
        (if S i then (1 : ℝ) else 0) = 1 := by
      generalize S i = b
      cases b <;> simp
    set a : ℝ := ((m + 1 : ℕ) : ℝ) with hadef
    set T : ℝ := ∑ _j : Fin (m + 1),
      (if Fin.removeNth i S _j then (1 : ℝ) else 0)
    set xi : ℝ := (if S i then (1 : ℝ) else 0)
    have hN : (0 : ℝ) < a := by
      rw [hadef]
      exact Nat.cast_pos.mpr (Nat.succ_pos m)
    have ha0 : a ≠ 0 := ne_of_gt hN
    have ha10 : a + 1 ≠ 0 := ne_of_gt (by positivity)
    have hcast : (((m + 1) + 1 : ℕ) : ℝ) = a + 1 := by
      rw [hadef, Nat.cast_add, Nat.cast_one]
    have hD : (0 : ℝ) < a * (a + 1) := mul_pos hN (by linarith)
    have hmeans : |boolTestMean ((m + 1) + 1) S -
        boolTestMean (m + 1) (Fin.removeNth i S)| ≤ 1 / (a + 1) := by
      simp only [boolTestMean, hsplit, hcast, ← hadef]
      have hid : (1 / (a + 1)) * (xi + T) - (1 / a) * T =
          (a * xi - T) / (a * (a + 1)) := by
        field_simp
        ring
      rw [hid, abs_div, abs_of_pos hD, div_le_iff₀ hD]
      have hDD : (1 / (a + 1)) * (a * (a + 1)) = a := by
        field_simp
      rw [hDD]
      rcases hxi with h0 | h1
      · rw [h0, mul_zero, zero_sub, abs_neg, abs_of_nonneg hT0]
        exact hTn
      · rw [h1, mul_one, abs_of_nonneg (show (0 : ℝ) ≤ a - T by linarith)]
        linarith
    have hLip := boolTestLoss_lip (boolTestMean ((m + 1) + 1) S)
      (boolTestMean (m + 1) (Fin.removeNth i S)) z
    exact hLip.trans hmeans

private theorem boolTestMean_meas (n : ℕ) :
    Measurable fun _p : (Fin (n + 1) → Bool) × Bool =>
      boolTestLoss (boolTestMean (n + 1) _p.1) _p.2 :=
  measurable_of_countable _

private theorem boolTestMean_bdd (n : ℕ) (S : Fin (n + 1) → Bool) (z : Bool) :
    0 ≤ boolTestLoss (boolTestMean (n + 1) S) z ∧
      boolTestLoss (boolTestMean (n + 1) S) z ≤ 1 := by
  simp only [boolTestLoss]
  exact ⟨le_min zero_le_one (norm_nonneg _), min_le_left _ _⟩

private theorem boolTestMean_abs (k : ℕ) (S : Fin k → Bool) (z : Bool) :
    |boolTestLoss (boolTestMean k S) z| ≤ 1 := by
  simp only [boolTestLoss]
  rw [abs_of_nonneg (le_min zero_le_one (norm_nonneg _))]
  exact min_le_left _ _

-- T2a: the Bool mean algorithm is `1/(n+1)`-remove-one stable for every `n`.
example (n : ℕ) :
    IsRemoveOneUniformlyStable boolTestLoss boolTestMean n (1 / ((n : ℝ) + 1)) :=
  boolTestMean_stable n

-- T2b: the `κ = 1` division corollary at sample size `100` and `δ = 1/20`.
example : 1 - 1 / 20 ≤
    (Measure.pi fun _ : Fin (99 + 1) => uniformOn (Set.univ : Set Bool)).real
      {S | risk boolTestLoss (uniformOn (Set.univ : Set Bool)) (boolTestMean (99 + 1) S) ≤
        empiricalRisk boolTestLoss S (boolTestMean (99 + 1) S) + 1 / 50 +
        5 * √(log 20 / 200)} := by
  have hstab := boolTestMean_stable 99
  have hmeas := boolTestMean_meas 99
  have hbdd := boolTestMean_bdd 99
  have hmain := one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable_div
    (ν := uniformOn (Set.univ : Set Bool)) (κ := 1) (M := 1) hmeas hbdd hstab
    (δ := 1 / 20) (by norm_num) (by norm_num)
  have e99 : ((99 : ℕ) : ℝ) + 1 = 100 := by norm_num
  have g1 : 2 * (1 : ℝ) / 100 = 1 / 50 := by norm_num
  have g2 : (4 : ℝ) * 1 + 1 = 5 := by norm_num
  have g3 : (1 : ℝ) / (1 / 20) = 20 := by norm_num
  have g4 : (2 : ℝ) * 100 = 200 := by norm_num
  rw [e99, g1, g2, g3, g4] at hmain
  exact hmain

-- T3 bridge at size `100`, with constant `2 * (1/100)`.
private theorem boolTestMean_replace100 :
    IsUniformlyStable boolTestLoss (boolTestMean 100) (2 * (1 / 100)) := by
  have hstab := boolTestMean_stable 99
  have hrep := isUniformlyStable_two_mul_of_isRemoveOneUniformlyStable hstab
  have e99 : ((99 : ℕ) : ℝ) + 1 = 100 := by norm_num
  have n99 : 99 + 1 = 100 := rfl
  rw [n99, e99] at hrep
  exact hrep

-- T3a: replace-one stability `2 * (1/100)` from T2 at sample size `100`.
example : IsUniformlyStable boolTestLoss (boolTestMean 100) (2 * (1 / 100)) :=
  boolTestMean_replace100

-- T3b: the expected empirical-minus-risk gap is at most `1/50`.
example : |∫ S, (empiricalRisk boolTestLoss S (boolTestMean 100 S) -
      risk boolTestLoss (uniformOn (Set.univ : Set Bool)) (boolTestMean 100 S))
      ∂(Measure.pi fun _ : Fin 100 => uniformOn (Set.univ : Set Bool))| ≤ 1 / 50 := by
  have hmeas : Measurable fun _p : (Fin 100 → Bool) × Bool =>
      boolTestLoss (boolTestMean 100 _p.1) _p.2 :=
    measurable_of_countable _
  have hbdd : ∀ S z, |boolTestLoss (boolTestMean 100 S) z| ≤ (1 : ℝ) :=
    fun S z => boolTestMean_abs 100 S z
  have hgap := abs_integral_empiricalRisk_sub_risk_le
    (ν := uniformOn (Set.univ : Set Bool)) (M := 1) hmeas hbdd boolTestMean_replace100
  have g6 : 2 * (1 / (100 : ℝ)) = 1 / 50 := by norm_num
  rw [g6] at hgap
  exact hgap

-- T4a: the tail bound with zero loss, `M = 0` and `β = 0`.
example (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin (n + 1) => ν).real
        {S | ε + 2 * 0 < risk (fun _ _ => (0 : ℝ)) ν ((fun _ _ => (0 : ℝ)) (n + 1) S) -
          empiricalRisk (fun _ _ => (0 : ℝ)) S ((fun _ _ => (0 : ℝ)) (n + 1) S)} ≤
      exp (-2 * ((n : ℝ) + 1) * ε ^ 2 / (4 * ((n : ℝ) + 1) * 0 + 0) ^ 2) := by
  have hstab : IsRemoveOneUniformlyStable (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ))
      (fun _ _ => (0 : ℝ)) n 0 := by
    intro S i z
    simp
  have hmeas : Measurable fun _p : (Fin (n + 1) → ℝ) × ℝ =>
      (fun _ _ => (0 : ℝ)) ((fun _ _ => (0 : ℝ)) (n + 1) _p.1) _p.2 :=
    measurable_const
  have hbdd : ∀ (S : Fin (n + 1) → ℝ) (z : ℝ),
      0 ≤ (fun _ _ => (0 : ℝ)) ((fun _ _ => (0 : ℝ)) (n + 1) S) z ∧
      (fun _ _ => (0 : ℝ)) ((fun _ _ => (0 : ℝ)) (n + 1) S) z ≤ 0 :=
    fun S z => ⟨le_refl _, le_refl _⟩
  exact measureReal_lt_risk_sub_empiricalRisk_le_of_isRemoveOneUniformlyStable (ν := ν)
    (M := 0) hmeas hbdd hstab hε

-- T4b: the main bound with zero loss, `M = 0` and `β = 0`.
example (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin (n + 1) => ν).real
      {S | risk (fun _ _ => (0 : ℝ)) ν ((fun _ _ => (0 : ℝ)) (n + 1) S) ≤
        empiricalRisk (fun _ _ => (0 : ℝ)) S ((fun _ _ => (0 : ℝ)) (n + 1) S) + 2 * 0 +
        (4 * ((n : ℝ) + 1) * 0 + 0) * √(log (1 / δ) / (2 * ((n : ℝ) + 1)))} := by
  have hstab : IsRemoveOneUniformlyStable (fun (_ : ℝ) (_ : ℝ) => (0 : ℝ))
      (fun _ _ => (0 : ℝ)) n 0 := by
    intro S i z
    simp
  have hmeas : Measurable fun _p : (Fin (n + 1) → ℝ) × ℝ =>
      (fun _ _ => (0 : ℝ)) ((fun _ _ => (0 : ℝ)) (n + 1) _p.1) _p.2 :=
    measurable_const
  have hbdd : ∀ (S : Fin (n + 1) → ℝ) (z : ℝ),
      0 ≤ (fun _ _ => (0 : ℝ)) ((fun _ _ => (0 : ℝ)) (n + 1) S) z ∧
      (fun _ _ => (0 : ℝ)) ((fun _ _ => (0 : ℝ)) (n + 1) S) z ≤ 0 :=
    fun S z => ⟨le_refl _, le_refl _⟩
  exact one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable (ν := ν) (M := 0)
    hmeas hbdd hstab hδ0 hδ1

#print axioms abs_sub_le_two_mul_of_isRemoveOneUniformlyStable
#print axioms isUniformlyStable_two_mul_of_isRemoveOneUniformlyStable
#print axioms measureReal_lt_risk_sub_empiricalRisk_le_of_isRemoveOneUniformlyStable
#print axioms one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable
#print axioms one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable_div

end CSLibExt.MachineLearning.GeneralizationBounds
