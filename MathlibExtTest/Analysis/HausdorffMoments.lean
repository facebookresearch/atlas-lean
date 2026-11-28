/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.HausdorffMoments

/-!
# Tests for the Hausdorff moment criteria

A point mass at a mixed corner has a nonconstant moment sequence. The difference of two
corner point masses gives moments of both signs. In dimension zero the sole moment can be
any nonnegative real number in the positive criterion and any real number in the signed one.
-/

open MeasureTheory MathlibExt.Analysis.HausdorffMomentsWanted.Analysis

-- The two coordinates of this atom distinguish the zeroth and positive powers of zero.
example (k n : Fin 2 → ℕ) (h : k ≤ n) :
    0 ≤ diff (fun m : Fin 2 → ℕ => if m 0 = 0 then 1 else 0) k n := by
  classical
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have hx : x ∈ cube 2 := by
    intro i
    fin_cases i <;> norm_num [x]
  apply (hausdorff_positivity _).mp _ k n h
  refine ⟨Measure.dirac x, inferInstance, fun m => ?_⟩
  rw [momentOf, setIntegral_dirac, ite_eq_left hx]
  by_cases hm : m 0 = 0 <;> simp [monomial, Fin.prod_univ_two, x, hm]

example (c : ℝ) :
    IsPositiveMomentConfiguration (fun _ : Fin 0 → ℕ => c) ↔ 0 ≤ c := by
  rw [hausdorff_positivity]
  have hd (k n : Fin 0 → ℕ) : diff (fun _ => c) k n = c := by
    simp [diff, multiChoose, Pi.card_Iic]
  simp [hd]

-- Two opposite signed corner atoms give moments of both signs.
example : HausdorffBounded
    (fun m : Fin 2 → ℕ => (if m 1 = 0 then 1 else 0) - (if m 0 = 0 then 1 else 0)) := by
  classical
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let y : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have hx : x ∈ cube 2 := by
    intro i
    fin_cases i <;> norm_num [x]
  have hy : y ∈ cube 2 := by
    intro i
    fin_cases i <;> norm_num [y]
  apply (hausdorff_hildebrandt_schoenberg _).mp
  refine ⟨Measure.dirac x, Measure.dirac y, inferInstance, inferInstance, fun m => ?_⟩
  rw [momentOf, momentOf, setIntegral_dirac, setIntegral_dirac, ite_eq_left hx, ite_eq_left hy]
  by_cases h₀ : m 0 = 0 <;> by_cases h₁ : m 1 = 0 <;>
    simp [monomial, Fin.prod_univ_two, x, y, h₀, h₁]

-- At a corner with one zero coordinate, just one backward-difference weight survives.
private theorem cornerWeight (n k : Fin 2 → ℕ) (hk : k ≤ n) (j : Fin 2) :
    (multiChoose n k : ℝ) * diff (fun m => if m j = 0 then 1 else 0) k n =
      if k = (fun i => if i = j then n i else 0) then 1 else 0 := by
  classical
  let x (i : Fin 2) : ℝ := if i = j then 0 else 1
  have ha : (fun m : Fin 2 → ℕ => if m j = 0 then (1 : ℝ) else 0) =
      (fun m => ∏ i, x i ^ m i) := by
    funext m
    rw [Finset.prod_eq_single j (fun i _ hi => by simp [x, hi]) (by simp)]
    by_cases h : m j = 0 <;> simp [x, h]
  rw [ha, weighted_diff_prod_pow x hk]
  by_cases h : k = (fun i => if i = j then n i else 0)
  · rw [ite_eq_left h, h]
    apply Finset.prod_eq_one
    intro i _
    by_cases hij : i = j <;> simp [x, hij]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ (if i = j then n i else 0) := by
      by_contra! hall
      exact h (funext hall)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hij : i = j
    · subst i
      have hlt : k j < n j := lt_of_le_of_ne (hk j) (by simpa using hi)
      simp [x, Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)]
    · have hki : k i ≠ 0 := by simpa [hij] using hi
      simp [x, hij, hki]

-- Compute the bound without assuming any representing measure or using the forward criterion.
example : IsMomentConfiguration
    (fun m : Fin 2 → ℕ => (if m 1 = 0 then 1 else 0) - (if m 0 = 0 then 1 else 0)) := by
  classical
  let a (m : Fin 2 → ℕ) : ℝ := (if m 1 = 0 then 1 else 0) - (if m 0 = 0 then 1 else 0)
  have hb : HausdorffBounded a := by
    apply (hausdorffBounded_iff a).mpr
    refine ⟨2, fun n => ?_⟩
    let e (j i : Fin 2) := if i = j then n i else 0
    have he (j : Fin 2) : e j ∈ Finset.Iic n :=
      Finset.mem_Iic.mpr fun i => by
        by_cases h : i = j <;> simp [e, h]
    let w (j : Fin 2) (k : Fin 2 → ℕ) : ℝ := if k = e j then 1 else 0
    have hw (j : Fin 2) : ∑ k ∈ Finset.Iic n, w j k = 1 := by simp [w, he j]
    calc
      _ ≤ ∑ k ∈ Finset.Iic n, (w 1 k + w 0 k) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn := Finset.mem_Iic.mp hk
        dsimp only [a]
        rw [diff_sub, mul_sub, cornerWeight n k hkn 1, cornerWeight n k hkn 0]
        change |w 1 k - w 0 k| ≤ w 1 k + w 0 k
        simp only [w]
        split <;> split <;> norm_num
      _ = 2 := by rw [Finset.sum_add_distrib, hw 1, hw 0]; norm_num
  exact (hausdorff_hildebrandt_schoenberg a).mpr hb

-- The signed criterion has no positivity restriction on the sole moment in dimension zero.
example (c : ℝ) : IsMomentConfiguration (fun _ : Fin 0 → ℕ => c) := by
  apply (hausdorff_hildebrandt_schoenberg _).mpr
  refine ⟨|c|, fun n => ?_⟩
  have hd (k : Fin 0 → ℕ) : diff (fun _ => c) k n = c := by
    simp [diff, multiChoose, Pi.card_Iic]
  simp [hd, multiChoose, Pi.card_Iic]
