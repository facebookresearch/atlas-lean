/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Empirical ROC area equals the Mann–Whitney statistic, with ties

Score `m` positive cases `x : Fin m → ℝ` and `n` negative cases `y : Fin n → ℝ`. The empirical
ROC curve plots, for each threshold `t`, the false-positive rate `#{j | t ≤ y j} / n` against the
true-positive rate `#{i | t ≤ x i} / m`, and joins `(0, 0)` and the points at the distinct
observed scores, in decreasing order of `t`, by straight segments (tied scores give a diagonal
segment). Its area by the trapezoidal rule equals the Mann–Whitney probability
`U / (m n)`, where `U = ∑ᵢ ∑ⱼ (1[y j < x i] + ½ 1[y j = x i])` counts ties as one half
(Bamber 1975; Hanley–McNeil 1982). So the empirical AUC estimates `P(X > Y) + ½ P(X = Y)`.

The trapezoid at a distinct score `t` runs from the ROC point at the next larger distinct score
(or from `(0, 0)` above the largest score) to the point at `t`. Since no score lies strictly
between them, that previous point has the strict rates `#{· > t}`
(`rocRateAbove_eq_rocRate_of_forall_not_mem_Ioo`, `rocRateAbove_eq_zero_of_forall_le`), which is
how `empiricalAUC` is written.

## Main results

* `ProbabilityTheory.rocRate`, `ProbabilityTheory.rocRateAbove`: empirical rates `≥ t`, `> t`.
* `ProbabilityTheory.empiricalAUC`: trapezoidal area under the empirical ROC curve.
* `ProbabilityTheory.mannWhitneyU`: the Mann–Whitney count with ties counted one half.
* `ProbabilityTheory.empiricalAUC_eq_mannWhitneyU`: `AUC = U / (m n)`.

## References

* D. Bamber, *The area above the ordinal dominance graph and the area below the receiver
  operating characteristic graph*, J. Math. Psych. 12 (1975) 387–415.
* J. A. Hanley and B. J. McNeil, *The meaning and use of the area under a receiver operating
  characteristic (ROC) curve*, Radiology 143 (1982) 29–36.
* H. B. Mann and D. R. Whitney, *On a test of whether one of two random variables is
  stochastically larger than the other*, Ann. Math. Statist. 18 (1947) 50–60.
-/

@[expose] public section

open Finset

namespace ProbabilityTheory

/-- Empirical rate `#{i | t ≤ z i} / k` of scores at or above the threshold `t` (the true- or
false-positive rate when `z` are the positive or negative scores). -/
noncomputable def rocRate {k : ℕ} (z : Fin k → ℝ) (t : ℝ) : ℝ :=
  (#{i | t ≤ z i} : ℝ) / k

/-- Empirical rate `#{i | t < z i} / k` of scores strictly above `t`: the ROC coordinate at the
next larger distinct score. -/
noncomputable def rocRateAbove {k : ℕ} (z : Fin k → ℝ) (t : ℝ) : ℝ :=
  (#{i | t < z i} : ℝ) / k

/-- Trapezoidal area under the empirical ROC curve of positive scores `x` and negative scores
`y`: the sum over the distinct observed scores `t` of the trapezoid from the point
`(rocRateAbove y t, rocRateAbove x t)` to `(rocRate y t, rocRate x t)`. -/
noncomputable def empiricalAUC {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ t ∈ univ.image x ∪ univ.image y,
    (rocRate y t - rocRateAbove y t) * (rocRate x t + rocRateAbove x t) / 2

/-- Mann–Whitney count `U = ∑ᵢ ∑ⱼ (1[y j < x i] + ½ 1[y j = x i])` of (positive, negative)
pairs ranked correctly, with ties counted one half. -/
noncomputable def mannWhitneyU {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if y j < x i then 1 else if y j = x i then 1 / 2 else 0

/-- If no score lies strictly between `t < t'`, the strict rate at `t` is the rate at `t'`: the
left end of the trapezoid at `t` is the ROC point of the next larger distinct score. -/
theorem rocRateAbove_eq_rocRate_of_forall_not_mem_Ioo {k : ℕ} {z : Fin k → ℝ} {t t' : ℝ}
    (htt' : t < t') (h : ∀ i, z i ∉ Set.Ioo t t') : rocRateAbove z t = rocRate z t' := by
  unfold rocRateAbove rocRate
  congr 3
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hi
    by_contra hlt
    exact h i ⟨hi, lt_of_not_ge hlt⟩
  · intro hi
    exact htt'.trans_le hi

/-- Above the largest score the strict rate is zero: the first trapezoid starts at `(0, 0)`. -/
theorem rocRateAbove_eq_zero_of_forall_le {k : ℕ} {z : Fin k → ℝ} {t : ℝ}
    (h : ∀ i, z i ≤ t) : rocRateAbove z t = 0 := by
  unfold rocRateAbove
  rw [filter_false_of_mem (fun i _ => not_lt.mpr (h i))]
  simp

/-- **Empirical AUC = Mann–Whitney with ties** (Bamber 1975): the trapezoidal area under the
empirical ROC curve equals `U / (m n)`, for nonempty samples. -/
theorem empiricalAUC_eq_mannWhitneyU {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (x : Fin m → ℝ) (y : Fin n → ℝ) : empiricalAUC x y = mannWhitneyU x y / (m * n) := by
  classical
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  -- the width of the trapezoid at `t` counts the negatives tied at `t`
  have hwidth : ∀ t, rocRate y t - rocRateAbove y t =
      (∑ j, if y j = t then (1 : ℝ) else 0) / n := by
    intro t
    unfold rocRate rocRateAbove
    rw [← sub_div, natCast_card_filter, natCast_card_filter, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    by_cases h1 : y j = t
    · simp [h1]
    · by_cases h2 : t < y j
      · simp [h1, h2, h2.le]
      · have : ¬ t ≤ y j := fun h => h2 (lt_of_le_of_ne h (Ne.symm h1))
        simp [h1, h2, this]
  -- the height sum at a score `s` counts positives above `s`, ties once
  have hheight : ∀ s, rocRate x s + rocRateAbove x s =
      2 * (∑ i, if s < x i then (1 : ℝ) else if s = x i then 1 / 2 else 0) / m := by
    intro s
    unfold rocRate rocRateAbove
    rw [← add_div, natCast_card_filter, natCast_card_filter, ← sum_add_distrib, mul_sum]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    by_cases h2 : s < x i
    · simp [h2, h2.le, one_add_one_eq_two]
    · by_cases h1 : s = x i
      · simp [h1]
      · have : ¬ s ≤ x i := fun h => h2 (lt_of_le_of_ne h h1)
        simp [h1, h2, this]
  unfold empiricalAUC mannWhitneyU
  simp_rw [hwidth, sum_div, sum_mul, sum_div]
  rw [sum_comm]
  have hyV : ∀ j, y j ∈ univ.image x ∪ univ.image y := fun j =>
    mem_union_right _ (mem_image_of_mem y (mem_univ j))
  have hinner : ∀ j, (∑ t ∈ univ.image x ∪ univ.image y, (if y j = t then (1 : ℝ) else 0) / n *
      (rocRate x t + rocRateAbove x t) / 2) =
      (rocRate x (y j) + rocRateAbove x (y j)) / (2 * n) := by
    intro j
    rw [sum_eq_single_of_mem (y j) (hyV j)]
    · simp only [ite_true]
      field_simp
    · intro t _ ht
      simp [Ne.symm ht]
  simp_rw [hinner, hheight]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_div]
  field_simp

end ProbabilityTheory
