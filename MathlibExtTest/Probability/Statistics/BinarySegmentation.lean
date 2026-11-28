/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.BinarySegmentation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Tests for binary segmentation: the segments of an induced partition, the CUSUM statistics of a
two-point and a three-point data vector, two runs of the algorithm (the second step falling back on
the value of `sign 0` at a tie), the two-point selection event of the source's expansion, and an
instance of the polyhedral selection theorem with feasible locations. -/

namespace MathlibExtTest.Probability.Statistics.BinarySegmentation

open Finset Matrix MathlibExt.Probability.Statistics.BinarySegmentation

/-- Tie-breaking rules exist: pick the smallest tied split point. -/
noncomputable def lowestTie : TieBreak where
  pick _ S := if h : S.Nonempty then S.min' h else 0
  pick_mem _ S h := by simpa [h] using S.min'_mem h

/-- With changepoints `2` and `5` on `{1, …, 8}`, the split point `4` lies in the segment
`{3, 4, 5}`, the split point `1` in `{1, 2}` and the split point `7` in `{6, 7, 8}`. -/
example : segmentStart {2, 5} 4 = 3 ∧ segmentEnd 8 {2, 5} 4 = 5 ∧
    segmentStart {2, 5} 1 = 1 ∧ segmentEnd 8 {2, 5} 1 = 2 ∧
    segmentStart {2, 5} 7 = 6 ∧ segmentEnd 8 {2, 5} 7 = 8 := by
  decide

/-- At step `ℓ` (counted from `1`) there are `n - ℓ - 1` competitors, each giving two rows, plus
one sign row: for `n = 4` and `k = 2`, `5 + 3 = 8` rows. -/
example : ∑ ℓ ∈ Icc 1 2, (2 * (4 - ℓ - 1) + 1) = 8 := by
  decide

/-- The CUSUM statistic of the only split of two points is `(y₂ - y₁) / √2`. -/
theorem cusum_two (y : Fin 2 → ℝ) : cusum y 1 1 2 = √(1 / 2) * (y 1 - y 0) := by
  norm_num [cusum, segmentMean, Finset.sum_filter, Fin.sum_univ_two]

/-- The data `(0, 0, 1)`: splitting after the second point has CUSUM `√(2/3)`. -/
theorem cusum_three_two : cusum ![0, 0, 1] 1 2 3 = √(2 / 3) := by
  norm_num [cusum, segmentMean, Finset.sum_filter, Fin.sum_univ_three]

/-- The data `(0, 0, 1)`: splitting after the first point has CUSUM `√(2/3) / 2`. -/
theorem cusum_three_one : cusum ![0, 0, 1] 1 1 3 = √(2 / 3) * (1 / 2) := by
  norm_num [cusum, segmentMean, Finset.sum_filter, Fin.sum_univ_three]

/-- The data `(0, 0, 1)`: on the second segment `{1, 2}` of the split after `2`, the split after
the first point has CUSUM `0`. -/
theorem cusum_three_one_left : cusum ![0, 0, 1] 1 1 2 = 0 := by
  norm_num [cusum, segmentMean, Finset.sum_filter, Fin.sum_univ_three]

/-- The first step on `(0, 0, 1)` splits after the second point, upwards, whatever the
tie-breaking rule and the value of `sign 0`. -/
theorem model_three_one (rule : TieBreak) (sign0 : ℤˣ) :
    model rule sign0 ![0, 0, 1] 1 = [(2, 1)] := by
  have h1 : splitCusum ![0, 0, 1] ∅ 1 = √(2 / 3) * (1 / 2) := by
    rw [splitCusum, show segmentStart ∅ 1 = 1 by decide, show segmentEnd 3 ∅ 1 = 3 by decide,
      cusum_three_one]
  have h2 : splitCusum ![0, 0, 1] ∅ 2 = √(2 / 3) := by
    rw [splitCusum, show segmentStart ∅ 2 = 1 by decide, show segmentEnd 3 ∅ 2 = 3 by decide,
      cusum_three_two]
  have hpos : (0 : ℝ) < √(2 / 3) := by positivity
  rw [model_succ_of_lt rule sign0 _ (by norm_num)]
  simp only [model, List.nil_append, List.cons.injEq, and_true]
  refine step_eq_of_lt (by decide) ?_ ?_
  · simp only [List.map_nil, List.toFinset_nil, h2, Units.val_one, Int.cast_one, one_mul]
    exact hpos
  · intro c hc hc2
    simp only [List.map_nil, List.toFinset_nil] at hc ⊢
    have hc1 : c = 1 := by
      simp only [freeSplits, sdiff_empty, mem_Icc] at hc
      omega
    subst hc1
    rw [h1, h2, Units.val_one, Int.cast_one, one_mul, abs_of_pos (by positivity)]
    linarith

/-- The second step on `(0, 0, 1)` splits the segment `{1, 2}`, where the CUSUM is `0`, so its
direction is the value of `sign 0`. -/
example (rule : TieBreak) (sign0 : ℤˣ) :
    model rule sign0 ![0, 0, 1] 2 = [(2, 1), (1, sign0)] := by
  have hB : (([(2, 1)] : List (ℕ × ℤˣ)).map Prod.fst).toFinset = {2} := by decide
  have hfree : freeSplits 3 {2} = {1} := by decide
  have hbest : bestSplits ![0, 0, 1] {2} = {1} := by
    rw [bestSplits, hfree]
    exact Finset.filter_true_of_mem fun c hc c' hc' => by
      rw [mem_singleton.1 hc, mem_singleton.1 hc']
  have hpick : rule.pick [(2, 1)] {1} = 1 :=
    mem_singleton.1 (rule.pick_mem _ _ (singleton_nonempty _))
  have hzero : splitCusum ![0, 0, 1] {2} 1 = 0 := by
    rw [splitCusum, show segmentStart {2} 1 = 1 by decide, show segmentEnd 3 {2} 1 = 2 by decide,
      cusum_three_one_left]
  rw [model_succ_of_lt rule sign0 _ (by norm_num), model_three_one]
  simp only [step, hB, hbest, hpick, hzero, direction, lt_irrefl, ite_false, List.cons_append,
    List.nil_append]

/-- The source's two-point example: with `n = 2`, `k = 1`, `b₁ = 1` and `d₁ = +1`, the selection
event lies between `{y₁ < y₂}` and `{y₁ ≤ y₂}`, so the sign row alone cuts it down from `ℝ²`. -/
example (rule : TieBreak) (sign0 : ℤˣ) :
    {y : Fin 2 → ℝ | y 0 < y 1} ⊆ selectionEvent 2 rule sign0 ![1] ![1] ∧
      selectionEvent 2 rule sign0 ![1] ![1] ⊆ {y : Fin 2 → ℝ | y 0 ≤ y 1} := by
  have hX : ∀ y : Fin 2 → ℝ, splitCusum y ∅ 1 = √(1 / 2) * (y 1 - y 0) := fun y => by
    rw [splitCusum, show segmentStart ∅ 1 = 1 by decide, show segmentEnd 2 ∅ 1 = 2 by decide,
      cusum_two]
  have hc : (0 : ℝ) < √(1 / 2) := by positivity
  have hT : (List.ofFn fun ℓ : Fin 1 => ((![1] : Fin 1 → ℕ) ℓ, (![1] : Fin 1 → ℤˣ) ℓ)) =
      [(1, 1)] := rfl
  constructor
  · intro y hy
    simp only [selectionEvent, Set.mem_ofPred_eq, hT]
    rw [model_succ_of_lt rule sign0 y (by norm_num)]
    simp only [model, List.nil_append, List.cons.injEq, and_true]
    refine step_eq_of_lt (by decide) ?_ ?_
    · simp only [List.map_nil, List.toFinset_nil, hX, Units.val_one, Int.cast_one, one_mul]
      exact mul_pos hc (sub_pos.2 hy)
    · intro c hc' hc1
      simp only [List.map_nil, List.toFinset_nil, freeSplits, sdiff_empty, mem_Icc] at hc'
      omega
  · intro y hy
    simp only [selectionEvent, Set.mem_ofPred_eq, hT] at hy
    rw [model_succ_of_lt rule sign0 y (by norm_num)] at hy
    simp only [model, List.nil_append, List.cons.injEq, and_true] at hy
    obtain ⟨-, habs⟩ := step_spec hy (by decide)
    simp only [List.map_nil, List.toFinset_nil, hX, Units.val_one, Int.cast_one, one_mul] at habs
    have := habs ▸ abs_nonneg (√(1 / 2) * (y 1 - y 0))
    exact sub_nonneg.1 ((mul_nonneg_iff_of_pos_left hc).1 this)

/-- The theorem applies to the feasible locations `b = (2, 1)` on `n = 3` points: `Γ` has
`3 + 1 = 4` rows, those of `selectionRow`. -/
example (d : Fin 2 → ℤˣ) :
    ∃ Γ : Matrix (Fin (∑ ℓ ∈ Icc 1 2, (2 * (3 - ℓ - 1) + 1))) (Fin 3) ℝ,
      (∃ e : (Σ ℓ : Fin 2, Option (competitors 3 ![2, 1] ℓ × Bool)) ≃
          Fin (∑ ℓ ∈ Icc 1 2, (2 * (3 - ℓ - 1) + 1)),
        ∀ i, Γ i = selectionRow 3 ![2, 1] d (e.symm i)) ∧
      (∀ i, Γ i ≠ 0) ∧ ∀ (rule : TieBreak) (sign0 : ℤˣ),
        {y | ∀ i, 0 < (Γ *ᵥ y) i} ⊆ selectionEvent 3 rule sign0 ![2, 1] d ∧
        selectionEvent 3 rule sign0 ![2, 1] d ⊆ {y | ∀ i, 0 ≤ (Γ *ᵥ y) i} ∧
        symmDiff (selectionEvent 3 rule sign0 ![2, 1] d) {y | ∀ i, 0 ≤ (Γ *ᵥ y) i} ⊆
          ⋃ i, {y | (Γ *ᵥ y) i = 0} ∧
        MeasureTheory.volume (symmDiff (selectionEvent 3 rule sign0 ![2, 1] d)
          {y | ∀ i, 0 ≤ (Γ *ᵥ y) i}) = 0 :=
  exists_polyhedral_selectionEvent ![2, 1] d (by decide) (by decide)

example : ∑ ℓ ∈ Icc 1 2, (2 * (3 - ℓ - 1) + 1) = 4 := by
  decide

/-- Two steps on three points never select the same location twice. -/
example (rule : TieBreak) (sign0 : ℤˣ) (d : Fin 2 → ℤˣ) :
    selectionEvent 3 rule sign0 ![1, 1] d = ∅ :=
  selectionEvent_eq_empty rule sign0 d fun h => by
    simpa using h.1 (a₁ := 0) (a₂ := 1) rfl

/-- One step on three points never selects the location `3`, which is no split point. -/
example (rule : TieBreak) (sign0 : ℤˣ) (d : Fin 1 → ℤˣ) :
    selectionEvent 3 rule sign0 ![3] d = ∅ :=
  selectionEvent_eq_empty rule sign0 d fun h => by
    simpa using h.2 0

/-- A single point has no split point, so the run stops at once: one step with the rule
`lowestTie` selects nothing, rather than the location `0` that the rule returns on no candidates. -/
example (sign0 : ℤˣ) (y : Fin 1 → ℝ) : model lowestTie sign0 y 1 = [] :=
  model_succ_of_le lowestTie sign0 y le_rfl

example : lowestTie.pick [] ∅ = 0 := rfl

/-- So one step on a single point selects no location at all. -/
example (rule : TieBreak) (sign0 : ℤˣ) (b : Fin 1 → ℕ) (d : Fin 1 → ℤˣ) :
    selectionEvent 1 rule sign0 b d = ∅ :=
  selectionEvent_eq_empty rule sign0 d fun h => by
    simpa using h.2 0

/-- On three points both possible steps are taken, and a third step adds nothing. -/
example (rule : TieBreak) (sign0 : ℤˣ) (y : Fin 3 → ℝ) :
    (model rule sign0 y 2).length = 2 ∧ model rule sign0 y 3 = model rule sign0 y 2 :=
  ⟨length_model_of_le rule sign0 y 2 (by norm_num), model_succ_of_le rule sign0 y (by norm_num)⟩

/-- Three steps on three points select no three locations: the selection event of any three
locations is empty, the theorem's feasibility hypothesis failing for them. -/
example (rule : TieBreak) (sign0 : ℤˣ) (b : Fin 3 → ℕ) (d : Fin 3 → ℤˣ) :
    selectionEvent 3 rule sign0 b d = ∅ :=
  selectionEvent_eq_empty rule sign0 d fun h => by
    have := le_sub_one_of_feasible (n := 3) h.1 h.2
    omega

end MathlibExtTest.Probability.Statistics.BinarySegmentation
