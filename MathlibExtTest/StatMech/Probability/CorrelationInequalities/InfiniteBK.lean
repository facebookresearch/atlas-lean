/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.InfiniteBK

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.InfiniteBK`

On the countable configuration space `ConfigSpace ℕ` with the events `openAt 0` and `openAt 1`
(`IsIncreasing` and `DependsOn` the window `{0, 1}` proved):
* `ibk_inequality_of_finite_dependsOn` at `p = 1/2`;
* `ibk_triple_of_finite_dependsOn` for `openAt 0, openAt 1, openAt 0`;
* `disjointOccurrence_isIncreasing` and `ibk_measure_mono_parameter` (`p = 1/3 ≤ q = 1/2`).
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.InfiniteBK

open _root_.StatMech

/-- The event "coordinate `i` is open" on `ConfigSpace ℕ`. -/
def openAt (i : ℕ) : Set (ConfigSpace ℕ) := {ω | ω i = true}

-- `openAt i` is increasing.
theorem isIncreasing_openAt (i : ℕ) : IsIncreasing (openAt i) := by
  intro x y hxy hx
  have h := hxy i
  simp only [openAt, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- `openAt i` depends only on the finite window `{0, 1}` when `i ≤ 1`.
theorem dependsOn_openAt (i : ℕ) (hi : i ∈ ({0, 1} : Finset ℕ)) :
    _root_.StatMech.DependsOn (openAt i) (({0, 1} : Finset ℕ) : Set ℕ) := by
  intro ω ω' h
  have := h i (by exact_mod_cast hi)
  simp [openAt, this]

open scoped NNReal in
-- `1/3 ≤ 1` in `ℝ≥0`.
theorem third_le_one : (1 / 3 : ℝ≥0) ≤ 1 := by
  rw [← NNReal.coe_le_coe]; norm_num

open scoped NNReal in
-- `1/3 ≤ 1/2` in `ℝ≥0`.
theorem third_le_half : (1 / 3 : ℝ≥0) ≤ 1 / 2 := by
  rw [← NNReal.coe_le_coe]; norm_num

-- The BK inequality on `ℕ` with all hypotheses instantiated.
example : (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real
      (disjointOccurrence (openAt 0) (openAt 1))
    ≤ (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (openAt 0)
      * (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (openAt 1) :=
  ibk_inequality_of_finite_dependsOn _ {0, 1} (dependsOn_openAt 0 (by simp))
    (dependsOn_openAt 1 (by simp)) (isIncreasing_openAt 0) (isIncreasing_openAt 1)

-- The three-event BK inequality.
example : (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real
      (disjointOccurrence (openAt 0) (disjointOccurrence (openAt 1) (openAt 0)))
    ≤ (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (openAt 0)
      * (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (openAt 1)
      * (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (openAt 0) :=
  ibk_triple_of_finite_dependsOn _ {0, 1} (dependsOn_openAt 0 (by simp))
    (dependsOn_openAt 1 (by simp)) (dependsOn_openAt 0 (by simp)) (isIncreasing_openAt 0)
    (isIncreasing_openAt 1) (isIncreasing_openAt 0)

-- Disjoint occurrence of increasing events is increasing.
example : IsIncreasing (disjointOccurrence (openAt 0) (openAt 1)) :=
  disjointOccurrence_isIncreasing (isIncreasing_openAt 0) (isIncreasing_openAt 1)

-- Monotonicity in the parameter, `p = 1/3 ≤ q = 1/2`.
example : (bernoulliProductMeasure (E := ℕ) (1 / 3) third_le_one).real (openAt 0)
    ≤ (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (openAt 0) :=
  ibk_measure_mono_parameter _ _ third_le_half {0, 1} (dependsOn_openAt 0 (by simp))
    (isIncreasing_openAt 0)

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.InfiniteBK
