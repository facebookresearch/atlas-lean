/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.InhomogeneousBK

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.InhomogeneousProduct`

* `inhom_bk_inequality` on `ConfigSpace (Fin 2)` with the non-constant parameter
  `p = ![1/3, 1/2]` and the increasing events "coordinate `0` open", "coordinate `1` open";
* `inhomBernoulliProductMeasure_const`;
* `inhom_bk_of_finite_dependsOn` on `ConfigSpace ℕ` with `p n = 1/(n+2)`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.InhomogeneousProduct

open _root_.StatMech
open scoped NNReal

/-- The event "coordinate `i` is open" on two coordinates. -/
def openF (i : Fin 2) : Set (ConfigSpace (Fin 2)) := {ω | ω i = true}

-- `openF i` is increasing.
theorem isIncreasing_openF (i : Fin 2) : IsIncreasing (openF i) := by
  intro x y hxy hx
  have h := hxy i
  simp only [openF, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- A non-constant parameter on two coordinates. -/
noncomputable def p2 : Fin 2 → ℝ≥0 := ![1 / 3, 1 / 2]

-- Each `p2 e` is at most `1`.
theorem p2_le_one (e : Fin 2) : p2 e ≤ 1 := by
  fin_cases e
  · change (1 / 3 : ℝ≥0) ≤ 1
    exact div_le_one_of_le₀ (by norm_num) (by norm_num)
  · change (1 / 2 : ℝ≥0) ≤ 1
    exact div_le_one_of_le₀ (by norm_num) (by norm_num)

-- The inhomogeneous BK inequality with all hypotheses instantiated.
example : (inhomBernoulliProductMeasure p2 p2_le_one).real (disjointOccurrence (openF 0) (openF 1))
    ≤ (inhomBernoulliProductMeasure p2 p2_le_one).real (openF 0)
      * (inhomBernoulliProductMeasure p2 p2_le_one).real (openF 1) :=
  inhom_bk_inequality p2 p2_le_one (isIncreasing_openF 0) (isIncreasing_openF 1)

-- A constant parameter gives `bernoulliProductMeasure`.
example : inhomBernoulliProductMeasure (E := Fin 2) (fun _ => (1 / 2 : ℝ≥0)) (fun _ => by norm_num)
    = bernoulliProductMeasure (1 / 2) (by norm_num) :=
  inhomBernoulliProductMeasure_const _ _

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

/-- The parameter `p n = 1/(n+2)` on `ℕ`. -/
noncomputable def pN (n : ℕ) : ℝ≥0 := 1 / (n + 2)

-- Each `pN n` is at most `1`.
theorem pN_le_one (n : ℕ) : pN n ≤ 1 :=
  div_le_one_of_le₀ (by
    have : (1 : ℝ≥0) ≤ (n : ℝ≥0) + 2 := le_add_of_le_right (by norm_num)
    exact this) bot_le

-- The inhomogeneous BK inequality on `ℕ` for events depending on `{0, 1}`.
example : (inhomBernoulliProductMeasure pN pN_le_one).real
      (disjointOccurrence (openAt 0) (openAt 1))
    ≤ (inhomBernoulliProductMeasure pN pN_le_one).real (openAt 0)
      * (inhomBernoulliProductMeasure pN pN_le_one).real (openAt 1) :=
  inhom_bk_of_finite_dependsOn pN pN_le_one {0, 1} (dependsOn_openAt 0 (by simp))
    (dependsOn_openAt 1 (by simp)) (isIncreasing_openAt 0) (isIncreasing_openAt 1)

end MathlibExtTest.StatMech.Probability.Hypercontractivity.InhomogeneousProduct
