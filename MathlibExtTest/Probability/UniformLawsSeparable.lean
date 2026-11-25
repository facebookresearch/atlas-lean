/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.UniformLawsSeparable

/-!
# Tests for sup functionals over pointwise separable classes

Threshold classes instantiate the measurability theorems; the constant
(zero) class checks that every functional evaluates to zero on a closed
sample; `#print axioms` audits each of the nine production theorems.
-/

open MeasureTheory Filter Topology

namespace MathlibExt.Probability.UniformLawsWanted

/-- Each threshold function is measurable. -/
theorem threshold_measurable (t : ℝ) :
    Measurable (fun z : ℝ => if z ≤ t then (1 : ℝ) else 0) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_Iic

/-- Threshold values lie in `[0, 1]`. -/
theorem threshold_mem_Icc (t z : ℝ) :
    (if z ≤ t then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hz : z ≤ t
  · rw [ite_eq_left hz]
    exact Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩
  · rw [ite_eq_right hz]
    exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩

/-- Threshold class at sample size one has measurable uniform deviation. -/
example : Measurable (uniformDeviation (Measure.dirac (0 : ℝ))
    (fun t : ℝ => fun z : ℝ => if z ≤ t then (1 : ℝ) else 0)
    (n := 1) le_rfl) :=
  measurable_uniformDeviation_of_pointwiseSeparable
    (fun t => threshold_measurable t)
    (fun t z => threshold_mem_Icc t z)
    pointwiseSeparable_threshold le_rfl

/-- Threshold class at sample size one has measurable empirical Rademacher
sup. -/
example : Measurable (empRademacher
    (fun t : ℝ => fun z : ℝ => if z ≤ t then (1 : ℝ) else 0)
    (n := 1) (fun _ => true)) :=
  measurable_empRademacher_of_pointwiseSeparable
    (fun t => threshold_measurable t)
    (fun t z => threshold_mem_Icc t z)
    pointwiseSeparable_threshold (fun _ => true)

/-- Threshold class at sample size one has measurable swapped ghost sums. -/
example : Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
    swappedGhost (fun t : ℝ => fun z : ℝ => if z ≤ t then (1 : ℝ) else 0)
      (n := 1) (fun _ => true) p.1 p.2) :=
  measurable_swappedGhost_of_pointwiseSeparable
    (fun t => threshold_measurable t)
    (fun t z => threshold_mem_Icc t z)
    pointwiseSeparable_threshold (fun _ => true)

/-- The constant zero class is measurable. -/
theorem const_measurable : ∀ _ : Fin 2, Measurable (fun _ : ℝ => (0 : ℝ)) :=
  fun _ => measurable_const

/-- The constant zero class is `[0, 1]`-valued. -/
theorem const_mem_Icc : ∀ _ : Fin 2, ∀ _ : ℝ, (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
  fun _ _ => Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩

/-- The constant zero class is trivially pointwise dense in itself. -/
theorem const_dense : ∀ _ : Fin 2, ∃ seq : ℕ → Fin 2,
    (∀ m, seq m ∈ Set.univ) ∧
    ∀ _ : ℝ, Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
  fun _ => ⟨fun _ => 0, fun _ => Set.mem_univ _, fun _ => tendsto_const_nhds⟩

/-- Ghost deviation of the constant class is zero, via its equality. -/
example (x x' : Fin 2 → ℝ) :
    ghostDeviation (fun _ : Fin 2 => fun _ : ℝ => (0 : ℝ)) x x' = 0 := by
  rw [ghostDeviation_eq_subclass const_mem_Icc const_dense x x']
  simp [ghostDeviation]

/-- Swapped ghost sums of the constant class are zero, via their equality. -/
example (t : Fin 2 → Bool) (x x' : Fin 2 → ℝ) :
    swappedGhost (fun _ : Fin 2 => fun _ : ℝ => (0 : ℝ)) t x x' = 0 := by
  rw [swappedGhost_eq_subclass const_mem_Icc const_dense t x x']
  simp [swappedGhost]

/-- Empirical Rademacher sup of the constant class is zero, via its
equality. -/
example (t : Fin 2 → Bool) (x : Fin 2 → ℝ) :
    empRademacher (fun _ : Fin 2 => fun _ : ℝ => (0 : ℝ)) t x = 0 := by
  rw [empRademacher_eq_subclass const_mem_Icc const_dense t x]
  simp [empRademacher]

/-- Uniform deviation of the constant class is zero at a closed sample. -/
example (x : Fin 2 → ℝ) :
    uniformDeviation (Measure.dirac (0 : ℝ))
      (fun _ : Fin 2 => fun _ : ℝ => (0 : ℝ)) (n := 2) (by norm_num) x = 0 := by
  simp [uniformDeviation]

/-- The uniform deviation equality applies to the constant class. -/
example (x : Fin 2 → ℝ) :
    uniformDeviation (Measure.dirac (0 : ℝ))
      (fun _ : Fin 2 => fun _ : ℝ => (0 : ℝ)) (n := 2) (by norm_num) x =
      uniformDeviation (Measure.dirac (0 : ℝ))
        (fun _ : ↥(Set.univ : Set (Fin 2)) => fun _ : ℝ => (0 : ℝ))
        (n := 2) (by norm_num) x :=
  uniformDeviation_eq_subclass (n := 2) const_measurable const_mem_Icc const_dense (by norm_num) x

/-- The two-valued class is `[0, 1]`-valued. -/
theorem twoVal_mem_Icc : ∀ i : Fin 3, ∀ _ : ℝ,
    (if i = 1 then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
  intro i _
  by_cases hi : i = 1
  · rw [ite_eq_left hi]
    exact Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩
  · rw [ite_eq_right hi]
    exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩

/-- The two-valued class is dense in its `{0, 1}` subclass. -/
theorem twoVal_dense : ∀ i : Fin 3, ∃ seq : ℕ → Fin 3,
    (∀ m, seq m ∈ ({0, 1} : Set (Fin 3))) ∧
    ∀ _ : ℝ, Tendsto (fun m => (if seq m = 1 then (1 : ℝ) else 0))
      atTop (𝓝 (if i = 1 then (1 : ℝ) else 0)) := by
  intro i
  by_cases hi : i = 1
  · refine ⟨fun _ => 1, fun _ => by simp, fun _ => ?_⟩
    rw [ite_eq_left hi]
    exact tendsto_const_nhds
  · refine ⟨fun _ => 0, fun _ => by simp, fun _ => ?_⟩
    rw [ite_eq_right hi]
    exact tendsto_const_nhds

/-- Empirical Rademacher sup of the two-valued class is one, via its
equality over the `{0, 1}` subclass. -/
example : empRademacher (fun i : Fin 3 => fun _ : ℝ => if i = 1 then (1 : ℝ) else 0)
    (fun _ : Fin 1 => true) (fun _ : Fin 1 => (0 : ℝ)) = 1 := by
  rw [empRademacher_eq_subclass twoVal_mem_Icc twoVal_dense _ _]
  simp only [empRademacher]
  have hne : Nonempty ↥(({0, 1} : Set (Fin 3))) := ⟨⟨1, by simp⟩⟩
  apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro j
    by_cases hj : (↑j : Fin 3) = 1 <;> simp [hj]
  · intro w hw
    have hmem1 : (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by simp
    refine ⟨⟨1, hmem1⟩, ?_⟩
    simp
    exact hw

/-- The off-subclass singleton computes to the smaller value zero. -/
example : empRademacher
    (fun j : ↥(({2} : Set (Fin 3))) => fun _ : ℝ => if (↑j : Fin 3) = 1 then (1 : ℝ) else 0)
    (fun _ : Fin 1 => true) (fun _ : Fin 1 => (0 : ℝ)) = 0 := by
  simp only [empRademacher]
  have hne : Nonempty ↥(({2} : Set (Fin 3))) := ⟨⟨2, by simp⟩⟩
  apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro j
    have hj2 : (↑j : Fin 3) = 2 := Set.mem_singleton_iff.mp j.2
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simp [hj2, h21]
  · intro w hw
    have hmem2 : (2 : Fin 3) ∈ ({2} : Set (Fin 3)) := by simp
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    refine ⟨⟨2, hmem2⟩, ?_⟩
    simp [h21]
    exact hw

/-- Empirical Rademacher sup of the threshold class at the boundary
threshold, with the sample equal to the threshold. -/
example : empRademacher
    (fun j : ↥(({0} : Set ℝ)) => fun z : ℝ => if z ≤ (↑j : ℝ) then (1 : ℝ) else 0)
    (fun _ : Fin 1 => true) (fun _ : Fin 1 => (0 : ℝ)) = 1 := by
  simp only [empRademacher]
  have hne : Nonempty ↥(({0} : Set ℝ)) := ⟨⟨0, by simp⟩⟩
  apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro j
    have hj0 : (↑j : ℝ) = 0 := Set.mem_singleton_iff.mp j.2
    simp [hj0]
  · intro w hw
    have hmem0 : (0 : ℝ) ∈ ({0} : Set ℝ) := by simp
    refine ⟨⟨0, hmem0⟩, ?_⟩
    simp
    exact hw

#print axioms uniformDeviation_eq_subclass
#print axioms ghostDeviation_eq_subclass
#print axioms swappedGhost_eq_subclass
#print axioms empRademacher_eq_subclass
#print axioms measurable_uniformDeviation_of_pointwiseSeparable
#print axioms measurable_ghostDeviation_of_pointwiseSeparable
#print axioms measurable_empRademacher_of_pointwiseSeparable
#print axioms measurable_swappedGhost_of_pointwiseSeparable
#print axioms pointwiseSeparable_threshold

end UniformLawsWanted

end Probability

end MathlibExt
