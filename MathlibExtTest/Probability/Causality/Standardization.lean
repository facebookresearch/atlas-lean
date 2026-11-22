/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.Standardization
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic.FinCases

/-! Examples for `MathlibExt.Probability.Causality.Standardization` with exact values: unequal
treatment propensities `1/4` and `3/4` in two covariate cells, the treated arm, the control arm
and the ATE, and a covariate value of probability zero whose term vanishes. -/

@[expose] public section

namespace MathlibExtTest.Probability.Causality.Standardization

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality

open scoped ENNReal

/-- Uniform probability measure on `Fin 8`. -/
noncomputable def testMu : Measure (Fin 8) := (8 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure testMu := ⟨by
  have hcount : Measure.count (Set.univ : Set (Fin 8)) = 8 := by
    rw [← Finset.coe_univ, Measure.count_apply_finset]
    simp
  unfold testMu
  rw [Measure.smul_apply, smul_eq_mul, hcount]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
⟩

/-- Three-valued covariate: `0` on `{0, 1, 2, 3}`, `1` on `{4, 5, 6, 7}`, `2` never taken. -/
def testX : Fin 8 → Fin 3 := fun ω => if ω.val < 4 then 0 else 1

/-- Treated event with propensity `1 / 4` in cell `0` and `3 / 4` in cell `1`. -/
def testT : Set (Fin 8) := {0, 4, 5, 6}

/-- Treated potential outcome as a function of the covariate. -/
def testG1 : Fin 3 → ℝ := fun x => if x = 0 then 10 else if x = 1 then 20 else 0

/-- Control potential outcome as a function of the covariate. -/
def testG0 : Fin 3 → ℝ := fun x => if x = 0 then 1 else if x = 1 then 2 else 0

/-- Treated potential outcome. -/
def testY1 : Fin 8 → ℝ := testG1 ∘ testX

/-- Control potential outcome. -/
def testY0 : Fin 8 → ℝ := testG0 ∘ testX

/-- A function of `X` is conditionally independent of any event given `X`. -/
theorem condIndepDiscrete_of_comp {Ω 𝒳 β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {μ : Measure Ω} {T : Set Ω} {X : Ω → 𝒳} {g : 𝒳 → β} :
    CondIndepDiscrete μ T (g ∘ X) X := by
  intro B _ w
  by_cases hB : g w ∈ B
  · have e1 : T ∩ (g ∘ X) ⁻¹' B ∩ X ⁻¹' {w} = T ∩ X ⁻¹' {w} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨hT, -⟩, hX⟩
        exact ⟨hT, hX⟩
      · rintro ⟨hT, hX⟩
        have hB' : g (X ω) ∈ B := by rw [hX]; exact hB
        exact ⟨⟨hT, hB'⟩, hX⟩
    have e2 : (g ∘ X) ⁻¹' B ∩ X ⁻¹' {w} = X ⁻¹' {w} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, hX⟩
        exact hX
      · intro hX
        have hB' : g (X ω) ∈ B := by rw [hX]; exact hB
        exact ⟨hB', hX⟩
    rw [e1, e2]
  · have e1 : T ∩ (g ∘ X) ⁻¹' B ∩ X ⁻¹' {w} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply,
        Set.mem_singleton_iff, Set.notMem_empty, iff_false]
      rintro ⟨⟨-, hgB⟩, hX⟩
      rw [hX] at hgB
      exact hB hgB
    have e2 : (g ∘ X) ⁻¹' B ∩ X ⁻¹' {w} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply,
        Set.mem_singleton_iff, Set.notMem_empty, iff_false]
      rintro ⟨hgB, hX⟩
      rw [hX] at hgB
      exact hB hgB
    rw [e1, e2]
    simp

/-- Each singleton has measure `1 / 8`. -/
theorem testMu_single (a : Fin 8) : testMu.real {a} = 1 / 8 := by
  have h : testMu {a} = (8 : ℝ≥0∞)⁻¹ := by
    unfold testMu
    rw [Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
  unfold Measure.real
  rw [h]
  norm_num [ENNReal.toReal_inv]

/-- The `0` cell is `{0, 1, 2, 3}`. -/
theorem testX_zero : testX ⁻¹' {0} = (((({0} ∪ {1}) ∪ {2}) ∪ {3}) : Set (Fin 8)) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union]
  constructor <;> fin_cases ω <;> decide

/-- The `1` cell is `{4, 5, 6, 7}`. -/
theorem testX_one : testX ⁻¹' {1} = (((({4} ∪ {5}) ∪ {6}) ∪ {7}) : Set (Fin 8)) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union]
  constructor <;> fin_cases ω <;> decide

/-- The `2` cell is empty. -/
theorem testX_two : testX ⁻¹' {2} = (∅ : Set (Fin 8)) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.notMem_empty, iff_false]
  fin_cases ω <;> decide

/-- Treated units in the `0` cell. -/
theorem testTA_zero : testT ∩ testX ⁻¹' {0} = ({0} : Set (Fin 8)) := by
  show ({0, 4, 5, 6} : Set (Fin 8)) ∩ testX ⁻¹' {0} = {0}
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor <;> fin_cases ω <;> decide

/-- Treated units in the `1` cell. -/
theorem testTA_one : testT ∩ testX ⁻¹' {1} = ((({4} ∪ {5}) ∪ {6}) : Set (Fin 8)) := by
  show ({0, 4, 5, 6} : Set (Fin 8)) ∩ testX ⁻¹' {1} = ((({4} ∪ {5}) ∪ {6}) : Set (Fin 8))
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_insert_iff, Set.mem_union]
  constructor <;> fin_cases ω <;> decide

/-- Disjointness of distinct singletons, `0` vs `1`. -/
theorem testDisj01 : Disjoint ({0} : Set (Fin 8)) {1} := by
  rw [Set.disjoint_left]
  rintro ω h1 h2
  simp only [Set.mem_singleton_iff] at h1 h2
  rw [h1] at h2
  revert h2
  decide

/-- Disjointness of `{0, 1}` vs `2`. -/
theorem testDisj012 : Disjoint (({0} ∪ {1} : Set (Fin 8))) {2} := by
  rw [Set.disjoint_left]
  rintro ω h1 h2
  simp only [Set.mem_union, Set.mem_singleton_iff] at h1 h2
  fin_cases ω <;> simp_all

/-- Disjointness of `{0, 1, 2}` vs `3`. -/
theorem testDisj0123 : Disjoint ((({0} ∪ {1}) ∪ {2} : Set (Fin 8))) {3} := by
  rw [Set.disjoint_left]
  rintro ω h1 h2
  simp only [Set.mem_union, Set.mem_singleton_iff] at h1 h2
  fin_cases ω <;> simp_all

/-- Disjointness of distinct singletons, `4` vs `5`. -/
theorem testDisj45 : Disjoint ({4} : Set (Fin 8)) {5} := by
  rw [Set.disjoint_left]
  rintro ω h1 h2
  simp only [Set.mem_singleton_iff] at h1 h2
  rw [h1] at h2
  revert h2
  decide

/-- Disjointness of `{4, 5}` vs `6`. -/
theorem testDisj456 : Disjoint (({4} ∪ {5} : Set (Fin 8))) {6} := by
  rw [Set.disjoint_left]
  rintro ω h1 h2
  simp only [Set.mem_union, Set.mem_singleton_iff] at h1 h2
  fin_cases ω <;> simp_all

/-- Disjointness of `{4, 5, 6}` vs `7`. -/
theorem testDisj4567 : Disjoint ((({4} ∪ {5}) ∪ {6} : Set (Fin 8))) {7} := by
  rw [Set.disjoint_left]
  rintro ω h1 h2
  simp only [Set.mem_union, Set.mem_singleton_iff] at h1 h2
  fin_cases ω <;> simp_all

/-- Measure of the `0` cell. -/
theorem testMu_zero : testMu.real (testX ⁻¹' {0}) = 1 / 2 := by
  rw [testX_zero, measureReal_union testDisj0123 (measurableSet_singleton 3),
    measureReal_union testDisj012 (measurableSet_singleton 2),
    measureReal_union testDisj01 (measurableSet_singleton 1)]
  simp only [testMu_single]
  norm_num

/-- Measure of the `1` cell. -/
theorem testMu_one : testMu.real (testX ⁻¹' {1}) = 1 / 2 := by
  rw [testX_one, measureReal_union testDisj4567 (measurableSet_singleton 7),
    measureReal_union testDisj456 (measurableSet_singleton 6),
    measureReal_union testDisj45 (measurableSet_singleton 5)]
  simp only [testMu_single]
  norm_num

/-- Measure of the empty `2` cell. -/
theorem testMu_two : testMu.real (testX ⁻¹' {2}) = 0 := by
  rw [testX_two]
  simp

/-- Measure of treated units in the `0` cell. -/
theorem testMu_TA_zero : testMu.real (testT ∩ testX ⁻¹' {0}) = 1 / 8 := by
  rw [testTA_zero]
  exact testMu_single 0

/-- Measure of treated units in the `1` cell. -/
theorem testMu_TA_one : testMu.real (testT ∩ testX ⁻¹' {1}) = 3 / 8 := by
  rw [testTA_one, measureReal_union testDisj456 (measurableSet_singleton 6),
    measureReal_union testDisj45 (measurableSet_singleton 5)]
  simp only [testMu_single]
  norm_num

/-- Propensity in cell `0` is `1 / 4`. -/
theorem testProp_zero : propensity testMu testT testX 0 = 1 / 4 := by
  unfold propensity
  rw [testMu_TA_zero, testMu_zero]
  norm_num

/-- Propensity in cell `1` is `3 / 4`. -/
theorem testProp_one : propensity testMu testT testX 1 = 3 / 4 := by
  unfold propensity
  rw [testMu_TA_one, testMu_one]
  norm_num

/-- Overlap holds with unequal propensities `1 / 4` and `3 / 4`. -/
theorem testOverlap (w : Fin 3) (hw : testMu (testX ⁻¹' {w}) ≠ 0) :
    0 < propensity testMu testT testX w ∧ propensity testMu testT testX w < 1 := by
  fin_cases w
  · show 0 < propensity testMu testT testX 0 ∧ propensity testMu testT testX 0 < 1
    rw [testProp_zero]
    norm_num
  · show 0 < propensity testMu testT testX 1 ∧ propensity testMu testT testX 1 < 1
    rw [testProp_one]
    norm_num
  · have hw2 : testMu (testX ⁻¹' {2}) ≠ 0 := hw
    rw [testX_two] at hw2
    simp at hw2

/-- Strong ignorability holds in the test model (treated arm). -/
theorem testSI1 : StronglyIgnorable testMu testT testY1 testX :=
  ⟨condIndepDiscrete_of_comp (μ := testMu) (T := testT) (X := testX) (g := testG1),
    testOverlap⟩

/-- Strong ignorability holds in the test model (control arm). -/
theorem testSI0 : StronglyIgnorable testMu testT testY0 testX :=
  ⟨condIndepDiscrete_of_comp (μ := testMu) (T := testT) (X := testX) (g := testG0),
    testOverlap⟩

/-- Strong ignorability holds for the pair `(Y₀, Y₁)`. -/
theorem testSIpair : StronglyIgnorable testMu testT (fun ω => (testY0 ω, testY1 ω)) testX := by
  have heq : (fun ω => (testY0 ω, testY1 ω)) =
      (fun x => (testG0 x, testG1 x)) ∘ testX := rfl
  rw [heq]
  exact ⟨condIndepDiscrete_of_comp (μ := testMu) (T := testT) (X := testX)
    (g := fun x => (testG0 x, testG1 x)), testOverlap⟩

/-- The test model is non-vacuous: `E[Y₁] = 15`. -/
theorem testMu_Y1 : ∫ ω, testY1 ω ∂testMu = 15 := by
  have hY1i : Integrable testY1 testMu :=
    integrableOn_univ.1 (IntegrableOn.of_finite (Set.toFinite _))
  have tx0 : testX 0 = 0 := by decide
  have tx1 : testX 1 = 0 := by decide
  have tx2 : testX 2 = 0 := by decide
  have tx3 : testX 3 = 0 := by decide
  have tx4 : testX 4 = 1 := by decide
  have tx5 : testX 5 = 1 := by decide
  have tx6 : testX 6 = 1 := by decide
  have tx7 : testX 7 = 1 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have y0 : testY1 0 = 10 := by simp [testY1, tx0, testG1]
  have y1 : testY1 1 = 10 := by simp [testY1, tx1, testG1]
  have y2 : testY1 2 = 10 := by simp [testY1, tx2, testG1]
  have y3 : testY1 3 = 10 := by simp [testY1, tx3, testG1]
  have y4 : testY1 4 = 20 := by simp [testY1, tx4, testG1, h10]
  have y5 : testY1 5 = 20 := by simp [testY1, tx5, testG1, h10]
  have y6 : testY1 6 = 20 := by simp [testY1, tx6, testG1, h10]
  have y7 : testY1 7 = 20 := by simp [testY1, tx7, testG1, h10]
  rw [integral_fintype hY1i]
  simp only [testMu_single, smul_eq_mul]
  rw [Fin.sum_univ_eight, y0, y1, y2, y3, y4, y5, y6, y7]
  norm_num

/-- The test model is non-vacuous: `E[Y₀] = 3 / 2`. -/
theorem testMu_Y0 : ∫ ω, testY0 ω ∂testMu = 3 / 2 := by
  have hY0i : Integrable testY0 testMu :=
    integrableOn_univ.1 (IntegrableOn.of_finite (Set.toFinite _))
  have tx0 : testX 0 = 0 := by decide
  have tx1 : testX 1 = 0 := by decide
  have tx2 : testX 2 = 0 := by decide
  have tx3 : testX 3 = 0 := by decide
  have tx4 : testX 4 = 1 := by decide
  have tx5 : testX 5 = 1 := by decide
  have tx6 : testX 6 = 1 := by decide
  have tx7 : testX 7 = 1 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have y0 : testY0 0 = 1 := by simp [testY0, tx0, testG0]
  have y1 : testY0 1 = 1 := by simp [testY0, tx1, testG0]
  have y2 : testY0 2 = 1 := by simp [testY0, tx2, testG0]
  have y3 : testY0 3 = 1 := by simp [testY0, tx3, testG0]
  have y4 : testY0 4 = 2 := by simp [testY0, tx4, testG0, h10]
  have y5 : testY0 5 = 2 := by simp [testY0, tx5, testG0, h10]
  have y6 : testY0 6 = 2 := by simp [testY0, tx6, testG0, h10]
  have y7 : testY0 7 = 2 := by simp [testY0, tx7, testG0, h10]
  rw [integral_fintype hY0i]
  simp only [testMu_single, smul_eq_mul]
  rw [Fin.sum_univ_eight, y0, y1, y2, y3, y4, y5, y6, y7]
  norm_num

/-- The ATE in the test model is `27 / 2`. -/
theorem testMu_sub : ∫ ω, (testY1 ω - testY0 ω) ∂testMu = 27 / 2 := by
  have hY0i : Integrable testY0 testMu :=
    integrableOn_univ.1 (IntegrableOn.of_finite (Set.toFinite _))
  have hY1i : Integrable testY1 testMu :=
    integrableOn_univ.1 (IntegrableOn.of_finite (Set.toFinite _))
  rw [integral_sub hY1i hY0i, testMu_Y1, testMu_Y0]
  norm_num

/-- The zero-probability value contributes `0` (treated arm). -/
theorem testZero_treated : testMu.real (testX ⁻¹' {2}) *
    ∫ ω, observed testT testY0 testY1 ω ∂testMu[|testT ∩ testX ⁻¹' {2}] = 0 := by
  rw [testMu_two, zero_mul]

/-- The zero-probability value contributes `0` (control arm). -/
theorem testZero_control : testMu.real (testX ⁻¹' {2}) *
    ∫ ω, observed testT testY0 testY1 ω ∂testMu[|testTᶜ ∩ testX ⁻¹' {2}] = 0 := by
  rw [testMu_two, zero_mul]

/-- The zero-probability value contributes `0` (ATE). -/
theorem testZero_ate : testMu.real (testX ⁻¹' {2}) *
    (∫ ω, observed testT testY0 testY1 ω ∂testMu[|testT ∩ testX ⁻¹' {2}] -
      ∫ ω, observed testT testY0 testY1 ω ∂testMu[|testTᶜ ∩ testX ⁻¹' {2}]) = 0 := by
  rw [testMu_two, zero_mul]

example : StronglyIgnorable testMu testT testY1 testX := testSI1

example : StronglyIgnorable testMu testT testY0 testX := testSI0

example : StronglyIgnorable testMu testT (fun ω => (testY0 ω, testY1 ω)) testX := testSIpair

example : (∑ x, testMu.real (testX ⁻¹' {x}) *
    ∫ ω, observed testT testY0 testY1 ω ∂testMu[|testT ∩ testX ⁻¹' {x}]) = 15 := by
  have hT : MeasurableSet testT := MeasurableSet.of_discrete
  have hX : Measurable testX := Measurable.of_discrete
  have hY1 : Measurable testY1 := Measurable.of_discrete
  have hY1i : Integrable testY1 testMu :=
    integrableOn_univ.1 (IntegrableOn.of_finite (Set.toFinite _))
  have hid : ∫ ω, testY1 ω ∂testMu =
      (∑ x, testMu.real (testX ⁻¹' {x}) *
        ∫ ω, observed testT testY0 testY1 ω ∂testMu[|testT ∩ testX ⁻¹' {x}]) :=
    integral_eq_sum_standardized_treated hT hX hY1 hY1i testSI1
  rw [← hid]
  exact testMu_Y1

example : (∑ x, testMu.real (testX ⁻¹' {x}) *
    ∫ ω, observed testT testY0 testY1 ω ∂testMu[|testTᶜ ∩ testX ⁻¹' {x}]) = 3 / 2 := by
  have hT : MeasurableSet testT := MeasurableSet.of_discrete
  have hX : Measurable testX := Measurable.of_discrete
  have hY0 : Measurable testY0 := Measurable.of_discrete
  have hY0i : Integrable testY0 testMu :=
    integrableOn_univ.1 (IntegrableOn.of_finite (Set.toFinite _))
  have hid : ∫ ω, testY0 ω ∂testMu =
      (∑ x, testMu.real (testX ⁻¹' {x}) *
        ∫ ω, observed testT testY0 testY1 ω ∂testMu[|testTᶜ ∩ testX ⁻¹' {x}]) :=
    integral_eq_sum_standardized_control hT hX hY0 hY0i testSI0
  rw [← hid]
  exact testMu_Y0

example : (∑ x, testMu.real (testX ⁻¹' {x}) *
    (∫ ω, observed testT testY0 testY1 ω ∂testMu[|testT ∩ testX ⁻¹' {x}] -
      ∫ ω, observed testT testY0 testY1 ω ∂testMu[|testTᶜ ∩ testX ⁻¹' {x}])) = 27 / 2 := by
  have hT : MeasurableSet testT := MeasurableSet.of_discrete
  have hX : Measurable testX := Measurable.of_discrete
  have hY0 : Measurable testY0 := Measurable.of_discrete
  have hY1 : Measurable testY1 := Measurable.of_discrete
  have hY0i : Integrable testY0 testMu :=
    integrableOn_univ.1 (IntegrableOn.of_finite (Set.toFinite _))
  have hY1i : Integrable testY1 testMu :=
    integrableOn_univ.1 (IntegrableOn.of_finite (Set.toFinite _))
  have hid : ∫ ω, (testY1 ω - testY0 ω) ∂testMu =
      (∑ x, testMu.real (testX ⁻¹' {x}) *
        (∫ ω, observed testT testY0 testY1 ω ∂testMu[|testT ∩ testX ⁻¹' {x}] -
          ∫ ω, observed testT testY0 testY1 ω ∂testMu[|testTᶜ ∩ testX ⁻¹' {x}])) :=
    integral_sub_eq_sum_standardized hT hX hY0 hY1 hY0i hY1i testSIpair
  rw [← hid]
  exact testMu_sub

end MathlibExtTest.Probability.Causality.Standardization
