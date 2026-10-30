/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.LpMultiplicationOperator

import Mathlib.Tactic.FinCases

/-!
# Tests for multiplication operators on `L²`

* On `L²` of `Fin 2` with counting measure, the multiplier `![1, 3]` has
  spectrum `{1, 3}`; `1` is an eigenvalue, `2` is not.
* On `L²` of `Fin 1` with counting measure, multiplication by the constant `2`
  has spectrum `{2}`, operator norm `2`, and acts as scalar multiplication.
* On `L²` of `ℕ` with counting measure, multiplication by the constant `2` has
  spectrum `{2}`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.FunctionalAnalysis.LpMultiplicationOperatorTests

open Set Filter MeasureTheory Topology
open scoped ENNReal
open MathlibExt.Analysis.FunctionalAnalysis.LpMultiplicationOperator

/-- Counting measure gives the whole space positive measure. -/
theorem count_univ_ne_zero {α : Type*} [MeasurableSpace α] [Nonempty α] :
    (Measure.count : Measure α) univ ≠ 0 := by
  rw [Measure.count_univ]
  have hpos : 0 < ENat.card α := ENat.card_pos
  exact_mod_cast hpos.ne'

/-- Counting measure on a nonempty type is nonzero. -/
theorem count_ne_zero {α : Type*} [MeasurableSpace α] [Nonempty α] :
    (Measure.count : Measure α) ≠ 0 := by
  intro h
  exact count_univ_ne_zero (by rw [h]; simp)

/-- The multiplier `0 ↦ 1`, `1 ↦ 3` on `Fin 2`. -/
noncomputable def testPhi2 : Fin 2 → ℂ := ![1, 3]

/-- The multiplier `![1, 3]` is essentially bounded. -/
theorem testPhi2_memLp : MemLp testPhi2 ∞ (Measure.count : Measure (Fin 2)) := by
  simp [testPhi2]

/-- The range of the multiplier `![1, 3]` is `{1, 3}`. -/
theorem testPhi2_range : Set.range testPhi2 = {1, 3} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [testPhi2]
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨0, by simp [testPhi2]⟩
    · exact ⟨1, by simp [testPhi2]⟩

/-- The spectrum of the multiplication operator for `![1, 3]` is `{1, 3}`. -/
example : spectrum ℂ (lpMulCLM testPhi2 testPhi2_memLp) = {1, 3} := by
  rw [spectrum_lpMulCLM, essentialRange_count_eq_range, testPhi2_range]

/-- `1` is in the spectrum of the multiplication operator for `![1, 3]`. -/
example : (1 : ℂ) ∈ spectrum ℂ (lpMulCLM testPhi2 testPhi2_memLp) := by
  rw [spectrum_lpMulCLM, essentialRange_count_eq_range, testPhi2_range]
  simp

/-- `2` is not in the spectrum of the multiplication operator for `![1, 3]`. -/
example : (2 : ℂ) ∉ spectrum ℂ (lpMulCLM testPhi2 testPhi2_memLp) := by
  rw [spectrum_lpMulCLM, essentialRange_count_eq_range, testPhi2_range]
  simp

/-- `1` is an eigenvalue: the level set `{x | testPhi2 x = 1}` is `{0}`. -/
example : Module.End.HasEigenvalue
    (lpMulCLM testPhi2 testPhi2_memLp : Lp ℂ 2 (Measure.count : Measure (Fin 2)) →ₗ[ℂ]
      Lp ℂ 2 (Measure.count : Measure (Fin 2))) 1 := by
  rw [hasEigenvalue_lpMulCLM_iff]
  have hset : {x : Fin 2 | testPhi2 x = 1} = {0} := by
    ext i
    fin_cases i <;> simp [testPhi2]
  rw [hset, Measure.count_singleton]
  exact one_pos

/-- `2` is not an eigenvalue: the multiplier never takes the value `2`. -/
example : ¬ Module.End.HasEigenvalue
    (lpMulCLM testPhi2 testPhi2_memLp : Lp ℂ 2 (Measure.count : Measure (Fin 2)) →ₗ[ℂ]
      Lp ℂ 2 (Measure.count : Measure (Fin 2))) 2 := by
  rw [hasEigenvalue_lpMulCLM_iff]
  have hset : {x : Fin 2 | testPhi2 x = 2} = ∅ := by
    ext i
    fin_cases i <;> simp [testPhi2]
  rw [hset, MeasureTheory.measure_empty]
  exact lt_irrefl 0

/-- Multiplication by the constant `2` on `L² (Fin 1)` has spectrum `{2}`. -/
example : spectrum ℂ (lpMulCLM (μ := Measure.count) (fun _ : Fin 1 => (2 : ℂ))
    (memLp_const_top (μ := Measure.count) (2 : ℂ))) = {2} := by
  rw [spectrum_lpMulCLM, essentialRange_const count_univ_ne_zero]

/-- Multiplication by the constant `2` on `L² (Fin 1)` has operator norm `2`. -/
example : ‖lpMulCLM (μ := Measure.count) (fun _ : Fin 1 => (2 : ℂ))
    (memLp_const_top (μ := Measure.count) (2 : ℂ))‖ = 2 := by
  rw [norm_lpMulCLM, eLpNorm_exponent_top aestronglyMeasurable_const,
    eLpNormEssSup_const _ count_ne_zero]
  simp

/-- Multiplication by the constant `2` on `L² (Fin 1)` is scalar multiplication. -/
example (f : Lp ℂ 2 (Measure.count : Measure (Fin 1))) :
    lpMulCLM (μ := Measure.count) (fun _ : Fin 1 => (2 : ℂ))
      (memLp_const_top (μ := Measure.count) (2 : ℂ)) f = (2 : ℂ) • f :=
  lpMulCLM_const_apply 2 f

/-- Multiplication by the constant `2` on `L² (ℕ)` has spectrum `{2}`. -/
example : spectrum ℂ (lpMulCLM (μ := Measure.count) (fun _ : ℕ => (2 : ℂ))
    (memLp_const_top (μ := Measure.count) (2 : ℂ))) = {2} := by
  rw [spectrum_lpMulCLM, essentialRange_const count_univ_ne_zero]

end MathlibExtTest.Analysis.FunctionalAnalysis.LpMultiplicationOperatorTests
