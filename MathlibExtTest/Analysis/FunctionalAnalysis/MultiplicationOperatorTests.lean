/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.MultiplicationOperator
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Order.IntermediateValue

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for multiplication operators on `C(X, 𝕜)`

* On `C(Fin 2, ℝ)`, the multiplier taking `0 ↦ 0`, `1 ↦ 1` has spectrum
  containing `0` and `1` but not `1 / 2`; `0` is an eigenvalue, `1 / 2`
  is not; the operator is not a unit.
* Multiplication by the constant `2` on `C(Fin 2, ℝ)` is a unit with
  operator norm `2`.
* On `C([0, 1], ℝ)`, the identity multiplier has spectrum `[0, 1]`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.FunctionalAnalysis.MultiplicationOperatorTests

open Set Filter Topology
open MathlibExt.Analysis.FunctionalAnalysis.MultiplicationOperator

/-- The multiplier `0 ↦ 0`, `1 ↦ 1` on `C(Fin 2, ℝ)`. -/
noncomputable def testPhi : C(Fin 2, ℝ) :=
  ⟨fun i => (i : ℝ), continuous_of_discreteTopology⟩

example : testPhi 0 = 0 := by simp [testPhi]

example : testPhi 1 = 1 := by simp [testPhi]

/-- `0` is in the spectrum. -/
example : (0 : ℝ) ∈ spectrum ℝ (mulCLM testPhi) := by
  rw [spectrum_mulCLM]
  exact ⟨0, by simp [testPhi]⟩

/-- `1` is in the spectrum. -/
example : (1 : ℝ) ∈ spectrum ℝ (mulCLM testPhi) := by
  rw [spectrum_mulCLM]
  exact ⟨1, by simp [testPhi]⟩

/-- `1 / 2` is not in the spectrum. -/
example : (1 / 2 : ℝ) ∉ spectrum ℝ (mulCLM testPhi) := by
  rw [spectrum_mulCLM]
  rintro ⟨i, hi⟩
  fin_cases i <;> simp [testPhi] at hi

/-- `0` is an eigenvalue: the multiplier is `0` on `{0}`, which is open. -/
example : Module.End.HasEigenvalue
    (mulCLM testPhi : C(Fin 2, ℝ) →ₗ[ℝ] C(Fin 2, ℝ)) 0 := by
  rw [hasEigenvalue_mulCLM_iff]
  have hpre : testPhi ⁻¹' {(0 : ℝ)} = {0} := by
    ext i
    fin_cases i <;> simp [testPhi]
  refine ⟨0, ?_⟩
  rw [hpre, (isOpen_discrete ({0} : Set (Fin 2))).interior_eq]
  exact Set.mem_singleton 0

/-- `1 / 2` is not an eigenvalue: the multiplier never takes that value. -/
example : ¬ Module.End.HasEigenvalue
    (mulCLM testPhi : C(Fin 2, ℝ) →ₗ[ℝ] C(Fin 2, ℝ)) (1 / 2) := by
  rw [hasEigenvalue_mulCLM_iff]
  intro h
  obtain ⟨x, hx⟩ := h
  have hpre : testPhi ⁻¹' {(1 / 2 : ℝ)} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro i hi
    fin_cases i <;> simp [testPhi] at hi
  rw [hpre, interior_empty] at hx
  exact hx

/-- The operator is not a unit: the multiplier vanishes at `0`. -/
example : ¬ IsUnit (mulCLM testPhi) := by
  rw [isUnit_mulCLM_iff]
  intro h
  exact h 0 (by simp [testPhi])

/-- Multiplication by the constant `2` is a unit. -/
example : IsUnit (mulCLM (ContinuousMap.const (Fin 2) (2 : ℝ))) := by
  rw [isUnit_mulCLM_iff]
  intro i
  simp

/-- Multiplication by the constant `2` has operator norm `2`. -/
example : ‖mulCLM (ContinuousMap.const (Fin 2) (2 : ℝ))‖ = 2 := by
  have hnorm : ‖mulCLM (ContinuousMap.const (Fin 2) (2 : ℝ))‖ =
      ‖ContinuousMap.const (Fin 2) (2 : ℝ)‖ :=
    ContinuousLinearMap.opNorm_mul_apply ℝ C(Fin 2, ℝ) _
  rw [hnorm]
  simp [ContinuousMap.norm_eq_iSup_norm]

/-- The identity multiplier on `C([0, 1], ℝ)` has spectrum `[0, 1]`. -/
example : spectrum ℝ (mulCLM (⟨Subtype.val, continuous_subtype_val⟩ :
    C(Set.Icc (0 : ℝ) 1, ℝ))) = Set.Icc 0 1 := by
  rw [spectrum_mulCLM]
  exact Subtype.range_val

/-- The attained midpoint lies in the spectrum, but its singleton fiber has empty
interior in the actual interval subtype and hence it is not an eigenvalue. -/
theorem interval_identity_midpoint_spectral_not_eigenvalue :
    let φ : C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
    (1 / 2 : ℝ) ∈ spectrum ℝ (mulCLM φ) ∧
      ¬ Module.End.HasEigenvalue
        (mulCLM φ : C(Set.Icc (0 : ℝ) 1, ℝ) →ₗ[ℝ] C(Set.Icc (0 : ℝ) 1, ℝ)) (1 / 2) := by
  intro φ
  let midpoint : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  have hfiber : φ ⁻¹' {(1 / 2 : ℝ)} = {midpoint} := by
    ext x
    change ((x : ℝ) = (1 / 2 : ℝ)) ↔ x = midpoint
    constructor
    · intro hx
      exact Subtype.ext hx
    · intro hx
      exact congrArg Subtype.val hx
  letI : ConnectedSpace (Set.Icc (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc (by norm_num))
  letI : Nontrivial (Set.Icc (0 : ℝ) 1) :=
    ⟨⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, by
      intro h
      have hval := congrArg Subtype.val h
      norm_num at hval⟩⟩
  constructor
  · rw [spectrum_mulCLM]
    exact ⟨midpoint, rfl⟩
  · rw [hasEigenvalue_mulCLM_iff, hfiber, interior_singleton]
    simp

end MathlibExtTest.Analysis.FunctionalAnalysis.MultiplicationOperatorTests
