/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.RationalFunctionFareyPathPolyContFractExtendFareyPath
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

namespace MathlibExtTest.Algebra.RationalFunctionFareyPathPolyContFractExtendFareyPath

open MetaMathlibExt Polynomial

private noncomputable def testPart : ℕ → ℚ[X]
  | 0 => 0
  | 1 => X
  | _ => 0

private noncomputable def testNum : ℕ → ℚ[X]
  | 0 => 0
  | 1 => 1
  | _ => 0

private noncomputable def testDen : ℕ → ℚ[X]
  | 0 => 1
  | 1 => X
  | _ => 0

-- The fraction X / (X^2 - 1) extends the continued fraction [0; X].
example : ∃ b : ℚ[X], 0 < b.natDegree ∧
    (polyContFract (Function.update testPart 2 b) 2).convs 2 =
      algebraMap ℚ[X] (RatFunc ℚ) X / algebraMap ℚ[X] (RatFunc ℚ) (X ^ 2 - 1) := by
  have ha : ∀ i, 1 ≤ i → i ≤ 1 → 0 < (testPart i).natDegree := by
    intro i hi hin
    interval_cases i
    simp [testPart]
  have hA : ∀ i ≤ 1, (polyContFract testPart 1).nums i =
      algebraMap ℚ[X] (RatFunc ℚ) (testNum i) := by
    intro i hi
    interval_cases i
    · rw [polyContFract_nums_zero]
      simp [testPart, testNum]
    · rw [polyContFract_nums_one testPart zero_lt_one]
      simp [testPart, testNum]
  have hB : ∀ i ≤ 1, (polyContFract testPart 1).dens i =
      algebraMap ℚ[X] (RatFunc ℚ) (testDen i) := by
    intro i hi
    interval_cases i
    · rw [polyContFract_dens_zero]
      simp [testDen]
    · rw [polyContFract_dens_one testPart zero_lt_one]
      simp [testPart, testDen]
  have hadj : IsUnit (X * testDen 1 - (X ^ 2 - 1) * testNum 1 : ℚ[X]) := by
    have h : (X * testDen 1 - (X ^ 2 - 1) * testNum 1 : ℚ[X]) = 1 := by
      simp [testDen, testNum]
      ring
    rw [h]
    exact isUnit_one
  have hdeg : (testDen 1).degree < (X ^ 2 - 1 : ℚ[X]).degree := by
    have h1 : (testDen 1).degree = 1 := by
      simp only [testDen]
      compute_degree!
    have h2 : (X ^ 2 - 1 : ℚ[X]).degree = 2 := by
      compute_degree!
    rw [h1, h2]
    decide
  obtain ⟨b, hb_pos, _, hconv⟩ := polyContFract_extend_farey_path testPart
    le_rfl ha testNum testDen hA hB X (X ^ 2 - 1) hadj hdeg
  exact ⟨b, hb_pos, hconv⟩

end MathlibExtTest.Algebra.RationalFunctionFareyPathPolyContFractExtendFareyPath
