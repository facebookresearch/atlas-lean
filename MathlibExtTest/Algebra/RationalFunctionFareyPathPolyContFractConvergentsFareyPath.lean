/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.RationalFunctionFareyPathPolyContFractConvergentsFareyPath

namespace MathlibExtTest.Algebra.RationalFunctionFareyPathPolyContFractConvergentsFareyPath

open MetaMathlibExt Polynomial

-- The constant sequence `X` gives a first convergent in lowest terms with unit determinant.
example : ∃ A B : ℕ → ℚ[X], B 1 ≠ 0 ∧ IsCoprime (A 1) (B 1) ∧
    IsUnit (A 1 * B 0 - A 0 * B 1) := by
  obtain ⟨A, B, h⟩ := polyContFract_convergents_farey_path (fun _ => (X : ℚ[X])) 2
    (fun i _ _ => by simp)
  obtain ⟨-, -, hB, hC, hU⟩ := h 1 (by decide)
  exact ⟨A, B, hB, hC, hU le_rfl⟩

-- A length-zero continued fraction has nonzero denominator and coprime zeroth convergent.
example (a0 : ℚ[X]) : ∃ A B : ℕ → ℚ[X], B 0 ≠ 0 ∧ IsCoprime (A 0) (B 0) := by
  obtain ⟨A, B, h⟩ := polyContFract_convergents_farey_path (fun _ => a0) 0
    (fun i _ hi => absurd hi (by omega))
  obtain ⟨-, -, hB, hC, -⟩ := h 0 le_rfl
  exact ⟨A, B, hB, hC⟩

end MathlibExtTest.Algebra.RationalFunctionFareyPathPolyContFractConvergentsFareyPath
