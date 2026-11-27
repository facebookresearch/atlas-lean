/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellRotatedSquarePellShiftedNormBijOnIci
import MathlibExt.NumberTheory.PellShiftedNormBeforeCrossing
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Endpoint tests for the shifted Pell norm bound -/

namespace MathlibExtTest.NumberTheory.PellShiftedNormBeforeCrossing

open MetaMathlibExt

private def w : Pell.Solution₁ 3 := .mk 2 1 (by decide)

private theorem hw : Pell.IsFundamental w :=
  ⟨by decide, by decide, fun {_} hb => hb⟩

-- At zero, test a negative first shifted coordinate and, separately,
-- a negative second shifted coordinate with a square-root-dominated bound.
example : pellShiftedNorm 3 w.x w.y 2 0 (-1) 1 0 ≤ pellShiftBound 3 2 0 :=
  pellShiftedNorm_le_pellShiftBound hw 2 0 (Or.inr rfl) (Or.inl rfl) le_rfl
    (Real.sSup_nonneg fun _ hy => hy.1)

example : pellShiftedNorm 3 w.x w.y 0 4 1 (-1) 0 ≤ pellShiftBound 3 0 4 :=
  pellShiftedNorm_le_pellShiftBound hw 0 4 (Or.inl rfl) (Or.inr rfl) le_rfl
    (Real.sSup_nonneg fun _ hy => hy.1)

-- For this shift `(u(1), v(1)) = (2, 1)` gives `f(1) = K = 3`.
example : pellShiftedNorm 3 w.x w.y (-1) 1 1 1 1 ≤ pellShiftBound 3 (-1) 1 := by
  let f := pellShiftedNorm 3 w.x w.y (-1) 1 1 1
  let K := pellShiftBound 3 (-1) 1
  let x₁ : ℝ := sSup {y : ℝ | 0 ≤ y ∧ f y = K}
  have hu : pellU 3 w.x w.y 1 = 2 := by
    change pellU 3 2 1 1 = 2
    norm_num [pellU]
  have hv : pellV 3 w.x w.y 1 = 1 := by
    change pellV 3 2 1 1 = 1
    norm_num [pellV]
    field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]
    ring
  have hEq : f 1 = K := by
    dsimp only [f, K, pellShiftedNorm, pellShiftBound]
    norm_num [hu, hv]
  have hx₁ : 1 ≤ x₁ := by
    by_contra! h
    obtain ⟨_, hmono, hbij⟩ := pellShiftedNorm_bijOn_Ici hw (-1) 1 (Or.inl rfl) (Or.inl rfl)
    have hmem : x₁ ∈ Set.Ici x₁ := le_rfl
    have hlt : f x₁ < f 1 := hmono hmem h.le h
    have hlo : K ≤ f x₁ := hbij.mapsTo hmem
    exact (hlo.trans_lt hlt).ne hEq.symm
  exact pellShiftedNorm_le_pellShiftBound hw (-1) 1 (Or.inl rfl) (Or.inl rfl) zero_le_one hx₁

end MathlibExtTest.NumberTheory.PellShiftedNormBeforeCrossing
