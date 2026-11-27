/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellRotatedSquarePellShiftedNormBijOnIci

/-!
# Tests for the shifted Pell norm beyond its last crossing

The last crossing attains the bound, and every value above the bound has a unique preimage
on the closed ray starting at that crossing.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Lemma 3.7.
-/

namespace MathlibExtTest.NumberTheory.PellRotatedSquarePellShiftedNormBijOnIci

open MetaMathlibExt

example {D : ℤ} {w : Pell.Solution₁ D} (hw : Pell.IsFundamental w) (a b : ℤ)
    {i j : ℤ} (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1) :
    let x₁ : ℝ := sSup {y : ℝ | 0 ≤ y ∧
      pellShiftedNorm D w.x w.y a b i j y = pellShiftBound D a b}
    pellShiftedNorm D w.x w.y a b i j x₁ = pellShiftBound D a b := by
  intro x₁
  obtain ⟨_, hmono, hbij⟩ := pellShiftedNorm_bijOn_Ici hw a b hi hj
  obtain ⟨x, hx, hfx⟩ := hbij.surjOn (Set.mem_Ici.mpr le_rfl)
  have hlo := hbij.mapsTo (Set.mem_Ici.mpr (le_refl x₁))
  have hhi := hmono.monotoneOn (Set.mem_Ici.mpr (le_refl x₁)) hx hx
  exact le_antisymm (hhi.trans_eq hfx) hlo

example {D : ℤ} {w : Pell.Solution₁ D} (hw : Pell.IsFundamental w) (a b : ℤ)
    {i j : ℤ} (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1)
    {y : ℝ} (hy : pellShiftBound D a b ≤ y) :
    let x₁ : ℝ := sSup {z : ℝ | 0 ≤ z ∧
      pellShiftedNorm D w.x w.y a b i j z = pellShiftBound D a b}
    ∃! x, x₁ ≤ x ∧ pellShiftedNorm D w.x w.y a b i j x = y := by
  intro x₁
  have hbij := (pellShiftedNorm_bijOn_Ici hw a b hi hj).2.2
  obtain ⟨x, hx, hfx⟩ := hbij.surjOn hy
  refine ⟨x, ⟨hx, hfx⟩, ?_⟩
  intro z hz
  exact hbij.injOn hz.1 hx (hz.2.trans hfx.symm)

end MathlibExtTest.NumberTheory.PellRotatedSquarePellShiftedNormBijOnIci
