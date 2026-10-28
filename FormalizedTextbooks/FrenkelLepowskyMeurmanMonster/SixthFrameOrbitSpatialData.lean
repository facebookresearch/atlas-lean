/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitGenerators

/-! Cleared physical matrices of the original words and the genuine sixth-axis matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The exact physical signed permutation numerators of the original monomial words. -/
def sixthFrameOrbitMonomialNumerator (k : Fin 16) : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if sixthFrameOrbitSpatialInput k i = j then sixthFrameOrbitSpatialSign k i else 0

/-- Cleared physical matrices of all fifteen original source words. -/
def sixthFrameOrbitSpatialNumerator (k : Fin 15) : Matrix (Fin 24) (Fin 24) ℤ :=
  if h : k.val < 14 then sixthFrameOrbitMonomialNumerator (Fin.castAdd 2 ⟨k.val, h⟩)
  else fun i j => co1XiNumerator (sixthFrameOrbitCForward i) (sixthFrameOrbitCForward j)

/-- Only the final original Xi word needs a physical denominator. -/
def sixthFrameOrbitSpatialDenominator (k : Fin 15) : ℤ := if k.val < 14 then 1 else 2

/-- Thirty-two times the actual original sixth-axis matrix in its source coordinate ordering. -/
def sixthFrameOrbitAxisNumerator : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if i = j then if i = 19 then 33 else if i = 16 ∨ i = 17 then 17 else 9
  else
    let a := if i < j then i else j
    let b := if i < j then j else i
    if a = 16 ∧ b = 17 then 4 else
      if (a = 16 ∧ b = 19) ∨ (a = 17 ∧ b = 19) then -12 else 0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
