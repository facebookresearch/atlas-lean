/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.Monoidal.Closed.CoefficientShuffleNaturality
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Focused clients of coefficient-shuffle naturality

In `Type` with its cartesian symmetric structure the coefficient shuffle
`M ⊗ (A ⊗ H) ⟶ A ⊗ (M ⊗ H)` sends `(m, (a, h))` to `(a, (m, h))`. The two naturality equations
are checked on elements with non-identity maps whose effect is visible: `succ` on the middle
coefficient factor and `(· * 3)` on the input factor. A negative guard shows the shuffle is not
the identity reassociation.
-/

open CategoryTheory MonoidalCategory

namespace MathlibExtTest.CategoryTheory.Monoidal.CoefficientShuffleFocusedClients

/-- `succ` as a morphism of `Type`. -/
def succH : ℕ ⟶ ℕ := TypeCat.ofHom Nat.succ

/-- `h ↦ 3 * h` as a morphism of `Type`. -/
def tripleH : ℕ ⟶ ℕ := TypeCat.ofHom fun x => 3 * x

/-- The shuffle on elements. -/
theorem map_apply (m : ℤ) (a : ℕ) (h : Bool) :
    CoefficientShuffle.map (V := Type) ℤ ℕ Bool ((m, (a, h)) : ℤ ⊗ (ℕ ⊗ Bool)) =
      ((a, (m, h)) : ℕ ⊗ (ℤ ⊗ Bool)) := rfl

/-- The coefficient factor moves past the middle factor: the shuffle is not a reassociation. -/
theorem map_moves_coefficient :
    CoefficientShuffle.map (V := Type) ℕ ℕ ℕ ((1, (2, 3)) : ℕ ⊗ (ℕ ⊗ ℕ)) ≠
      ((1, (2, 3)) : ℕ ⊗ (ℕ ⊗ ℕ)) := by
  rw [show CoefficientShuffle.map (V := Type) ℕ ℕ ℕ ((1, (2, 3)) : ℕ ⊗ (ℕ ⊗ ℕ)) =
    ((2, (1, 3)) : ℕ ⊗ (ℕ ⊗ ℕ)) from rfl]
  intro h
  exact absurd (congrArg Prod.fst h) (by decide)

/-- Naturality in the middle factor, evaluated: both sides send `(m, (a, h))` to
`(a + 1, (m, h))`. -/
theorem naturality_second_apply (m : ℤ) (a : ℕ) (h : Bool) :
    ((ℤ ◁ (succH ▷ Bool)) ≫ CoefficientShuffle.map (V := Type) ℤ ℕ Bool)
        ((m, (a, h)) : ℤ ⊗ (ℕ ⊗ Bool)) = ((a + 1, (m, h)) : ℕ ⊗ (ℤ ⊗ Bool)) ∧
      (CoefficientShuffle.map (V := Type) ℤ ℕ Bool ≫ (succH ▷ (ℤ ⊗ Bool)))
        ((m, (a, h)) : ℤ ⊗ (ℕ ⊗ Bool)) = ((a + 1, (m, h)) : ℕ ⊗ (ℤ ⊗ Bool)) :=
  ⟨rfl, rfl⟩

theorem naturality_second_types :
    (ℤ ◁ (succH ▷ Bool)) ≫ CoefficientShuffle.map (V := Type) ℤ ℕ Bool =
      CoefficientShuffle.map (V := Type) ℤ ℕ Bool ≫ (succH ▷ (ℤ ⊗ Bool)) :=
  CoefficientShuffle.naturality_second ℤ succH Bool

/-- Naturality in the input factor, evaluated with `h ↦ 3 * h`. -/
theorem naturality_third_apply (m : ℤ) (a : Bool) (h : ℕ) :
    ((ℤ ◁ (Bool ◁ tripleH)) ≫
        CoefficientShuffle.map (V := Type) ℤ Bool ℕ) ((m, (a, h)) : ℤ ⊗ (Bool ⊗ ℕ)) =
      ((a, (m, 3 * h)) : Bool ⊗ (ℤ ⊗ ℕ)) := rfl

theorem naturality_third_types :
    (ℤ ◁ (Bool ◁ tripleH)) ≫
        CoefficientShuffle.map (V := Type) ℤ Bool ℕ =
      CoefficientShuffle.map (V := Type) ℤ Bool ℕ ≫
        (Bool ◁ (ℤ ◁ tripleH)) :=
  CoefficientShuffle.naturality_third ℤ Bool tripleH

end MathlibExtTest.CategoryTheory.Monoidal.CoefficientShuffleFocusedClients
