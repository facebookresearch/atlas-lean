/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The original source square function is invariant under the exact existing Conway action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoSquareNonzero

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Source square values intertwine the exact original Conway source automorphisms. -/
theorem co1UniversalBinarySquare_action
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (g : Co1) (v : Fin 24 → ZMod 2) :
    (co1UniversalBinarySquare (co1BinaryAction g v)).val =
      co1UniversalRepresentation g (co1UniversalBinarySquare v).val := by
  have hv : (co1UniversalIntoBinary (co1UniversalRepresentation g
      (co1UniversalBinaryLift v))).toAdd = co1BinaryAction g v := by
    rw [co1UniversalIntoBinary_action, co1UniversalBinaryLift_image]
    rfl
  have he := co1UniversalBinarySquare_image hfinite hcard
    (co1UniversalRepresentation g (co1UniversalBinaryLift v))
  rw [hv] at he
  change (co1UniversalBinarySquare (co1BinaryAction g v)).val =
    co1UniversalRepresentation g (co1UniversalBinaryLift v ^ 2)
  rw [map_pow]
  exact he

/-- The actual-coordinate source square coefficient is invariant
under every actual Conway element. -/
theorem co1UniversalSquareCoefficient_action
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (g : Co1) (v : Fin 24 → ZMod 2) :
    co1UniversalSquareCoefficient (co1BinaryAction g v) = co1UniversalSquareCoefficient v := by
  have hid : co1UniversalBinarySquare (co1BinaryAction g v) = 1 ↔
      co1UniversalBinarySquare v = 1 := by
    rw [Subtype.ext_iff, Subtype.ext_iff]
    change (co1UniversalBinarySquare (co1BinaryAction g v)).val = 1 ↔
      (co1UniversalBinarySquare v).val = 1
    rw [co1UniversalBinarySquare_action hfinite hcard]
    exact (co1UniversalRepresentation g).map_eq_one_iff
  classical
  by_cases hv : co1UniversalBinarySquare v = 1
  · have hg := hid.mpr hv
    simp only [co1UniversalSquareCoefficient, co1UniversalCommutatorCoefficient,
      hg, hv, ite_true]
  · have hg : co1UniversalBinarySquare (co1BinaryAction g v) ≠ 1 :=
      fun h => hv (hid.mp h)
    simp only [co1UniversalSquareCoefficient, co1UniversalCommutatorCoefficient,
      hg, hv, ite_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
