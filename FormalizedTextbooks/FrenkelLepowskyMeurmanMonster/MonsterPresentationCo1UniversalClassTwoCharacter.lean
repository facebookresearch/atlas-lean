/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The bounded actual source commutator has its canonical binary coefficient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoSquares

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The identity source commutator has coefficient zero; every other element has coefficient one. -/
def co1UniversalCommutatorCoefficient (c : commutator Co1UniversalPresentation) : ZMod 2 :=
  by
    classical
    exact if c = 1 then 0 else 1

/-- The canonical source coefficient vanishes precisely at the identity. -/
theorem co1UniversalCommutatorCoefficient_eq_zero (c : commutator Co1UniversalPresentation) :
    co1UniversalCommutatorCoefficient c = 0 ↔ c = 1 := by
  classical
  by_cases h : c = 1 <;> simp [co1UniversalCommutatorCoefficient, h]

/-- Under the explicit source bound, multiplication adds canonical binary coefficients. -/
theorem co1UniversalCommutatorCoefficient_mul
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (a b : commutator Co1UniversalPresentation) :
    co1UniversalCommutatorCoefficient (a * b) =
      co1UniversalCommutatorCoefficient a + co1UniversalCommutatorCoefficient b := by
  classical
  by_cases ha : a = 1
  · subst a
    simp [co1UniversalCommutatorCoefficient]
  by_cases hb : b = 1
  · subst b
    simp [co1UniversalCommutatorCoefficient]
  have hne : commutator Co1UniversalPresentation ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨a, ha⟩
  obtain ⟨z, hz, hu⟩ := co1Universal_commutator_unique_involution hfinite hcard hne
  have he : a = b :=
    (hu a ⟨ha, co1Universal_commutator_square_of_card_le_two hfinite hcard a⟩).trans
      (hu b ⟨hb, co1Universal_commutator_square_of_card_le_two hfinite hcard b⟩).symm
  subst b
  have hs : a * a = 1 := by
    simpa only [pow_two] using co1Universal_commutator_square_of_card_le_two hfinite hcard a
  rw [hs]
  simp only [co1UniversalCommutatorCoefficient, ha, ite_false, ite_true]
  exact (ZModModule.add_self (1 : ZMod 2)).symm

/-- The explicit finite bound makes the actual source coefficient a group homomorphism. -/
def co1UniversalCommutatorCharacter
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) :
    commutator Co1UniversalPresentation →* Multiplicative (ZMod 2) where
  toFun c := Multiplicative.ofAdd (co1UniversalCommutatorCoefficient c)
  map_one' := by simp [co1UniversalCommutatorCoefficient]
  map_mul' a b := congrArg Multiplicative.ofAdd
    (co1UniversalCommutatorCoefficient_mul hfinite hcard a b)

/-- The actual canonical character is faithful under the explicit source bound. -/
theorem co1UniversalCommutatorCharacter_injective
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) :
    Function.Injective (co1UniversalCommutatorCharacter hfinite hcard) := by
  apply (co1UniversalCommutatorCharacter hfinite hcard).ker_eq_bot_iff.mp
  ext c
  change (co1UniversalCommutatorCoefficient c = 0) ↔ c = 1
  exact co1UniversalCommutatorCoefficient_eq_zero c

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
