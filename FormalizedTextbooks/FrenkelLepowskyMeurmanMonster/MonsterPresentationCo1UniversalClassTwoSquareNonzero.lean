/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A nontrivial bounded source commutator forces a nonzero actual-coordinate square function. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoCharacter

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The binary coefficient of the original source square at an actual binary coordinate. -/
def co1UniversalSquareCoefficient (v : Fin 24 → ZMod 2) : ZMod 2 :=
  co1UniversalCommutatorCoefficient (co1UniversalBinarySquare v)

/-- A zero square function would make every source element involutory and the source abelian. -/
theorem co1Universal_commutator_eq_bot_of_square_coefficient_zero
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hzero : ∀ v : Fin 24 → ZMod 2, co1UniversalSquareCoefficient v = 0) :
    commutator Co1UniversalPresentation = ⊥ := by
  have hs : ∀ x : Co1UniversalPresentation, x ^ 2 = 1 := by
    intro x
    have he : co1UniversalBinarySquare (co1UniversalIntoBinary x).toAdd = 1 :=
      (co1UniversalCommutatorCoefficient_eq_zero _).mp (hzero _)
    have hv := congrArg Subtype.val he
    rw [co1UniversalBinarySquare_image hfinite hcard x] at hv
    exact hv
  have hi (x : Co1UniversalPresentation) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs x)
  apply (commutator_eq_bot_iff_center_eq_top Co1UniversalPresentation).mpr
  apply le_antisymm le_top
  intro x _
  apply Subgroup.mem_center_iff.mpr
  intro g
  simpa only [hi (g * x), hi x, hi g] using (mul_inv_rev g x)

/-- The nontrivial bounded source case forces a genuinely nonzero square coefficient function. -/
theorem co1UniversalSquareCoefficient_nonzero
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    ∃ v : Fin 24 → ZMod 2, co1UniversalSquareCoefficient v ≠ 0 := by
  by_contra h
  push Not at h
  exact hne (co1Universal_commutator_eq_bot_of_square_coefficient_zero hfinite hcard h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
