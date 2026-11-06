/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source squares depend only on the exact binary quotient under the explicit commutator bound. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoCenter

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The explicit source commutator bound makes squares independent
of the quotient representative. -/
theorem co1Universal_square_eq_of_binary_eq
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x y : Co1UniversalPresentation) (hxy : co1UniversalIntoBinary x = co1UniversalIntoBinary y) :
    x ^ 2 = y ^ 2 := by
  let c := x⁻¹ * y
  have hc : c ∈ commutator Co1UniversalPresentation := by
    rw [← co1UniversalIntoBinary_ker]
    change co1UniversalIntoBinary (x⁻¹ * y) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hz : c ∈ Subgroup.center Co1UniversalPresentation :=
    co1Universal_commutator_le_center_of_card_le_two hfinite hcard hc
  have hcomm : Commute x c := Subgroup.mem_center_iff.mp hz x
  have hs : c ^ 2 = 1 := congrArg Subtype.val
    (co1Universal_commutator_square_of_card_le_two hfinite hcard ⟨c, hc⟩)
  have he : y = x * c := by
    dsimp only [c]
    simp only [mul_inv_cancel_left]
  rw [he, hcomm.mul_pow, hs, mul_one]

/-- Choose a preimage of a genuine full binary coordinate under the original source quotient. -/
def co1UniversalBinaryLift (v : Fin 24 → ZMod 2) : Co1UniversalPresentation :=
  Classical.choose (co1UniversalIntoBinary_surjective (Multiplicative.ofAdd v))

/-- The chosen source preimage has exactly the prescribed actual binary coordinate. -/
theorem co1UniversalBinaryLift_image (v : Fin 24 → ZMod 2) :
    co1UniversalIntoBinary (co1UniversalBinaryLift v) = Multiplicative.ofAdd v :=
  Classical.choose_spec (co1UniversalIntoBinary_surjective (Multiplicative.ofAdd v))

/-- The source square is an actual element of the original commutator subgroup. -/
def co1UniversalBinarySquare (v : Fin 24 → ZMod 2) : commutator Co1UniversalPresentation :=
  ⟨co1UniversalBinaryLift v ^ 2, co1Universal_square_mem_commutator _⟩

/-- Under the explicit bound, every source square is the binary square of its actual coordinate. -/
theorem co1UniversalBinarySquare_image
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x : Co1UniversalPresentation) :
    (co1UniversalBinarySquare (co1UniversalIntoBinary x).toAdd).val = x ^ 2 := by
  apply co1Universal_square_eq_of_binary_eq hfinite hcard
  exact co1UniversalBinaryLift_image _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
