/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Nondegeneracy identifies the original source center with its bounded nontrivial commutator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoPolar

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- Under the explicit nontrivial bound, a central source element has zero actual binary image. -/
theorem co1UniversalIntoBinary_eq_one_of_center
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥)
    (x : Co1UniversalPresentation) (hx : x ∈ Subgroup.center Co1UniversalPresentation) :
    co1UniversalIntoBinary x = 1 := by
  have hv : (co1UniversalIntoBinary x).toAdd = 0 := by
    apply co1UniversalCommutatorPairing_nondegenerate hfinite hcard hne
    intro w
    have hc : co1UniversalCommutator x (co1UniversalBinaryLift w) = 1 := by
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hx _).symm
    have hi := co1UniversalBinaryCommutator_image hfinite hcard x (co1UniversalBinaryLift w)
    rw [co1UniversalBinaryLift_image] at hi
    change co1UniversalBinaryCommutator (co1UniversalIntoBinary x).toAdd w =
      co1UniversalCommutator x (co1UniversalBinaryLift w) at hi
    change co1UniversalCommutatorCoefficient
      (co1UniversalBinaryCommutator (co1UniversalIntoBinary x).toAdd w) = 0
    rw [hi, hc]
    exact (co1UniversalCommutatorCoefficient_eq_zero 1).mpr rfl
  exact congrArg Multiplicative.ofAdd hv

/-- The nontrivial bounded original source commutator is its entire center. -/
theorem co1Universal_center_eq_commutator
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) :
    Subgroup.center Co1UniversalPresentation = commutator Co1UniversalPresentation := by
  apply le_antisymm
  · intro x hx
    rw [← co1UniversalIntoBinary_ker]
    exact co1UniversalIntoBinary_eq_one_of_center hfinite hcard hne x hx
  · exact co1Universal_commutator_le_center_of_card_le_two hfinite hcard

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
