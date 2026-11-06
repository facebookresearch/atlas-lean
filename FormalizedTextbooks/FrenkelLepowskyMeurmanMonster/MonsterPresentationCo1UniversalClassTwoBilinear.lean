/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual source commutator induces a bilinear form on its exact binary quotient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoCommutators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoCharacter
public import Mathlib.LinearAlgebra.BilinearForm.Basic

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source commutator evaluated on chosen preimages of actual binary coordinates. -/
def co1UniversalBinaryCommutator (v w : Fin 24 → ZMod 2) :
    commutator Co1UniversalPresentation :=
  co1UniversalCommutator (co1UniversalBinaryLift v) (co1UniversalBinaryLift w)

/-- Under the explicit bound, every source commutator is the commutator of its binary images. -/
theorem co1UniversalBinaryCommutator_image
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (x y : Co1UniversalPresentation) :
    co1UniversalBinaryCommutator (co1UniversalIntoBinary x).toAdd
      (co1UniversalIntoBinary y).toAdd = co1UniversalCommutator x y := by
  calc
    _ = co1UniversalCommutator x
        (co1UniversalBinaryLift (co1UniversalIntoBinary y).toAdd) :=
      co1UniversalCommutator_eq_of_binary_eq_left hfinite hcard _ _ _
        (co1UniversalBinaryLift_image _)
    _ = co1UniversalCommutator x y :=
      co1UniversalCommutator_eq_of_binary_eq_right hfinite hcard _ _ _
        (co1UniversalBinaryLift_image _)

/-- The actual binary coefficient of the original source commutator. -/
def co1UniversalCommutatorPairing (v w : Fin 24 → ZMod 2) : ZMod 2 :=
  co1UniversalCommutatorCoefficient (co1UniversalBinaryCommutator v w)

/-- The source commutator coefficient is additive in its first binary argument. -/
theorem co1UniversalCommutatorPairing_add_left
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (v w t : Fin 24 → ZMod 2) :
    co1UniversalCommutatorPairing (v + w) t =
      co1UniversalCommutatorPairing v t + co1UniversalCommutatorPairing w t := by
  have he := co1UniversalBinaryCommutator_image hfinite hcard
    (co1UniversalBinaryLift v * co1UniversalBinaryLift w) (co1UniversalBinaryLift t)
  rw [map_mul, co1UniversalBinaryLift_image, co1UniversalBinaryLift_image,
    co1UniversalBinaryLift_image] at he
  change co1UniversalBinaryCommutator (v + w) t =
    co1UniversalCommutator (co1UniversalBinaryLift v * co1UniversalBinaryLift w)
      (co1UniversalBinaryLift t) at he
  change co1UniversalCommutatorCoefficient (co1UniversalBinaryCommutator (v + w) t) = _
  rw [he, co1UniversalCommutator_mul_left hfinite hcard,
    co1UniversalCommutatorCoefficient_mul hfinite hcard]
  exact add_comm _ _

/-- The source commutator coefficient is additive in its second binary argument. -/
theorem co1UniversalCommutatorPairing_add_right
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (v w t : Fin 24 → ZMod 2) :
    co1UniversalCommutatorPairing v (w + t) =
      co1UniversalCommutatorPairing v w + co1UniversalCommutatorPairing v t := by
  have he := co1UniversalBinaryCommutator_image hfinite hcard
    (co1UniversalBinaryLift v) (co1UniversalBinaryLift w * co1UniversalBinaryLift t)
  rw [map_mul, co1UniversalBinaryLift_image, co1UniversalBinaryLift_image,
    co1UniversalBinaryLift_image] at he
  change co1UniversalBinaryCommutator v (w + t) =
    co1UniversalCommutator (co1UniversalBinaryLift v)
      (co1UniversalBinaryLift w * co1UniversalBinaryLift t) at he
  change co1UniversalCommutatorCoefficient (co1UniversalBinaryCommutator v (w + t)) = _
  rw [he, co1UniversalCommutator_mul_right hfinite hcard,
    co1UniversalCommutatorCoefficient_mul hfinite hcard]
  rfl

/-- The actual source commutator pairing vanishes on a zero first binary argument. -/
theorem co1UniversalCommutatorPairing_zero_left
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) (v : Fin 24 → ZMod 2) :
    co1UniversalCommutatorPairing 0 v = 0 := by
  simpa only [zero_add, ZModModule.add_self] using
    co1UniversalCommutatorPairing_add_left hfinite hcard 0 0 v

/-- The actual source commutator pairing vanishes on a zero second binary argument. -/
theorem co1UniversalCommutatorPairing_zero_right
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) (v : Fin 24 → ZMod 2) :
    co1UniversalCommutatorPairing v 0 = 0 := by
  simpa only [zero_add, ZModModule.add_self] using
    co1UniversalCommutatorPairing_add_right hfinite hcard v 0 0

/-- The first source pairing argument respects actual binary scalars. -/
theorem co1UniversalCommutatorPairing_smul_left
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (a : ZMod 2) (v w : Fin 24 → ZMod 2) :
    co1UniversalCommutatorPairing (a • v) w = a • co1UniversalCommutatorPairing v w := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases h a with ha | ha
  · simp only [ha, zero_smul, co1UniversalCommutatorPairing_zero_left hfinite hcard]
  · simp only [ha, one_smul]

/-- The second source pairing argument respects actual binary scalars. -/
theorem co1UniversalCommutatorPairing_smul_right
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (a : ZMod 2) (v w : Fin 24 → ZMod 2) :
    co1UniversalCommutatorPairing v (a • w) = a • co1UniversalCommutatorPairing v w := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases h a with ha | ha
  · simp only [ha, zero_smul, co1UniversalCommutatorPairing_zero_right hfinite hcard]
  · simp only [ha, one_smul]

/-- The actual source commutator defines a genuine bilinear form on the actual binary module. -/
def co1UniversalCommutatorBilin
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2) :
    LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) co1UniversalCommutatorPairing
    (co1UniversalCommutatorPairing_add_left hfinite hcard)
    (co1UniversalCommutatorPairing_smul_left hfinite hcard)
    (co1UniversalCommutatorPairing_add_right hfinite hcard)
    (co1UniversalCommutatorPairing_smul_right hfinite hcard)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
