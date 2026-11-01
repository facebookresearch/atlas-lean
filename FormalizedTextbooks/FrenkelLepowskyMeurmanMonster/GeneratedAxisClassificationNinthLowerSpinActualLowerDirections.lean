/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineLowerFiberActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! Actual Co1 action on the nine distinct whole Ninth direction spaces. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The nine previously source-bound destination system addresses are distinct. -/
theorem generatedNinth_lower_spin_actual_destination_injective :
    Function.Injective generatedNinthAffineTransportSystemIndex := by
  decide +kernel

/-- The nine entire actual direction spaces are distinct, using genuine source transport. -/
theorem generatedNinth_lower_spin_actual_direction_spaces_injective :
    Function.Injective generatedNinthAffineDirectionClassSpace := by
  intro i j h
  have ht := congrArg (fun W : Submodule (ZMod 2) LeechModTwo =>
    W.map (leechModTwoAction generatedNinthAffineTransport).toLinearMap) h
  rw [generatedNinth_affine_system_class_map,
    generatedNinth_affine_system_class_map] at ht
  exact generatedNinth_lower_spin_actual_destination_injective
    (generatedAxisE8ActualFrameSystemCandidate_injective ht)

/-- The faithful actual Co1 binary action in the intrinsic genuine lattice quotient. -/
def generatedNinthLowerSpinActualClassAction :
    Co1 →* (LeechModTwo ≃ₗ[ZMod 2] LeechModTwo) where
  toFun g := (leechHyperbolicCoordinates.trans (co1BinaryAction g)).trans
    leechHyperbolicCoordinates.symm
  map_one' := by
    apply LinearEquiv.ext
    intro x
    rw [map_one]
    exact leechHyperbolicCoordinates.symm_apply_apply x
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply]

/-- The intrinsic quotient action of each actual Co0 source is its original lattice action. -/
theorem generatedNinth_lower_spin_actual_class_action_source (e : leechIsomSubgroup) :
    generatedNinthLowerSpinActualClassAction (QuotientGroup.mk e) = leechModTwoAction e := by
  apply LinearEquiv.ext
  intro x
  apply leechHyperbolicCoordinates.injective
  change leechHyperbolicCoordinates
    (leechHyperbolicCoordinates.symm
      (leechBinaryAction e (leechHyperbolicCoordinates x))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact leechBinaryAction_coordinates e x

/-- Push a whole intrinsic submodule forward by the genuine Conway quotient action. -/
def generatedNinthLowerSpinActualClassMap (g : Co1)
    (W : Submodule (ZMod 2) LeechModTwo) : Submodule (ZMod 2) LeechModTwo :=
  W.map (generatedNinthLowerSpinActualClassAction g).toLinearMap

/-- Whole-submodule transport by the actual identity is the identity. -/
theorem generatedNinth_lower_spin_actual_class_map_one
    (W : Submodule (ZMod 2) LeechModTwo) :
    generatedNinthLowerSpinActualClassMap 1 W = W := by
  rw [generatedNinthLowerSpinActualClassMap, map_one]
  exact Submodule.map_id _

/-- Whole-submodule transport retains the exact group multiplication order. -/
theorem generatedNinth_lower_spin_actual_class_map_mul (g h : Co1)
    (W : Submodule (ZMod 2) LeechModTwo) :
    generatedNinthLowerSpinActualClassMap (g * h) W =
      generatedNinthLowerSpinActualClassMap g (generatedNinthLowerSpinActualClassMap h W) := by
  rw [generatedNinthLowerSpinActualClassMap, map_mul]
  change W.map ((generatedNinthLowerSpinActualClassAction g).toLinearMap.comp
    (generatedNinthLowerSpinActualClassAction h).toLinearMap) = _
  exact Submodule.map_comp _ _ _

/-- The eleven genuine source classes have their complete original whole-fiber permutations. -/
theorem generatedNinth_lower_spin_actual_class_map_generator (k : Fin 11) (i : Fin 9) :
    generatedNinthLowerSpinActualClassMap
      (QuotientGroup.mk (generatedNinthAffineLowerTransportedIsometry k))
        (generatedNinthAffineDirectionClassSpace i) =
      generatedNinthAffineDirectionClassSpace (generatedNinthAffineLowerFiberPermutation k i) := by
  rw [generatedNinthLowerSpinActualClassMap,
    generatedNinth_lower_spin_actual_class_action_source]
  exact generatedNinth_affine_lower_fiber_map k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
