/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineLowerFiberData

/-! Whole fiber actions of the eleven source isometries transported to the actual Ninth axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Linearity retains the exact full source coordinate certificate on the entire fiber. -/
theorem generatedNinth_affine_lower_fiber_binary (k : Fin 11) (i : Fin 9)
    (a : Fin 4 → ZMod 2) :
    sixthFrameOrbitColumnMatrix (generatedNinthAffineLowerSourceColumns k) *ᵥ
      (sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ
        generatedNinthAffineDirectionMap i a) =
      sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ
        generatedNinthAffineDirectionMap (generatedNinthAffineLowerFiberPermutation k i)
          (generatedNinthAffineLowerFiberCoefficientMap k i a) := by
  have h : (Matrix.mulVecLin
      (sixthFrameOrbitColumnMatrix (generatedNinthAffineLowerSourceColumns k))).comp
        ((Matrix.mulVecLin
          (sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns)).comp
            (generatedNinthAffineDirectionMap i)) =
      (Matrix.mulVecLin
        (sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns)).comp
          ((generatedNinthAffineDirectionMap (generatedNinthAffineLowerFiberPermutation k i)).comp
            (generatedNinthAffineLowerFiberCoefficientMap k i)) := by
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro j
    simpa only [LinearMap.comp_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply] using
      generatedNinth_affine_lower_fiber_coordinate_certificate k i j
  exact LinearMap.congr_fun h a

/-- The complete genuine original source action retains the entire transported fiber formula. -/
theorem generatedNinth_affine_lower_fiber_class_source (k : Fin 11) (i : Fin 9)
    (a : Fin 4 → ZMod 2) :
    leechModTwoAction (generatedNinthAffineLowerSourceIsometry k)
      (leechModTwoAction generatedNinthAffineTransport
        (generatedNinthAffineDirectionClassMap i a)) =
      leechModTwoAction generatedNinthAffineTransport
        (generatedNinthAffineDirectionClassMap (generatedNinthAffineLowerFiberPermutation k i)
          (generatedNinthAffineLowerFiberCoefficientMap k i a)) := by
  apply leechHyperbolicCoordinates.injective
  rw [← leechBinaryAction_coordinates, ← leechBinaryAction_coordinates,
    ← leechBinaryAction_coordinates, generatedNinth_affine_lower_source_binary,
    generatedNinth_affine_transport_binary_action, generatedNinth_affine_transport_binary_action]
  change sixthFrameOrbitColumnMatrix (generatedNinthAffineLowerSourceColumns k) *ᵥ
      (sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ
        (leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _))) =
    sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ
      (leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact generatedNinth_affine_lower_fiber_binary k i a

/-- The complete original lower source word transported back to the actual Ninth coordinates. -/
def generatedNinthAffineLowerTransportedIsometry (k : Fin 11) : leechIsomSubgroup :=
  generatedNinthAffineTransport⁻¹ * generatedNinthAffineLowerSourceIsometry k *
    generatedNinthAffineTransport

/-- The actual transported source word acts on every vector of its stated whole fiber. -/
theorem generatedNinth_affine_lower_fiber_class (k : Fin 11) (i : Fin 9)
    (a : Fin 4 → ZMod 2) :
    leechModTwoAction (generatedNinthAffineLowerTransportedIsometry k)
        (generatedNinthAffineDirectionClassMap i a) =
      generatedNinthAffineDirectionClassMap (generatedNinthAffineLowerFiberPermutation k i)
        (generatedNinthAffineLowerFiberCoefficientMap k i a) := by
  rw [generatedNinthAffineLowerTransportedIsometry, map_mul, map_mul, map_inv]
  change (leechModTwoAction generatedNinthAffineTransport).symm
      (leechModTwoAction (generatedNinthAffineLowerSourceIsometry k)
        (leechModTwoAction generatedNinthAffineTransport
          (generatedNinthAffineDirectionClassMap i a))) = _
  rw [generatedNinth_affine_lower_fiber_class_source, LinearEquiv.symm_apply_apply]

/-- The entire genuine transported fiber is contained in its stated actual image fiber. -/
theorem generatedNinth_affine_lower_fiber_map_le (k : Fin 11) (i : Fin 9) :
    (generatedNinthAffineDirectionClassSpace i).map
      (leechModTwoAction (generatedNinthAffineLowerTransportedIsometry k)).toLinearMap ≤
        generatedNinthAffineDirectionClassSpace
          (generatedNinthAffineLowerFiberPermutation k i) := by
  rintro v ⟨u, ⟨a, rfl⟩, rfl⟩
  refine ⟨generatedNinthAffineLowerFiberCoefficientMap k i a, ?_⟩
  exact (generatedNinth_affine_lower_fiber_class k i a).symm

/-- Every full genuine transported fiber equals the stated actual image fiber. -/
theorem generatedNinth_affine_lower_fiber_map (k : Fin 11) (i : Fin 9) :
    (generatedNinthAffineDirectionClassSpace i).map
      (leechModTwoAction (generatedNinthAffineLowerTransportedIsometry k)).toLinearMap =
        generatedNinthAffineDirectionClassSpace
          (generatedNinthAffineLowerFiberPermutation k i) := by
  let : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  apply SetLike.coe_injective
  apply generatedAxisE8FrameSystems_set_eq_of_subset_card
    _ _ (generatedNinth_affine_lower_fiber_map_le k i)
  have hc := Nat.card_congr (Submodule.equivMapOfInjective
    (leechModTwoAction (generatedNinthAffineLowerTransportedIsometry k)).toLinearMap
    (leechModTwoAction (generatedNinthAffineLowerTransportedIsometry k)).injective
    (generatedNinthAffineDirectionClassSpace i)).toEquiv
  exact hc.symm.trans ((generatedNinth_affine_direction_class_card i).trans
    (generatedNinth_affine_direction_class_card
      (generatedNinthAffineLowerFiberPermutation k i)).symm)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
