/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineRootTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitFamilies

/-! Original binary coordinates transport each whole affine marking direction space to
an existing genuine selected-section frame system. The final nine-system set is an
existing actual960-parent-tree state, not an assumed catalogue spread. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Original four-coordinate labels of the transported affine source directions. -/
def generatedNinthAffineSystemCoefficientLabels : Fin 9 → Fin 4 → Fin 16 := ![
    ![14, 7, 15, 5],
    ![14, 6, 1, 11],
    ![13, 3, 4, 15],
    ![12, 5, 6, 11],
    ![12, 3, 4, 14],
    ![10, 4, 2, 9],
    ![10, 2, 5, 12],
    ![10, 5, 6, 8],
    ![9, 1, 2, 12]]

/-- The actual four-coordinate matrix into the specified original frame-system basis. -/
def generatedNinthAffineSystemCoefficientMatrix (i : Fin 9) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) := fun j k =>
  if (generatedNinthAffineSystemCoefficientLabels i k).val.testBit j.val then 1 else 0

/-- Complete original coordinates in the actual destination frame-system basis. -/
def generatedNinthAffineSystemCoefficientMap (i : Fin 9) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  Matrix.mulVecLin (generatedNinthAffineSystemCoefficientMatrix i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
-- Bind all36 actual source basis vectors through the original full binary transport.
/-- Every affine source basis vector has its actual original frame-system coordinates. -/
theorem generatedNinth_affine_system_transport_certificate : ∀ (i : Fin 9) (j : Fin 4),
    sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ
      (generatedNinthAffineDirectionMap i (Pi.single j 1)) =
        generatedFifthFrameBinaryMatrix *ᵥ
          (generatedAxisE8FrameSystemCandidateMap (generatedNinthAffineTransportSystemIndex i)
            (generatedNinthAffineSystemCoefficientMap i (Pi.single j 1))) := by
  decide +kernel

/-- Linearity retains the actual coordinate certificate on the entire source space. -/
theorem generatedNinth_affine_system_transport_binary (i : Fin 9) (a : Fin 4 → ZMod 2) :
    sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ
      (generatedNinthAffineDirectionMap i a) =
        generatedFifthFrameBinaryMatrix *ᵥ
          (generatedAxisE8FrameSystemCandidateMap (generatedNinthAffineTransportSystemIndex i)
            (generatedNinthAffineSystemCoefficientMap i a)) := by
  have h : (Matrix.mulVecLin
      (sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns)).comp
        (generatedNinthAffineDirectionMap i) =
      (Matrix.mulVecLin generatedFifthFrameBinaryMatrix).comp
        ((generatedAxisE8FrameSystemCandidateMap (generatedNinthAffineTransportSystemIndex i)).comp
          (generatedNinthAffineSystemCoefficientMap i)) := by
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro j
    simpa only [LinearMap.comp_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply] using
      generatedNinth_affine_system_transport_certificate i j
  exact LinearMap.congr_fun h a

/-- Every original affine direction has its genuine whole-lattice source-word transport. -/
theorem generatedNinth_affine_system_class_transport (i : Fin 9) (a : Fin 4 → ZMod 2) :
    leechModTwoAction generatedNinthAffineTransport (generatedNinthAffineDirectionClassMap i a) =
      generatedAxisE8FrameRootEmbedding
        (generatedAxisE8FrameSystemCandidateMap (generatedNinthAffineTransportSystemIndex i)
          (generatedNinthAffineSystemCoefficientMap i a)) := by
  apply leechHyperbolicCoordinates.injective
  rw [← leechBinaryAction_coordinates]
  change leechBinaryAction generatedNinthAffineTransport
      (leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _)) =
    leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    generatedNinth_affine_transport_binary_action]
  exact generatedNinth_affine_system_transport_binary i a

/-- The whole actual affine source space maps into its genuine destination frame system. -/
theorem generatedNinth_affine_system_class_map_le (i : Fin 9) :
    (generatedNinthAffineDirectionClassSpace i).map
      (leechModTwoAction generatedNinthAffineTransport).toLinearMap ≤
        generatedAxisE8ActualFrameSystemCandidate (generatedNinthAffineTransportSystemIndex i) := by
  rintro v ⟨u, ⟨a, rfl⟩, rfl⟩
  refine Submodule.mem_map.mpr ⟨generatedAxisE8FrameSystemCandidateMap
    (generatedNinthAffineTransportSystemIndex i) (generatedNinthAffineSystemCoefficientMap i a),
      ⟨generatedNinthAffineSystemCoefficientMap i a, rfl⟩, ?_⟩
  exact (generatedNinth_affine_system_class_transport i a).symm

/-- The whole actual sixteen-point affine direction space equals the destination frame system. -/
theorem generatedNinth_affine_system_class_map (i : Fin 9) :
    (generatedNinthAffineDirectionClassSpace i).map
      (leechModTwoAction generatedNinthAffineTransport).toLinearMap =
        generatedAxisE8ActualFrameSystemCandidate (generatedNinthAffineTransportSystemIndex i) := by
  let : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  apply SetLike.coe_injective
  apply generatedAxisE8FrameSystems_set_eq_of_subset_card
    _ _ (generatedNinth_affine_system_class_map_le i)
  have hc := Nat.card_congr (Submodule.equivMapOfInjective
    (leechModTwoAction generatedNinthAffineTransport).toLinearMap
    (leechModTwoAction generatedNinthAffineTransport).injective
    (generatedNinthAffineDirectionClassSpace i)).toEquiv
  exact hc.symm.trans ((generatedNinth_affine_direction_class_card i).trans
    (generatedAxisE8ActualFrameSystemCandidate_mem
      (generatedNinthAffineTransportSystemIndex i)).1.symm)

/-- The finite positions in the original sorted415th nine-system parent-tree state. -/
def generatedNinthAffineSpreadPosition : Fin 9 → Fin 9 := ![1, 5, 3, 4, 2, 0, 6, 8, 7]

/-- The nine positions exhaust the actual destination state without repetition. -/
theorem generatedNinth_affine_spread_position_bijective :
    Function.Bijective generatedNinthAffineSpreadPosition := by
  decide +kernel

set_option maxRecDepth 100000 in
-- The exact destination state is read from the original960-entry source tuple.
/-- All nine transported system indices are the genuine415th parent-tree state. -/
theorem generatedNinth_affine_spread_destination_coordinates : ∀ i : Fin 9,
    generatedNinthAffineTransportSystemIndex i =
      generatedNinthSpreadIndices 415 (generatedNinthAffineSpreadPosition i) := by
  decide +kernel

/-- All nine whole actual systems read directly from the existing original spread415 row. -/
def generatedNinthAffineDestinationCarrier : Finset (Submodule (ZMod 2) LeechModTwo) := by
  classical
  exact Finset.univ.image (fun j : Fin 9 =>
    generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadIndices 415 j))

/-- The transported actual system indices exhaust the genuine destination spread. -/
theorem generatedNinth_affine_spread_destination_range :
    Set.range (fun i => generatedAxisE8ActualFrameSystemCandidate
      (generatedNinthAffineTransportSystemIndex i)) =
        (generatedNinthAffineDestinationCarrier : Set (Submodule (ZMod 2) LeechModTwo)) := by
  classical
  ext W
  constructor
  · rintro ⟨i, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨generatedNinthAffineSpreadPosition i, Finset.mem_univ _, ?_⟩
    rw [← generatedNinth_affine_spread_destination_coordinates]
  · intro hW
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨i, hi⟩ := generatedNinth_affine_spread_position_bijective.2 j
    refine ⟨i, ?_⟩
    change generatedAxisE8ActualFrameSystemCandidate (generatedNinthAffineTransportSystemIndex i) =
      generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadIndices 415 j)
    rw [generatedNinth_affine_spread_destination_coordinates, hi]

/-- The entire nine-space family transports to the existing actual spread415. -/
theorem generatedNinth_affine_spread_family_transport :
    (fun W : Submodule (ZMod 2) LeechModTwo =>
      W.map (leechModTwoAction generatedNinthAffineTransport).toLinearMap) ''
        Set.range generatedNinthAffineDirectionClassSpace =
      (generatedNinthAffineDestinationCarrier : Set (Submodule (ZMod 2) LeechModTwo)) := by
  rw [← generatedNinth_affine_spread_destination_range]
  ext W
  constructor
  · rintro ⟨V, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (generatedNinth_affine_system_class_map i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨generatedNinthAffineDirectionClassSpace i, ⟨i, rfl⟩,
      generatedNinth_affine_system_class_map i⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
