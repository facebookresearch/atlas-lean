/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual local lifts match the centralizer's recognized spatial action. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerShortRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual local image has its proved inclusion in the actual full centralizer. -/
noncomputable def generatedLocalIntoCentralizer : H →* generatedCentralizer :=
  localIntoGenerated.codRestrict generatedCentralizer
    (fun h => localIntoGenerated_range_le_generatedCentralizer ⟨h, rfl⟩)

/-- Every actual Leech isometry has a compatible spin lift in the constructed fiber product. -/
theorem generatedCentral_localFiber_lift (e : leechIsomSubgroup) :
    ∃ f : localFiberSubgroup, f.val.2 = e := by
  let a := qBinaryIsometryLift (leechBinaryAction e) (leechBinaryAction_squareQuad e)
  obtain ⟨s, hs⟩ := exists_spinHolomorph_lift a
    (qBinaryIsometryLift_central (leechBinaryAction e) (leechBinaryAction_squareQuad e))
  have hf : (s, e) ∈ localFiberSubgroup := by
    change qBinaryAction (spinConjugation s) = leechBinaryAction e
    rw [hs]
    exact qBinaryAction_isometryLift (leechBinaryAction e) (leechBinaryAction_squareQuad e)
  exact ⟨⟨(s, e), hf⟩, rfl⟩

/-- On pure matrices, the local image acts by the original Leech matrix action. -/
theorem generatedLocal_matrix_action (f : localFiberSubgroup) (A : Sym24) :
    (generatedCentralizerMatrixAction
      (generatedLocalIntoCentralizer (QuotientGroup.mk f)) A).val =
      conwayMatrixAction f.val.2 A.val := by
  have h := congrArg (fun x : GriessSpace => (griessConwayEncode x).1)
    (generatedCentralizerMatrixAction_embed
      (generatedLocalIntoCentralizer (QuotientGroup.mk f)) A)
  change (griessConwayEncode (localGriessRepresentation f
    (generatedCentralPlusEmbed A 0).val)).1 = _ at h
  rw [localGriessRepresentation_encode, generatedCentralPlusEmbed_encode,
    localConwayRawRepresentation_apply, generatedCentralPlusEmbed_encode] at h
  exact h.symm

/-- On pure shorts, the local image is the constructed signed short representation. -/
theorem generatedLocal_short_action (f : localFiberSubgroup) (X : GriessShortIndex → ℝ) :
    generatedCentralizerShortAction
      (generatedLocalIntoCentralizer (QuotientGroup.mk f)) X =
        localShortRepresentation f X := by
  have h := congrArg (fun x : GriessSpace => (griessConwayEncode x).2.1)
    (generatedCentralizerShortAction_embed
      (generatedLocalIntoCentralizer (QuotientGroup.mk f)) X)
  change (griessConwayEncode (localGriessRepresentation f
    (generatedCentralPlusEmbed 0 X).val)).2.1 = _ at h
  rw [localGriessRepresentation_encode, generatedCentralPlusEmbed_encode,
    localConwayRawRepresentation_apply, generatedCentralPlusEmbed_encode] at h
  exact h.symm

/-- The matrix of the recognized orthogonal equivalence is exactly its stated matrix. -/
theorem generatedCentral_orthogonal_equiv_matrix (R : Matrix (Fin 24) (Fin 24) ℝ)
    (hTR : R.transpose * R = 1) (hRT : R * R.transpose = 1)
    (he : shortCoordinateOrthogonalEquiv R hTR hRT ∈ leechIsomSubgroup) :
    leechIsomMatrix ⟨shortCoordinateOrthogonalEquiv R hTR hRT, he⟩ = R := by
  ext i j
  change (R *ᵥ Pi.single j 1) i = R i j
  simp [Matrix.mulVec_single]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
