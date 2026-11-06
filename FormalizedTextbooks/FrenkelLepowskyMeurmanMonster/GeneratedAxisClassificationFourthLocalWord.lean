/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup

/-! The literal local part of the next original-triality transition,
and its full actual extraspecial action with the central phase retained. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open Multiplicative

/-- The middle local word, including the verified Parker phase of P0. -/
noncomputable def generatedFourthLocalFiber : localFiberSubgroup :=
  xiSpinLocalFiber⁻¹ * (monsterSourcePermutationFiber 0)⁻¹ * xiSpinLocalFiber⁻¹

/-- The literal representative is original triality, this local word, original triality. -/
theorem generatedFourthAxis_local_expression :
    generatedFourthAxis = sExtra (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))) := by
  simp only [generatedFourthAxis, generatedFourthAxisWord, xiSpinGenerated,
    monsterSourcePermutationGenerated, generatedFourthLocalFiber,
    map_mul, map_inv]
  rfl

/-- The explicit positive inverse action Xi, P0, Xi on actual Q. -/
noncomputable def generatedFourthInverseQImage (q : Q) : Q :=
  xiSpinGImage (xiSpinGammaImage (monsterSourcePermutationImage 0
    (xiSpinGImage (xiSpinGammaImage q))))

/-- This formula is full actual spin conjugation, including its central coordinate. -/
theorem generatedFourthInverseQImage_eq (q : Q) :
    spinConjugation (generatedFourthLocalFiber⁻¹).val.1 q =
      generatedFourthInverseQImage q := by
  change spinConjugation
    ((xiSpinHolomorph⁻¹ * (monsterSourcePermutationSpin 0)⁻¹ * xiSpinHolomorph⁻¹)⁻¹) q = _
  simp only [mul_inv_rev, inv_inv, map_mul]
  change spinConjugation xiSpinHolomorph
    (spinConjugation (monsterSourcePermutationSpin 0)
      (spinConjugation xiSpinHolomorph q)) = _
  rw [xiSpinHolomorph_conjugation, monsterSourcePermutationSpin_conjugation,
    xiSpinHolomorph_conjugation]
  rfl

/-- The sole candidate preferred pair input. -/
noncomputable def generatedFourthPairInput : GriessShortIndex :=
  Sum.inl (1, griessPairIndex 8 11 (by decide))

/-- Its preferred physical inverse image in the original octad. -/
noncomputable def generatedFourthPairOutput : GriessShortIndex :=
  Sum.inl (1, griessPairIndex 10 11 (by decide))

/-- The selected finite input has the stated genuine increasing coordinate pair. -/
theorem generatedFourthPairInput_coordinates :
    griessCoordinatePair (griessPairIndex 8 11 (by decide)) = (8, 11) := by
  rw [griessPairIndex_coordinates]
  decide

/-- The selected finite output has the stated genuine increasing coordinate pair. -/
theorem generatedFourthPairOutput_coordinates :
    griessCoordinatePair (griessPairIndex 10 11 (by decide)) = (10, 11) := by
  rw [griessPairIndex_coordinates]
  decide

/-- The phase is extracted from the genuine full-Q formula. -/
noncomputable def generatedFourthPairPhase : ZMod 2 :=
  toAdd (generatedFourthInverseQImage (monsterNortonShortQ generatedFourthPairInput)).coeff

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check every actual binary coordinate of the three-factor inverse source action.
/-- The actual preferred input maps to the selected actual preferred output modulo the center. -/
theorem generatedFourth_pair_binary_certificate : ∀ i : Fin 24,
    toAdd (generatedFourthInverseQImage (monsterNortonShortQ generatedFourthPairInput)).base i =
      toAdd (monsterNortonShortQ generatedFourthPairOutput).base i := by
  simp only [monsterNortonShortQ, generatedFourthPairInput, generatedFourthPairOutput,
    griessShortIntegral, griessPairIndex_coordinates, show (8 : Fin 24) < 11 from by decide,
    show (10 : Fin 24) < 11 from by decide, ite_true]
  decide +kernel

/-- The full preferred-Q image certificate retains the central phase exactly. -/
theorem generatedFourth_pair_image :
    spinConjugation (generatedFourthLocalFiber⁻¹).val.1
        (monsterNortonShortQ generatedFourthPairInput) =
      qCentral generatedFourthPairPhase * monsterNortonShortQ generatedFourthPairOutput := by
  rw [generatedFourthInverseQImage_eq]
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    funext i
    exact generatedFourth_pair_binary_certificate i
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change generatedFourthPairPhase = generatedFourthPairPhase + 0
    rw [add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
