/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPhaseFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortNumerator

/-! Genuine preferred-Q transport and original monomial phases give corrected short coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem short_original_image (f : localFiberSubgroup) (model : RepresentativeSpinModel)
    (hg : representativeSpinCertificate f.val.1 model.coordinate model.phase)
    (r s : GriessShortIndex)
    (hv : f.val.2.val (griessShortVector r) = griessShortVector s ∨
      f.val.2.val (griessShortVector r) = -griessShortVector s) :
    spinConjugation f.val.1 (monsterNortonShortQ r) =
      qCentral (monsterMonomialQuadratic model.phase (spinTranslation (griessShortQ s))) *
        monsterNortonShortQ s := by
  apply monsterNortonShortQ_image_of_vector_phase _ _ _ _ hv
  rw [monsterNortonShortQ_eq, generatedFifth_monomial_conjugation_coefficient _ _ _ hg,
    griessShortQ_coeff, zero_add]
  have hs := monsterNortonShortPermutation_of_vector _ _ _ hv
  have hb := griessShortQ_image_base f r
  rw [hs] at hb
  have ht : spinTranslation (spinConjugation f.val.1 (griessShortQ r)) =
      spinTranslation (griessShortQ s) := by
    funext i
    exact congrFun (congrArg toAdd hb) (Fin.castAdd 12 i)
  exact congrArg (monsterMonomialQuadratic model.phase) ht

/-- The actual central phase of the original word, evaluated on the target preferred lift. -/
theorem generatedFifth_monomial_permutation_original_image (k : Fin 6)
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan k))
    (r s : GriessShortIndex)
    (hv : (generatedFifthMonomialSpatialFiber k).val.2.val (griessShortVector r) =
        griessShortVector s ∨
      (generatedFifthMonomialSpatialFiber k).val.2.val (griessShortVector r) =
        -griessShortVector s) :
    spinConjugation (generatedFifthMonomialSpatialFiber k).val.1 (monsterNortonShortQ r) =
      qCentral (generatedFifthMonomialPermutationModelPhase k (spinTranslation (griessShortQ s))) *
        monsterNortonShortQ s :=
  short_original_image _ _ (generatedFifth_monomial_permutation_spin_plan_sound k hp) r s hv

/-- Both the original Parker coefficient and the actual Q-correction character are retained. -/
def generatedFifthMonomialPermutationShortPhase (k : Fin 6)
    (s : generatedFifthXiShortCachedLabel) : ZMod 2 :=
  generatedFifthMonomialPermutationModelPhase k
      (spinTranslation (generatedFifthXiShortCachedQ s)) +
    generatedFifthSignCachedShortPhase (generatedFifthMonomialPermutationCorrection k) s

/-- A true physical transport identifies the full corrected preferred-Q image. -/
theorem generatedFifth_monomial_permutation_corrected_short_image (k : Fin 6)
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan k))
    (r s : generatedFifthXiShortCachedLabel)
    (hv : (generatedFifthMonomialSpatialFiber k).val.2.val
        (griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
          griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) ∨
      (generatedFifthMonomialSpatialFiber k).val.2.val
        (griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
          -griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s))) :
    spinConjugation (generatedFifthMonomialPermutationCorrectedFiber k).val.1
      (monsterNortonShortQ
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
      qCentral (generatedFifthMonomialPermutationShortPhase k s) *
        monsterNortonShortQ
          (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) := by
  have hx := generatedFifth_monomial_permutation_original_image k hp _ _ hv
  change spinConjugation
    (spinHolomorphIncl (generatedFifthMonomialPermutationCorrection k) *
      (generatedFifthMonomialSpatialFiber k).val.1) _ = _
  rw [map_mul, MulAut.mul_apply]
  rw [hx, map_mul, spinConjugation_central, spinConjugation_incl, q_conjugation_central_phase]
  have hq : monsterNortonShortQ
      (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) =
        generatedFifthXiShortCachedQ s := by
    rw [monsterNortonShortQ_eq, ← generatedFifthXiEvenShortQ_actual,
      ← generatedFifthXiShortCachedQ_actual]
  apply NormalizedCocycleExtension.Extension.ext
  · simp only [qCentral_mul_base]
  · apply toAdd.injective
    simp only [qCentral_mul_coeff]
    unfold generatedFifthMonomialPermutationShortPhase generatedFifthSignCachedShortPhase
    have hgq : griessShortQ
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) =
          generatedFifthXiShortCachedQ s := by
      rw [← monsterNortonShortQ_eq, hq]
    rw [hq, hgq]
    exact (add_assoc _ _ _).symm

/-- A true physical transport and finite signed numerator equation fix the actual target row. -/
theorem generatedFifth_monomial_permutation_short_coordinate (k : Fin 6)
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan k))
    (r s : generatedFifthXiShortCachedLabel)
    (hv : (generatedFifthMonomialSpatialFiber k).val.2.val
        (griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
          griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) ∨
      (generatedFifthMonomialSpatialFiber k).val.2.val
        (griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
          -griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)))
    (hn : nortonUIntegerSign (generatedFifthMonomialPermutationShortPhase k s) *
        generatedFifthXiShortCachedNumerator r = generatedFifthXiShortCachedNumerator s) :
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber k)
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) := by
  rw [monsterNortonShortOperator_of_Q_image _ _ _ _
    (generatedFifth_monomial_permutation_corrected_short_image k hp r s hv)]
  exact generatedFifthXiShortCachedNumerator_signed r s _ hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
