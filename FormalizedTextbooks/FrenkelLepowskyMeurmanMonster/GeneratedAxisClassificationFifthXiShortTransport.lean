/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortPreferredQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddCocode

/-! Physical Xi transport and the full preferred-Q phase determine the corrected short action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The genuine Xi coefficient plus the actual Q-correction character at the target row. -/
noncomputable def generatedFifthXiEvenShortPhase (r s : generatedFifthXiEvenShortLabel) : ZMod 2 :=
  toAdd (xiSpinGImage (xiSpinGammaImage (generatedFifthXiEvenShortQ r))).coeff +
    (qBeta (toAdd generatedFifthXiCorrection.base) (toAdd (generatedFifthXiEvenShortQ s).base) +
      qBeta (toAdd (generatedFifthXiEvenShortQ s).base) (toAdd generatedFifthXiCorrection.base))

/-- Actual physical transport certifies the corrected full preferred-Q image, including phase. -/
theorem generatedFifthXiEvenShort_image (r s : generatedFifthXiEvenShortLabel)
    (hv : xiSpinLocalFiber.val.2.val (griessShortVector (generatedFifthXiEvenShortIndex r)) =
        griessShortVector (generatedFifthXiEvenShortIndex s) ∨
      xiSpinLocalFiber.val.2.val (griessShortVector (generatedFifthXiEvenShortIndex r)) =
        -griessShortVector (generatedFifthXiEvenShortIndex s)) :
    spinConjugation generatedFifthXiCorrectedFiber.val.1
      (monsterNortonShortQ (generatedFifthXiEvenShortIndex r)) =
      qCentral (generatedFifthXiEvenShortPhase r s) *
        monsterNortonShortQ (generatedFifthXiEvenShortIndex s) := by
  have hx : spinConjugation xiSpinLocalFiber.val.1
      (monsterNortonShortQ (generatedFifthXiEvenShortIndex r)) =
      qCentral (toAdd (xiSpinGImage (xiSpinGammaImage (generatedFifthXiEvenShortQ r))).coeff) *
        monsterNortonShortQ (generatedFifthXiEvenShortIndex s) := by
    apply monsterNortonShortQ_image_of_vector_phase _ _ _ _ hv
    change toAdd (spinConjugation xiSpinHolomorph _).coeff = _
    rw [xiSpinHolomorph_conjugation, monsterNortonShortQ_eq, generatedFifthXiEvenShortQ_actual]
  change spinConjugation (spinHolomorphIncl generatedFifthXiCorrection * xiSpinHolomorph) _ = _
  rw [map_mul, MulAut.mul_apply]
  change spinConjugation (spinHolomorphIncl generatedFifthXiCorrection)
    (spinConjugation xiSpinLocalFiber.val.1 _) = _
  rw [hx, map_mul, spinConjugation_central, spinConjugation_incl,
    q_conjugation_central_phase]
  apply NormalizedCocycleExtension.Extension.ext
  · simp only [qCentral_mul_base]
  · apply toAdd.injective
    simp only [qCentral_mul_coeff]
    unfold generatedFifthXiEvenShortPhase
    have hs : monsterNortonShortQ (generatedFifthXiEvenShortIndex s) =
        generatedFifthXiEvenShortQ s :=
      (monsterNortonShortQ_eq _).trans (generatedFifthXiEvenShortQ_actual s).symm
    rw [hs]
    exact (add_assoc _ _ _).symm

/-- The actual corrected short coordinate has precisely the same full preferred-Q phase. -/
theorem generatedFifthXiEvenShort_operator (r s : generatedFifthXiEvenShortLabel)
    (hv : xiSpinLocalFiber.val.2.val (griessShortVector (generatedFifthXiEvenShortIndex r)) =
        griessShortVector (generatedFifthXiEvenShortIndex s) ∨
      xiSpinLocalFiber.val.2.val (griessShortVector (generatedFifthXiEvenShortIndex r)) =
        -griessShortVector (generatedFifthXiEvenShortIndex s))
    (X : GriessShortIndex → ℝ) :
    localShortOperator generatedFifthXiCorrectedFiber X (generatedFifthXiEvenShortIndex s) =
      qSign (generatedFifthXiEvenShortPhase r s) * X (generatedFifthXiEvenShortIndex r) :=
  monsterNortonShortOperator_of_Q_image _ _ _ _ (generatedFifthXiEvenShort_image r s hv) X

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
