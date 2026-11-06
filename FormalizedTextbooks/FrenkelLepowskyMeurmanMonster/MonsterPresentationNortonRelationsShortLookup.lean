/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact short-coordinate transport from computable, phase-correct actual Q image certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinLeechCompatibility

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A finite full-Q certificate determines the actual short-coordinate permutation and sign. -/
theorem monsterNortonShortOperator_of_Q_image (f : localFiberSubgroup)
    (r s : GriessShortIndex) (c : ZMod 2)
    (h : spinConjugation f.val.1 (monsterNortonShortQ r) = qCentral c * monsterNortonShortQ s)
    (X : GriessShortIndex → ℝ) : localShortOperator f X s = qSign c * X r := by
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at h
  have hp : griessShortPermutation f.val.2 r = s := by
    apply griessShortClassEquiv.injective
    apply Subtype.ext
    apply leechHyperbolicCoordinates.injective
    have hb := congrArg (fun q : Q => toAdd q.base) h
    rw [qCentral_mul_base] at hb
    have hi := griessShortQ_image_base f r
    rw [hi] at hb
    exact hb
  have hc : localShortPhase f r = c := by
    have hcoeff := congrArg (fun q : Q => toAdd q.coeff) h
    rw [qCentral_mul_coeff, griessShortQ_coeff, add_zero] at hcoeff
    exact hcoeff
  rw [← hp, localShortOperator_image, hc]

/-- The intrinsic preferred lift of the first X row. -/
def monsterNortonXiFirstShortInput : GriessShortIndex := Sum.inr (Sum.inr (0, 0))

/-- The actual xi image row; the physical lattice vector may differ by an overall sign. -/
def monsterNortonXiFirstShortOutput : GriessShortIndex := Sum.inr (Sum.inr (1024, 0))

/-- The central sign is taken from the full actual source xi conjugation formula. -/
noncomputable def monsterNortonXiFirstShortPhase : ZMod 2 :=
  toAdd (xiSpinGImage (xiSpinGammaImage (monsterNortonShortQ monsterNortonXiFirstShortInput))).coeff

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- All 24 binary coordinates use the certified integer inverse of the actual Leech basis.
/-- The explicit actual xi Q formula sends the first X label to the stated short label. -/
theorem monsterNortonXiFirstShort_binary : ∀ i : Fin 24,
    toAdd (xiSpinGImage (xiSpinGammaImage
      (monsterNortonShortQ monsterNortonXiFirstShortInput))).base i =
        toAdd (monsterNortonShortQ monsterNortonXiFirstShortOutput).base i := by
  decide +kernel

/-- This is a full actual Q image, including the central sign. -/
theorem monsterNortonXiFirstShort_image :
    spinConjugation xiSpinLocalFiber.val.1 (monsterNortonShortQ monsterNortonXiFirstShortInput) =
      qCentral monsterNortonXiFirstShortPhase * monsterNortonShortQ monsterNortonXiFirstShortOutput
        := by
  rw [show xiSpinLocalFiber.val.1 = xiSpinHolomorph from rfl, xiSpinHolomorph_conjugation]
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    funext i
    exact monsterNortonXiFirstShort_binary i
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change monsterNortonXiFirstShortPhase = monsterNortonXiFirstShortPhase + 0
    rw [add_zero]

/-- The first nontrivial actual xi short-row dictionary is obtained without class enumeration. -/
theorem monsterNortonXiFirstShort_operator (X : GriessShortIndex → ℝ) :
    localShortOperator xiSpinLocalFiber X monsterNortonXiFirstShortOutput =
      qSign monsterNortonXiFirstShortPhase * X monsterNortonXiFirstShortInput := by
  exact monsterNortonShortOperator_of_Q_image _ _ _ _ monsterNortonXiFirstShort_image X

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
