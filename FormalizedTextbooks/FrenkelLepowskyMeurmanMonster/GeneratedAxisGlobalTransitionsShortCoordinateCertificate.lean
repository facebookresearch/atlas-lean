/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparsePairingCoordinates

/-! Complete original extraspecial certificates determine actual short coefficients at selected target coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A complete original Q image gives the exact source coefficient at its actual target coordinate. -/
theorem generatedAxisGlobalShort_coordinate_of_QImage
    (f : localFiberSubgroup) (r s : GriessShortIndex) (c : ZMod 2)
    (hq : spinConjugation f.val.1 (griessShortQ r) = qCentral c * griessShortQ s)
    (C : GriessShortIndex → ℝ) :
    localShortOperator f C s = qSign c * C r := by
  have hb : localShortOperator f (Pi.single r (1 : ℝ)) =
      qSign c • Pi.single s (1 : ℝ) := by
    apply monsterNortonShortBasis_of_Q_image
    rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq]
    exact hq
  have hs : griessShortPermutation f.val.2 r = s := by
    by_contra hn
    have he := congrFun hb (griessShortPermutation f.val.2 r)
    rw [localShortOperator_image] at he
    simp only [Pi.single_eq_same, mul_one, Pi.smul_apply, smul_eq_mul] at he
    have hz : (Pi.single s (1 : ℝ) : GriessShortIndex → ℝ)
        (griessShortPermutation f.val.2 r) = 0 := by
      simp [hn]
    rw [hz, mul_zero] at he
    have hsq := qSign_sq (localShortPhase f r)
    rw [he, zero_mul] at hsq
    norm_num at hsq
  have hp : qSign (localShortPhase f r) = qSign c := by
    have he := congrFun hb (griessShortPermutation f.val.2 r)
    rw [localShortOperator_image, hs] at he
    simpa using he
  rw [← hs, localShortOperator_image, hp]

/-- Every selected genuine Griess short coordinate is the certified original input coordinate. -/
theorem generatedAxisGlobalGriessShort_coordinate_of_QImage
    (f : localFiberSubgroup) (r s : GriessShortIndex) (c : ZMod 2)
    (hq : spinConjugation f.val.1 (griessShortQ r) = qCentral c * griessShortQ s)
    (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (localFiberIntoH f) x)).2.1 s =
      qSign c * (griessConwayEncode x).2.1 r := by
  change (griessConwayEncode (localGriessRepresentation f x)).2.1 s = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  exact generatedAxisGlobalShort_coordinate_of_QImage f r s c hq _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
