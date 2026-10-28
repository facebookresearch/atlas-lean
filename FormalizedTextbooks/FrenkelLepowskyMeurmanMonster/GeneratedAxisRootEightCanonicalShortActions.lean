/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalPositiveAxis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup

/-! Whole actual canonical short-coordinate transport retains the original preferred-Q phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A complete original preferred-Q image gives the actual canonical short coefficient. -/
theorem generatedRootEight_canonical_short_coordinate_of_Q_image
    (r s : GriessShortIndex) (c : ZMod 2)
    (h : spinConjugation generatedRootEightCanonicalPositiveFiber.val.1
      (monsterNortonShortQ r) = qCentral c * monsterNortonShortQ s) :
    (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 s =
      (nortonUIntegerSign c * generatedRootEightPositiveFinalShortNumerator r : ℤ) / 256 := by
  change (localGriessRepresentation generatedRootEightCanonicalPositiveFiber
    generatedRootEightIncomingPositiveTrialityDestination |> griessConwayEncode).2.1 s = _
  rw [localGriessRepresentation_encode]
  change localShortOperator generatedRootEightCanonicalPositiveFiber
    (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).2.1 s = _
  rw [monsterNortonShortOperator_of_Q_image _ r s c h,
    generatedRootEight_positive_final_short_integer]
  simp only [Int.cast_mul, nortonUIntegerSign_real]
  ring

/-- Complete preferred-Q images bind a full integer cache to every actual canonical short row. -/
theorem generatedRootEight_canonical_short_cache_actual
    (destination : GriessShortIndex → GriessShortIndex)
    (phase : GriessShortIndex → ZMod 2) (cache : GriessShortIndex → ℤ)
    (hq : ∀ r, spinConjugation generatedRootEightCanonicalPositiveFiber.val.1
      (monsterNortonShortQ r) = qCentral (phase r) * monsterNortonShortQ (destination r))
    (hcache : ∀ r, nortonUIntegerSign (phase r) *
      generatedRootEightPositiveFinalShortNumerator r = cache (destination r)) :
    ∀ s, (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 s =
      (cache s : ℝ) / 256 := by
  have hd (r : GriessShortIndex) :
      griessShortPermutation generatedRootEightCanonicalPositiveFiber.val.2 r = destination r := by
    have h := hq r
    rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at h
    apply griessShortClassEquiv.injective
    apply Subtype.ext
    apply leechHyperbolicCoordinates.injective
    have hb := congrArg (fun q : Q => Multiplicative.toAdd q.base) h
    rw [qCentral_mul_base, griessShortQ_image_base] at hb
    exact hb
  intro s
  obtain ⟨r, hr⟩ :=
    (griessShortPermutation generatedRootEightCanonicalPositiveFiber.val.2).surjective s
  have hrs : destination r = s := (hd r).symm.trans hr
  rw [← hrs, generatedRootEight_canonical_short_coordinate_of_Q_image r _ _ (hq r), hcache r]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
