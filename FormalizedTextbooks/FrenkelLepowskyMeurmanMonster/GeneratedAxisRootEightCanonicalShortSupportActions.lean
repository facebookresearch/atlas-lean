/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortPackedActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightShortSupportTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortCacheData

/-! Full actual canonical short transport from exact source binding and complete nonzero source images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every nonzero original source is checked with its entire preferred-Q central phase. -/
def generatedRootEightCanonicalShortSupportCondition (r : GriessShortIndex) : Prop :=
  generatedRootEightPositiveFinalShortCachedNumerator r ≠ 0 →
    generatedRootEightCanonicalShortPackedCondition r ∧
      nortonUIntegerSign (generatedRootEightCanonicalShortPhase r) *
        generatedRootEightPositiveFinalShortCachedNumerator r =
          generatedRootEightCanonicalShortCachedNumerator (generatedRootEightCanonicalShortDestination r)

/-- Complete actual source binding, exact support cardinality, and all nonzero images
supply every canonical short coordinate, including all zeros. -/
theorem generatedRootEight_canonical_short_cache_of_support
    (hsource : ∀ r, generatedRootEightPositiveFinalShortNumerator r =
      generatedRootEightPositiveFinalShortCachedNumerator r)
    (hcard : Nat.card {r : GriessShortIndex // generatedRootEightPositiveFinalShortCachedNumerator r ≠ 0} =
      Nat.card {r : GriessShortIndex // generatedRootEightCanonicalShortCachedNumerator r ≠ 0})
    (h : ∀ r, generatedRootEightCanonicalShortSupportCondition r) :
    ∀ r, (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 r =
      (generatedRootEightCanonicalShortCachedNumerator r : ℝ) / 256 := by
  let X := (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).2.1
  let Y : GriessShortIndex → ℝ := fun r => (generatedRootEightCanonicalShortCachedNumerator r : ℝ) / 256
  have hX (r : GriessShortIndex) : X r =
      (generatedRootEightPositiveFinalShortCachedNumerator r : ℝ) / 256 := by
    rw [show X r = (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).2.1 r from rfl,
      generatedRootEight_positive_final_short_integer, hsource r]
  have hSX : Nat.card {r : GriessShortIndex // X r ≠ 0} =
      Nat.card {r : GriessShortIndex // generatedRootEightPositiveFinalShortCachedNumerator r ≠ 0} := by
    apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro r
    rw [hX r]
    norm_num
  have hSY : Nat.card {r : GriessShortIndex // Y r ≠ 0} =
      Nat.card {r : GriessShortIndex // generatedRootEightCanonicalShortCachedNumerator r ≠ 0} := by
    apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro r
    change ((generatedRootEightCanonicalShortCachedNumerator r : ℝ) / 256 ≠ 0) ↔ _
    norm_num
  have hf : localShortRepresentation generatedRootEightCanonicalPositiveFiber X = Y := by
    apply generatedRootEight_short_transport_of_nonzero_sources
    · exact hSX.trans (hcard.trans hSY.symm)
    · intro r hr
      have hn : generatedRootEightPositiveFinalShortCachedNumerator r ≠ 0 := by
        intro hz
        rw [hX r, hz, Int.cast_zero, zero_div] at hr
        exact hr rfl
      obtain ⟨hq, hc⟩ := h r hn
      have hi := generatedRootEight_canonical_short_image_of_packed r hq
      have hd : griessShortPermutation generatedRootEightCanonicalPositiveFiber.val.2 r =
          generatedRootEightCanonicalShortDestination r := by
        rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at hi
        apply griessShortClassEquiv.injective
        apply Subtype.ext
        apply leechHyperbolicCoordinates.injective
        have hb := congrArg (fun q : Q => Multiplicative.toAdd q.base) hi
        rw [qCentral_mul_base, griessShortQ_image_base] at hb
        exact hb
      change localShortOperator generatedRootEightCanonicalPositiveFiber X
        (griessShortPermutation generatedRootEightCanonicalPositiveFiber.val.2 r) = _
      rw [hd, monsterNortonShortOperator_of_Q_image _ r _ _ hi, hX r]
      have he := congrArg (fun z : ℤ => (z : ℝ)) hc
      simp only [Int.cast_mul, nortonUIntegerSign_real] at he
      change qSign (generatedRootEightCanonicalShortPhase r) *
        ((generatedRootEightPositiveFinalShortCachedNumerator r : ℝ) / 256) =
        (generatedRootEightCanonicalShortCachedNumerator (generatedRootEightCanonicalShortDestination r) : ℝ) / 256
      rw [← mul_div_assoc, he]
  intro r
  change (localGriessRepresentation generatedRootEightCanonicalPositiveFiber
    generatedRootEightIncomingPositiveTrialityDestination |> griessConwayEncode).2.1 r = _
  rw [localGriessRepresentation_encode]
  change localShortRepresentation generatedRootEightCanonicalPositiveFiber X r = Y r
  rw [hf]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
