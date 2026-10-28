/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixLifts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactFullQCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup

/-! Complete actual preferred-Q transport uses only the already verified 24 full generator images.
The actual candidate short coefficient cache binding is an explicit separate prerequisite. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The compact original mask is the whole actual preferred lift of every dictionary coordinate. -/
theorem generatedTwelfth_complete_short_q_mask_actual (r : GriessShortIndex) :
    generatedAxisGlobalQMask (generatedAxisGlobalShortMask r) = monsterNortonShortQ r := by
  rw [← generatedAxisGlobalShortMask_Q_actual,
    generatedAxisGlobalShortQFinite_actual, monsterNortonShortQ_eq]

/-- All finite source transport obligations: complete preferred-Q image and signed coefficient. -/
def generatedTwelfthCompleteShortCondition (i : Fin 12) (a : Fin 98280) : Prop :=
  let r := generatedNinthLowerSpinShortIndex a
  generatedTwelfthSpinCompactFullQFast i
      (generatedAxisGlobalQMask (generatedAxisGlobalShortMask r)) =
    qCentral (generatedTwelfthCompleteShortPhase i r) *
      generatedAxisGlobalQMask
        (generatedAxisGlobalShortMask (generatedTwelfthCompleteShortDestination i r)) ∧
    nortonUIntegerSign (generatedTwelfthCompleteShortPhase i r) *
      generatedTwelfthCompleteShortInputInteger r =
        generatedTwelfthCompleteShortInputInteger (generatedTwelfthCompleteShortDestination i r)

/-- Every complete finite preferred lift certificate is an actual compact source short image. -/
theorem generatedTwelfth_complete_short_image (i : Fin 12)
    (h : ∀ a, generatedTwelfthCompleteShortCondition i a) (r : GriessShortIndex) :
    spinConjugation (generatedTwelfthCertifiedFiber i).val.1 (monsterNortonShortQ r) =
      qCentral (generatedTwelfthCompleteShortPhase i r) *
        monsterNortonShortQ (generatedTwelfthCompleteShortDestination i r) := by
  have hr := h (generatedNinthLowerSpinShortAddress r)
  simp only [generatedTwelfthCompleteShortCondition,
    generatedNinth_lower_spin_short_index_address] at hr
  change spinConjugation (generatedTwelfthSpinCompact i) (monsterNortonShortQ r) = _
  rw [generatedTwelfth_spin_compact_full_Q_fast,
    ← generatedTwelfth_complete_short_q_mask_actual r,
    ← generatedTwelfth_complete_short_q_mask_actual (generatedTwelfthCompleteShortDestination i r)]
  exact hr.1

/-- The whole preferred-Q image fixes its exact genuine spatial short permutation. -/
theorem generatedTwelfth_complete_short_destination_actual (i : Fin 12)
    (h : ∀ a, generatedTwelfthCompleteShortCondition i a) (r : GriessShortIndex) :
    griessShortPermutation (generatedTwelfthCertifiedFiber i).val.2 r =
      generatedTwelfthCompleteShortDestination i r := by
  have hq := generatedTwelfth_complete_short_image i h r
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at hq
  apply griessShortClassEquiv.injective
  apply Subtype.ext
  apply leechHyperbolicCoordinates.injective
  have hb := congrArg (fun q : Q => toAdd q.base) hq
  rw [qCentral_mul_base, griessShortQ_image_base] at hb
  exact hb

/-- Binding every actual short coordinate to the full integer cache yields genuine local
fixation. -/
theorem generatedTwelfth_complete_short_fix_of_source_cache (i : Fin 12)
    (h : ∀ a, generatedTwelfthCompleteShortCondition i a) (X : GriessShortIndex → ℝ)
    (hinput : ∀ r, 128 * X r = (generatedTwelfthCompleteShortInputInteger r : ℝ)) :
    localShortRepresentation (generatedTwelfthCertifiedFiber i) X = X := by
  funext s
  obtain ⟨r, hr⟩ := (griessShortPermutation
    (generatedTwelfthCertifiedFiber i).val.2).surjective s
  have hd : generatedTwelfthCompleteShortDestination i r = s :=
    (generatedTwelfth_complete_short_destination_actual i h r).symm.trans hr
  have ho := monsterNortonShortOperator_of_Q_image
    (generatedTwelfthCertifiedFiber i) r (generatedTwelfthCompleteShortDestination i r)
      (generatedTwelfthCompleteShortPhase i r) (generatedTwelfth_complete_short_image i h r) X
  rw [hd] at ho
  change localShortOperator (generatedTwelfthCertifiedFiber i) X s = X s
  rw [ho]
  have hc := (h (generatedNinthLowerSpinShortAddress r))
  simp only [generatedTwelfthCompleteShortCondition,
    generatedNinth_lower_spin_short_index_address] at hc
  have hz := congrArg (fun z : ℤ => (z : ℝ)) hc.2
  simp only [Int.cast_mul, nortonUIntegerSign_real] at hz
  rw [← hinput r, ← hinput (generatedTwelfthCompleteShortDestination i r), hd] at hz
  nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
