/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCMetadata
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortPackedCacheSourceGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSupportActions

/-! Ungated actual Tenth short support bridge.
The reused support theorem is polymorphic in the fiber and coefficient function.
No Ninth source, candidate data, axis action, or Fin11 fixation theorem is used. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Complete actual source calibration, with all98280 source coefficients and every zero. -/
def GeneratedTenthTwoFixerCSourceCacheCondition : Prop :=
  ∀ r : GriessShortIndex, 128 * (griessConwayEncode generatedTenthAxis).2.1 r =
    (generatedTenthFinalShortPackedCacheCoefficient r : ℝ)

/-- Full preferred source/target masks, exact central phase, and signed integer coefficient. -/
def GeneratedTenthTwoFixerCPackedCondition (g : Fin 2)
    (destination : Fin 98280 → Fin 98280) (phase : Fin 98280 → ZMod 2)
    (a : Fin 98280) : Prop :=
  let r := generatedNinthLowerSpinShortIndex a
  let s := generatedNinthLowerSpinShortIndex (destination a)
  generatedAxisGlobalQMaskVector (generatedTenthTwoFixerCColumns g)
      (generatedAxisGlobalShortMask r) = generatedAxisGlobalShortMask s ∧
    (if (generatedAxisGlobalQMaskCentral (generatedTenthTwoFixerCRows g)
      (generatedTenthTwoFixerCCoefficients g) (generatedAxisGlobalShortMask r)).testBit 0
        then (1 : ZMod 2) else 0) = phase a ∧
    nortonUIntegerSign (phase a) * generatedTenthFinalShortPackedCacheCoefficient r =
      generatedTenthFinalShortPackedCacheCoefficient s

/-- All nonzero sources must retain their complete genuine signed preferred-Q certificate. -/
def GeneratedTenthTwoFixerCSupportCondition (g : Fin 2)
    (destination : Fin 98280 → Fin 98280) (phase : Fin 98280 → ZMod 2) : Prop :=
  ∀ a : Fin 98280,
    generatedTenthFinalShortPackedCacheCoefficient (generatedNinthLowerSpinShortIndex a) ≠ 0 →
      GeneratedTenthTwoFixerCPackedCondition g destination phase a

/-- Zero complement condition uses the actual genuine spatial permutation, not candidate labels. -/
def GeneratedTenthTwoFixerCComplementCondition (g : Fin 2) : Prop :=
  ∀ r : GriessShortIndex, generatedTenthFinalShortPackedCacheCoefficient r = 0 →
    generatedTenthFinalShortPackedCacheCoefficient
      (griessShortPermutation (generatedTenthTwoFixerCFiber g).val.2 r) = 0

/-- Preferred packed masks retain the entire actual positive central short-Q section. -/
theorem generatedTenth_two_fixer_c_preferred (r : GriessShortIndex) :
    generatedAxisGlobalQMask (generatedAxisGlobalShortMask r) = monsterNortonShortQ r := by
  rw [← generatedAxisGlobalShortMask_Q_actual,
    generatedAxisGlobalShortQFinite_actual, monsterNortonShortQ_eq]

/-- The all-source cache condition follows only after the complete held source bridge. -/
theorem generatedTenth_two_fixer_c_source_cache
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hm : GeneratedTenthFinalShortSourceMatrixCalibration M)
    (hc : GeneratedTenthFinalShortFunctionCacheCondition M
      generatedTenthFinalShortPackedCacheAddressValue) :
    GeneratedTenthTwoFixerCSourceCacheCondition :=
  generatedTenth_final_short_packed_cache_actual hin M hm hc

/-- Every packed support row binds the entire genuine extraspecial image, including its phase. -/
theorem generatedTenth_two_fixer_c_image (g : Fin 2)
    (destination : Fin 98280 → Fin 98280) (phase : Fin 98280 → ZMod 2) (a : Fin 98280)
    (h : GeneratedTenthTwoFixerCPackedCondition g destination phase a) :
    spinConjugation (generatedTenthTwoFixerCFiber g).val.1
        (monsterNortonShortQ (generatedNinthLowerSpinShortIndex a)) =
      qCentral (phase a) *
        monsterNortonShortQ (generatedNinthLowerSpinShortIndex (destination a)) := by
  rw [← generatedTenth_two_fixer_c_preferred,
    ← generatedTenth_two_fixer_c_preferred]
  rw [generatedTenth_two_fixer_c_mask_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ h.1 h.2.1

/-- Whole preferred-Q transport proves the proposed target is the actual spatial permutation. -/
theorem generatedTenth_two_fixer_c_destination_actual (g : Fin 2)
    (destination : Fin 98280 → Fin 98280) (phase : Fin 98280 → ZMod 2) (a : Fin 98280)
    (h : GeneratedTenthTwoFixerCPackedCondition g destination phase a) :
    griessShortPermutation (generatedTenthTwoFixerCFiber g).val.2
        (generatedNinthLowerSpinShortIndex a) =
      generatedNinthLowerSpinShortIndex (destination a) := by
  have hq := generatedTenth_two_fixer_c_image g destination phase a h
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at hq
  apply griessShortClassEquiv.injective
  apply Subtype.ext
  apply leechHyperbolicCoordinates.injective
  have hb := congrArg (fun q : Q => toAdd q.base) hq
  rw [qCentral_mul_base, griessShortQ_image_base] at hb
  exact hb

/-- Complete support checks give actual C fixation, with zeros handled by genuine bijectivity. -/
theorem generatedTenth_two_fixer_c_short_fix (g : Fin 2)
    (destination : Fin 98280 → Fin 98280) (phase : Fin 98280 → ZMod 2)
    (hsource : GeneratedTenthTwoFixerCSourceCacheCondition)
    (hsupport : GeneratedTenthTwoFixerCSupportCondition g destination phase) :
    localShortRepresentation (generatedTenthTwoFixerCFiber g)
      (griessConwayEncode generatedTenthAxis).2.1 =
        (griessConwayEncode generatedTenthAxis).2.1 := by
  apply generatedNinth_lower_spin_short_fixer_of_nonzero_sources
  intro r hr
  have hn : generatedTenthFinalShortPackedCacheCoefficient r ≠ 0 := by
    intro hz
    have hh := hsource r
    rw [hz, Int.cast_zero] at hh
    apply hr
    linarith
  let a := generatedNinthLowerSpinShortAddress r
  have hp := hsupport a (by
    simpa only [a, generatedNinth_lower_spin_short_index_address] using hn)
  have hd := generatedTenth_two_fixer_c_destination_actual g destination phase a hp
  have ho := monsterNortonShortOperator_of_Q_image (generatedTenthTwoFixerCFiber g)
    (generatedNinthLowerSpinShortIndex a)
    (generatedNinthLowerSpinShortIndex (destination a)) (phase a)
    (generatedTenth_two_fixer_c_image g destination phase a hp)
    (griessConwayEncode generatedTenthAxis).2.1
  have hz := congrArg (fun z : ℤ => (z : ℝ)) hp.2.2
  simp only [Int.cast_mul, nortonUIntegerSign_real] at hz
  rw [← hsource (generatedNinthLowerSpinShortIndex a),
    ← hsource (generatedNinthLowerSpinShortIndex (destination a))] at hz
  simp only [a, generatedNinth_lower_spin_short_index_address] at hd ho hz
  change localShortOperator (generatedTenthTwoFixerCFiber g)
    (griessConwayEncode generatedTenthAxis).2.1
      (griessShortPermutation (generatedTenthTwoFixerCFiber g).val.2 r) = _
  rw [hd, ho]
  nlinarith

/-- The genuine permutation sends the entire zero complement to zero as a proved consequence. -/
theorem generatedTenth_two_fixer_c_complement (g : Fin 2)
    (destination : Fin 98280 → Fin 98280) (phase : Fin 98280 → ZMod 2)
    (hsource : GeneratedTenthTwoFixerCSourceCacheCondition)
    (hsupport : GeneratedTenthTwoFixerCSupportCondition g destination phase) :
    GeneratedTenthTwoFixerCComplementCondition g := by
  intro r hz
  have hf := generatedTenth_two_fixer_c_short_fix g destination phase hsource hsupport
  change localShortOperator (generatedTenthTwoFixerCFiber g)
    (griessConwayEncode generatedTenthAxis).2.1 =
      (griessConwayEncode generatedTenthAxis).2.1 at hf
  have hr : (griessConwayEncode generatedTenthAxis).2.1 r = 0 := by
    have h := hsource r
    rw [hz, Int.cast_zero] at h
    linarith
  have hi := localShortOperator_image (generatedTenthTwoFixerCFiber g)
    (griessConwayEncode generatedTenthAxis).2.1 r
  rw [hf, hr, mul_zero] at hi
  have ht := hsource (griessShortPermutation (generatedTenthTwoFixerCFiber g).val.2 r)
  rw [hi, mul_zero] at ht
  exact_mod_cast ht.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

