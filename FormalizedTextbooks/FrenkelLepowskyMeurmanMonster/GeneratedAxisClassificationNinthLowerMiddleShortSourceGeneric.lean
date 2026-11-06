/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMiddleShortSupport

/-! The complete middle dictionary is bound to the original spatial source, including zeros. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A certified original row has precisely its signed integer coefficient divided by16. -/
theorem generatedNinth_lower_signed_row_actual (k : Fin 4136)
    (h : GeneratedNinthShortRowCertificate k) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (generatedNinthShortRowTarget k) =
        (generatedNinthLowerSignedRowNumerator k : ℝ) / 16 := by
  rw [generatedNinth_short_row_coefficient_actual k h]
  rw [generatedNinth_short_row_numerator_fast_actual]
  unfold generatedNinthLowerSignedRowNumerator qSign
  by_cases hc : generatedNinthShortRowPhase k = 0
  · simp [hc]
  · simp [hc]
    ring

/-- Every nonzero dictionary value has a genuine chronological source row with that target. -/
theorem generatedNinth_lower_middle_short_generic_cache_covered
    (hkey : ∀ a : Fin 3856, generatedNinthLowerMiddleShortKey a =
      generatedNinthLowerShortAddress
        (generatedNinthShortRowTarget (generatedNinthLowerMiddleShortRow a)))
    (r : GriessShortIndex)
    (h : generatedNinthLowerMiddleShortCoefficient r ≠ 0) :
    ∃ k : Fin 4136, generatedNinthShortRowTarget k = r := by
  unfold generatedNinthLowerMiddleShortCoefficient at h
  split at h
  · exact False.elim (h rfl)
  · rename_i a ha
    refine ⟨generatedNinthLowerMiddleShortRow a, ?_⟩
    apply generatedNinth_lower_short_address_injective
    exact (hkey a).symm.trans
      (GeneratedNinthIncomingTree.lookup_sound _ _ _ _ ha)

/-- All original rows bind every actual middle short coefficient to the complete integer cache. -/
theorem generatedNinth_lower_middle_short_generic_actual
    (hkey : ∀ a : Fin 3856, generatedNinthLowerMiddleShortKey a =
      generatedNinthLowerShortAddress
        (generatedNinthShortRowTarget (generatedNinthLowerMiddleShortRow a)))
    (hcoverage : ∀ k : Fin 4136,
      generatedNinthLowerMiddleShortCoefficient (generatedNinthShortRowTarget k) =
        generatedNinthLowerSignedRowNumerator k)
    (hrows : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 r =
        (generatedNinthLowerMiddleShortCoefficient r : ℝ) / 16 := by
  by_cases hc : generatedNinthLowerMiddleShortCoefficient r = 0
  · rw [hc, Int.cast_zero, zero_div]
    apply not_ne_iff.mp
    intro hr
    obtain ⟨a, ha, _⟩ := generatedNinth_middle_short_nonzero_covered r hr
    let k := generatedNinthShortRowAddress a
    have hk : generatedNinthShortRowTarget k = r := by
      have ht := generatedNinth_short_row_target_actual k (hrows k)
      rw [generatedNinth_short_row_source_address] at ht
      exact ht.symm.trans ha
    have hn : generatedNinthLowerSignedRowNumerator k = 0 := by
      rw [← hcoverage, hk, hc]
    apply hr
    rw [← hk, generatedNinth_lower_signed_row_actual k (hrows k), hn,
      Int.cast_zero, zero_div]
  · obtain ⟨k, hk⟩ := generatedNinth_lower_middle_short_generic_cache_covered hkey r hc
    rw [← hk, generatedNinth_lower_signed_row_actual k (hrows k),
      hcoverage]

/-- Every actual incoming odd coordinate uses the same fully bound middle dictionary. -/
theorem generatedNinth_lower_incoming_generic_actual
    (hkey : ∀ a : Fin 3856, generatedNinthLowerMiddleShortKey a =
      generatedNinthLowerShortAddress
        (generatedNinthShortRowTarget (generatedNinthLowerMiddleShortRow a)))
    (hcoverage : ∀ k : Fin 4136,
      generatedNinthLowerMiddleShortCoefficient (generatedNinthShortRowTarget k) =
        generatedNinthLowerSignedRowNumerator k)
    (hrows : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inr (d, i))) =
        (generatedNinthLowerIncomingCoefficient d i : ℝ) / 16 :=
  generatedNinth_lower_middle_short_generic_actual hkey hcoverage hrows _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
