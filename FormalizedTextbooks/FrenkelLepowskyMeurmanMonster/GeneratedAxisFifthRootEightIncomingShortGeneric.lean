/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightIncomingShortData

/-! Bounded original-row certificates bind the entire genuine incoming short constituent. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- The complete original source packet unfolds to all4136 chronological entries.
set_option maxRecDepth 10000

/-- Each chronological source row has precisely its true signed integer coefficient. -/
theorem generatedFifthRootEight_incoming_signed_row_actual (k : Fin 4136) :
    generatedAxisGlobalFifthRoot08Packet.2.1 (generatedFifthRootEightIncomingShortTarget k) =
      (generatedFifthRootEightIncomingSignedRowNumerator k : ℝ) / 16 := by
  rw [generatedFifthRootEightIncomingShortTarget, generatedFifthRootEight_incoming_short_row_actual]
  have hn : generatedNinthOriginalShortNumerator (generatedAxisGlobalFifthPacketFromNumber k) =
      generatedNinthShortRowNumeratorFast k :=
    generatedNinth_short_row_numerator_fast_actual k
  rw [hn]
  unfold generatedFifthRootEightIncomingSignedRowNumerator qSign
  by_cases h : generatedAxisGlobalFifthRoot08ShortPhase
      (generatedAxisGlobalFifthPacketFromNumber k) = 0
  · simp [h]
  · simp only [h, ite_false, Int.cast_neg, mul_neg_one]
    ring

/-- Sparse lookup can only return a genuine original incoming row having the queried coordinate. -/
theorem generatedFifthRootEight_incoming_short_cache_covered
    (hkey : ∀ a : Fin 3856, generatedFifthRootEightIncomingShortKey a =
      generatedNinthLowerShortAddress
        (generatedFifthRootEightIncomingShortTarget (generatedFifthRootEightIncomingShortRow a)))
    (r : GriessShortIndex) (h : generatedFifthRootEightIncomingShortCoefficient r ≠ 0) :
    ∃ k : Fin 4136, generatedFifthRootEightIncomingShortTarget k = r := by
  unfold generatedFifthRootEightIncomingShortCoefficient at h
  split at h
  · exact False.elim (h rfl)
  · rename_i a ha
    refine ⟨generatedFifthRootEightIncomingShortRow a, ?_⟩
    apply generatedNinth_lower_short_address_injective
    exact (hkey a).symm.trans (GeneratedNinthIncomingTree.lookup_sound _ _ _ _ ha)

/-- Source-key soundness and complete original-row coverage determine every incoming coordinate. -/
theorem generatedFifthRootEight_incoming_short_generic_actual
    (hkey : ∀ a : Fin 3856, generatedFifthRootEightIncomingShortKey a =
      generatedNinthLowerShortAddress
        (generatedFifthRootEightIncomingShortTarget (generatedFifthRootEightIncomingShortRow a)))
    (hcoverage : ∀ k : Fin 4136,
      generatedFifthRootEightIncomingShortCoefficient
        (generatedFifthRootEightIncomingShortTarget k) =
        generatedFifthRootEightIncomingSignedRowNumerator k)
    (r : GriessShortIndex) :
    generatedAxisGlobalFifthRoot08Packet.2.1 r =
      (generatedFifthRootEightIncomingShortCoefficient r : ℝ) / 16 := by
  by_cases h : ∃ k : Fin 4136, generatedFifthRootEightIncomingShortTarget k = r
  · obtain ⟨k, rfl⟩ := h
    rw [generatedFifthRootEight_incoming_signed_row_actual, hcoverage]
  · have hc : generatedFifthRootEightIncomingShortCoefficient r = 0 := by
      by_contra hc
      exact h (generatedFifthRootEight_incoming_short_cache_covered hkey r hc)
    rw [hc, Int.cast_zero, zero_div]
    apply generatedFifthRootEight_incoming_short_zero
    intro a ha
    apply h
    refine ⟨generatedAxisGlobalFifthPacketNumber a, ?_⟩
    simpa only [generatedFifthRootEightIncomingShortTarget,
      generatedAxisGlobalFifthPacketFromNumber_number] using ha

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
