/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightRepresentative
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortSource

/-! Complete original short rows at the genuine root-eight incoming source. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false
-- The complete original packet has 4136 entries and a deep source-word spine.
set_option maxRecDepth 10000

/-- The checked full preferred-Q images determine the actual root-eight short permutation. -/
theorem generatedFifthRootEight_incoming_short_label_actual
    (a : GeneratedAxisGlobalFifthShortPacketIndex) :
    griessShortPermutation (generatedAxisGlobalFifthShortWordFiber 8).val.2
        (generatedAxisGlobalFifthShortPacketLabel a) =
      generatedAxisGlobalFifthRoot08ShortLabel a := by
  apply generatedNinth_short_Q_base_injective
  have h := griessShortQ_image_base (generatedAxisGlobalFifthShortWordFiber 8)
    (generatedAxisGlobalFifthShortPacketLabel a)
  rw [generatedAxisGlobalFifthShortWord_QImage,
    generatedAxisGlobalFifthQFast_actual 8 generatedAxisGlobalFifthQCache08_actual,
    ← generatedAxisGlobalFifthPacketQFinite_actual,
    generatedAxisGlobalFifthRoot08Short_QImage, qCentral_mul_base] at h
  exact h.symm

/-- The entire transported source retains distinct preferred-short rows. -/
theorem generatedFifthRootEight_incoming_short_label_injective :
    Function.Injective generatedAxisGlobalFifthRoot08ShortLabel := by
  intro a b h
  apply generatedAxisGlobalFifthShortPacketLabel_injective
  apply (griessShortPermutation (generatedAxisGlobalFifthShortWordFiber 8).val.2).injective
  simpa only [generatedFifthRootEight_incoming_short_label_actual] using h

private theorem packet_sum_at {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (c : ι → ℝ) (j : ι) :
    (∑ i, c i • Pi.single (f i) (1 : ℝ)) (f j) = c j := by
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp only [Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne (Ne.symm (fun h => hij (hf h))), mul_zero]
  · simp

/-- The original supported Fifth coefficient agrees with its complete integer numerator. -/
theorem generatedFifthRootEight_original_packet_numerator
    (a : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthShortPacketCoefficient a =
      (generatedNinthOriginalShortNumerator a : ℝ) / 16 :=
  generatedTwelfth_original_packet_numerator a

/-- Every full original incoming source row has its genuine signed integer coefficient. -/
theorem generatedFifthRootEight_incoming_short_row_actual
    (a : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthRoot08Packet.2.1 (generatedAxisGlobalFifthRoot08ShortLabel a) =
      (generatedNinthOriginalShortNumerator a : ℝ) / 16 *
        qSign (generatedAxisGlobalFifthRoot08ShortPhase a) := by
  change (∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i *
    qSign (generatedAxisGlobalFifthRoot08ShortPhase i)) •
      Pi.single (generatedAxisGlobalFifthRoot08ShortLabel i) (1 : ℝ)) _ = _
  rw [packet_sum_at _ generatedFifthRootEight_incoming_short_label_injective,
    generatedFifthRootEight_original_packet_numerator]

/-- An incoming source coordinate outside all original rows is exactly zero. -/
theorem generatedFifthRootEight_incoming_short_zero (r : GriessShortIndex)
    (hr : ∀ a, generatedAxisGlobalFifthRoot08ShortLabel a ≠ r) :
    generatedAxisGlobalFifthRoot08Packet.2.1 r = 0 := by
  change (∑ i, (generatedAxisGlobalFifthShortPacketCoefficient i *
    qSign (generatedAxisGlobalFifthRoot08ShortPhase i)) •
      Pi.single (generatedAxisGlobalFifthRoot08ShortLabel i) (1 : ℝ)) _ = _
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm (hr i)), mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
