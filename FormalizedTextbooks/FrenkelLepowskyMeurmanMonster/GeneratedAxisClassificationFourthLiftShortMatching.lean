/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortSoundness

/-! Full preferred-Q images certify both the actual short label and its original sign. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A full preferred-Q image determines the actual spatial short label and its central phase. -/
theorem generatedFourth_lift_short_image_recognition (f : localFiberSubgroup)
    (r s : GriessShortIndex) (c : ZMod 2)
    (h : spinConjugation f.val.1 (griessShortQ r) = qCentral c * griessShortQ s) :
    griessShortPermutation f.val.2 r = s ∧ localShortPhase f r = c := by
  constructor
  · have hb := congrArg NormalizedCocycleExtension.Extension.base h
    rw [griessShortQ_image_base, qCentral_mul_base] at hb
    apply griessShortClass_injective
    apply leechHyperbolicCoordinates.injective
    exact congrArg toAdd hb
  · have hc := congrArg (fun q : Q => toAdd q.coeff) h
    rw [qCentral_mul_coeff, griessShortQ_coeff, add_zero] at hc
    exact hc

/-- Supported full-Q matching certifies the entire actual local short-coordinate action. -/
theorem generatedFourth_lift_short_fixed_of_q_matching (f : localFiberSubgroup)
    (X : GriessShortIndex → ℝ)
    (h : ∀ r, X r ≠ 0 → ∃ s c,
      spinConjugation f.val.1 (griessShortQ r) = qCentral c * griessShortQ s ∧
        X s = qSign c * X r) : localShortOperator f X = X := by
  apply generatedFourth_local_short_fixed_of_support
  intro r hr
  obtain ⟨s, c, hq, hx⟩ := h r hr
  obtain ⟨hs, hc⟩ := generatedFourth_lift_short_image_recognition f r s c hq
  rw [hs, hc]
  exact hx

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
