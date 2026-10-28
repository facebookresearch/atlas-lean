/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFiniteSoundness

/-! Soundness of exact full-Q and signed short-coordinate matches for the four monomial lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- A target address must match both the full original Q image and the original signed numerator. -/
def generatedFourthMonomialShortMatch (k : Fin 4) (q : Q) (n : ℤ) (w : ℕ) : Prop :=
  n ≠ 0 → generatedFourthLiftShortTargetValid w ∧
    toAdd (generatedFourthMonomialCorrectedQImage k q).base =
      toAdd (generatedFourthLiftShortTargetQ w).base ∧
    toAdd (generatedFourthMonomialCorrectedQImage k q).coeff =
      generatedFourthLiftShortTargetPhase w ∧
    generatedFourthLiftShortTargetNumerator w =
      (if generatedFourthLiftShortTargetPhase w = 0 then 1 else -1) * n

/-- Verified full-Q and integer matches certify the genuine signed short-coordinate image. -/
theorem generatedFourth_monomial_short_match_sound (k : Fin 4)
    (r : GriessShortIndex) (q : Q) (n : ℤ) (w : ℕ)
    (hq : q = griessShortQ r)
    (hn : (griessConwayEncode generatedFourthAxis).2.1 r = (n : ℝ) / 16)
    (hm : generatedFourthMonomialShortMatch k q n w)
    (hr : (griessConwayEncode generatedFourthAxis).2.1 r ≠ 0) :
    ∃ s c, spinConjugation (generatedFourthMonomialCorrectedFiber k).val.1 (griessShortQ r) =
        qCentral c * griessShortQ s ∧
      (griessConwayEncode generatedFourthAxis).2.1 s =
        qSign c * (griessConwayEncode generatedFourthAxis).2.1 r := by
  have hne : n ≠ 0 := by
    intro hz
    apply hr
    rw [hn, hz, Int.cast_zero, zero_div]
  obtain ⟨hw, hb, hc, hnw⟩ := hm hne
  let s := generatedFourthLiftShortTargetLabel w hw
  let c := generatedFourthLiftShortTargetPhase w
  refine ⟨s, c, ?_, ?_⟩
  · rw [← hq, generatedFourth_monomial_corrected_q_image]
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      rw [qCentral_mul_base]
      rw [← generatedFourth_lift_short_target_q w hw]
      exact hb
    · apply toAdd.injective
      rw [qCentral_mul_coeff, griessShortQ_coeff, add_zero]
      exact hc
  · change (griessConwayEncode generatedFourthAxis).2.1
      (generatedFourthLiftShortTargetLabel w hw) = _
    rw [generatedFourth_lift_short_target_numerator, hnw, hn, Int.cast_mul,
      generatedFourth_lift_short_integer_sign]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
