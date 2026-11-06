/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalForm

/-! Complete true signed transport on nonzero rows fixes the whole original short vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Nonzero preferred integer rows suffice: finite injectivity gives support coverage,
and original orthogonality recovers every remaining coordinate. -/
theorem generatedSixth_short_fixed_of_supported_integer_certificate (f : localFiberSubgroup)
    (h : ∀ r : GriessShortIndex, generatedSixthFinalShortNumerator r ≠ 0 →
      nortonUIntegerSign (localShortPhase f r) * generatedSixthFinalShortNumerator r =
        generatedSixthFinalShortNumerator (griessShortPermutation f.val.2 r)) :
    localShortOperator f (griessConwayEncode generatedSixthAxis).2.1 =
      (griessConwayEncode generatedSixthAxis).2.1 := by
  let S := {r : GriessShortIndex // generatedSixthFinalShortNumerator r ≠ 0}
  have hm (r : S) :
      generatedSixthFinalShortNumerator (griessShortPermutation f.val.2 r.val) ≠ 0 := by
    rw [← h r.val r.property]
    apply mul_ne_zero
    · unfold nortonUIntegerSign
      split <;> norm_num
    · exact r.property
  let F : S → S := fun r => ⟨griessShortPermutation f.val.2 r.val, hm r⟩
  have hi : Function.Injective F := by
    intro r s hrs
    apply Subtype.ext
    apply (griessShortPermutation f.val.2).injective
    exact congrArg Subtype.val hrs
  have hj := Finite.surjective_of_injective hi
  let X := (griessConwayEncode generatedSixthAxis).2.1
  let Y := localShortOperator f X
  have hn : (∑ r : GriessShortIndex, Y r ^ 2) = ∑ r : GriessShortIndex, X r ^ 2 := by
    have hh := localShortRepresentation_pairing f X X
    change (∑ r, localShortOperator f X r * localShortOperator f X r) =
      ∑ r, X r * X r at hh
    simpa only [Y, pow_two] using hh
  have hs (s : GriessShortIndex) (hne : X s ≠ 0) : Y s = X s := by
    have hz : generatedSixthFinalShortNumerator s ≠ 0 := by
      intro hz
      apply hne
      change (griessConwayEncode generatedSixthAxis).2.1 s = 0
      rw [generatedSixth_final_short_numerator, hz, Int.cast_zero, zero_div]
    obtain ⟨r, hr⟩ := hj (⟨s, hz⟩ : S)
    have hp : griessShortPermutation f.val.2 r.val = s := congrArg Subtype.val hr
    change localShortOperator f X s = X s
    rw [← hp, localShortOperator_image]
    exact generatedSixth_final_short_signed _ _ _ (h r.val r.property)
  exact generatedFourth_real_eq_of_norm_support X Y hn hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
