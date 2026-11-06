/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressSigned
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairEnumeration

/-! The complete original nonzero short support is covered by genuine sparse catalogue addresses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuinely nonzero source short coordinate is a certified sparse address. -/
theorem generatedSixth_xi_short_support_covered (r : GriessShortIndex)
    (hr : (griessConwayEncode generatedSixthAxis).2.1 r ≠ 0) :
    ∃ x : GeneratedSixthXiShortAddress, generatedSixthXiShortAddressIndex x = r := by
  classical
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · obtain ⟨k, hk⟩ := generatedSixth_xi_pair_input_surjective s p
    exact ⟨Sum.inl k, hk⟩
  · have ho : ∃ f : Fin 231, generatedSixthFinalOctadCacheOctad f = o := by
      by_contra hn
      exact hr (generatedSixth_final_octad_cached_zero o e hn)
    obtain ⟨f, rfl⟩ := ho
    exact ⟨Sum.inr (Sum.inl (f, e)), rfl⟩
  · have hd := generatedSixth_monomial_odd_support d j hr
    exact ⟨Sum.inr (Sum.inr (generatedSixthMonomialOddOwner d, j)),
      congrArg (fun c => Sum.inr (Sum.inr (c, j))) hd⟩

/-- Complete actual sparse transport certificates fix the entire original short constituent. -/
theorem generatedSixth_xi_short_fixed_of_sparse_certificates
    (h : ∀ x : GeneratedSixthXiShortAddress, ∃ y : GeneratedSixthXiShortAddress,
      sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMask x) =
        generatedSixthXiShortAddressMask y ∧
      nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMask x)) *
        generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y) :
    localShortOperator (generatedSixthCorrectedGenerator 4)
        (griessConwayEncode generatedSixthAxis).2.1 =
      (griessConwayEncode generatedSixthAxis).2.1 := by
  apply generatedSixth_xi_short_fixed_of_nonzero_sources
  intro r hr
  obtain ⟨x, rfl⟩ := generatedSixth_xi_short_support_covered r hr
  obtain ⟨y, hm, hn⟩ := h x
  exact generatedSixth_xi_short_address_signed x y hm hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
