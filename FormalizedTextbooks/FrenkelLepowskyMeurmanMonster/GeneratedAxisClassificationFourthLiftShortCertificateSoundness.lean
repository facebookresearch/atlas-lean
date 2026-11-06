/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFiniteSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOdd

/-! Complete soundness of finite preferred-Q coefficient checks for the original fourth axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Full actual short fixation follows from finite listed-octad and increasing-pair certificates. -/
theorem generatedFourth_lift_short_certificate_soundness
    (ho : ∀ j : Fin 63, ∀ e : Fin 64, generatedFourthLiftShortFiniteMatch
      (generatedFourthLiftShortSourceQ j e) (generatedFourthLiftShortOctadNumerator j e)
        (generatedFourthLiftShortOctadTargets j e))
    (hp : ∀ s : Fin 2, ∀ a b : Fin 24, a < b → generatedFourthLiftShortFiniteMatch
      (generatedFourthLiftShortPairQ s a b) (generatedFourthLiftShortPairNumerator s a b)
        (generatedFourthLiftShortPairTargets s a b)) :
    localShortOperator generatedFourthFlagCorrectedLift
      (griessConwayEncode generatedFourthAxis).2.1 =
        (griessConwayEncode generatedFourthAxis).2.1 := by
  apply generatedFourth_lift_short_fixed_of_q_matching
  intro r hr
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨d, i⟩
  · have hab := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
    change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hab
    apply generatedFourth_lift_short_finite_match_sound _
      (generatedFourthLiftShortPairQ s (griessCoordinatePair p).1 (griessCoordinatePair p).2)
      (generatedFourthLiftShortPairNumerator s
        (griessCoordinatePair p).1 (griessCoordinatePair p).2)
      (generatedFourthLiftShortPairTargets s
        (griessCoordinatePair p).1 (griessCoordinatePair p).2)
    · simpa only [griessPairIndex_pair] using generatedFourth_lift_short_pair_q s
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 hab
    · exact generatedFourth_lift_short_pair_numerator s p
    · exact hp s _ _ hab
    · exact hr
  · have hs : ∃ j : Fin 63, generatedFourthEvenRootOctad j = o := by
      by_contra h
      exact hr (generatedFourthQShortBasis_octad_zero_outside o e h)
    obtain ⟨j, rfl⟩ := hs
    exact generatedFourth_lift_short_finite_match_sound _
      (generatedFourthLiftShortSourceQ j e) (generatedFourthLiftShortOctadNumerator j e)
      (generatedFourthLiftShortOctadTargets j e)
      (generatedFourth_lift_short_source_q j e)
      (generatedFourth_lift_short_octad_numerator j e) (ho j e) hr
  · exact False.elim (hr (generatedFourthQShortBasis_odd_zero d i))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
