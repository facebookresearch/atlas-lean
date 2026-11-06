/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOdd
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All seven genuine basis elements fix every supported actual octad-short coefficient. -/
theorem generatedFourthQShortBasis_octad_fixed (i : Fin 7) (o : Fin 759) (e : Fin 64)
    (hr : (griessConwayEncode generatedFourthAxis).2.1 (Sum.inr (Sum.inl (o, e))) ≠ 0) :
    localAxisQPhase (Sum.inr (Sum.inl (o, e))) (generatedFourthQAffineParameterBasis i) = 1 := by
  have ho : ∃ j : Fin 63, generatedFourthEvenRootOctad j = o := by
    by_contra ho
    exact hr (generatedFourthQShortBasis_octad_zero_outside o e ho)
  obtain ⟨j, rfl⟩ := ho
  apply Multiplicative.toAdd.injective
  rw [generatedFourthQShortBasis_octad_phase_actual]
  change generatedFourthQShortBasisOctadPhase i j e = 0
  by_contra h
  have hz := generatedFourthQShortBasis_octad_zero_certificate i j e h
  apply hr
  rw [generatedFourthQShortBasis_octad_coordinate, generatedFourthEvenRootOctad_label,
    hz, Int.cast_zero, zero_div]

/-- Every genuine seven-basis element fixes the entire original short block of the fourth axis. -/
theorem generatedFourthQShortBasis_short_fixed (i : Fin 7) :
    localShortOperator (localFiberIncl (generatedFourthQAffineParameterBasis i))
      (griessConwayEncode generatedFourthAxis).2.1 =
        (griessConwayEncode generatedFourthAxis).2.1 := by
  apply (generatedFourthQ_short_fixed_iff _ _).mpr
  rintro (⟨s, p⟩ | ⟨o, e⟩ | ⟨d, j⟩) hr
  · exact generatedFourthQShortBasis_pair_fixed i s p hr
  · exact generatedFourthQShortBasis_octad_fixed i o e hr
  · exact False.elim (hr (generatedFourthQShortBasis_odd_zero d j))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
