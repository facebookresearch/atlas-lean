/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightPreparation

/-! Internal norm-eight transitivity in the actual coordinate E8 section. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual monomial and ξ generators reduce every section vector of norm eight
to +8e₀ while preserving the whole section in both directions. -/
theorem generatedStandardOctad_normEight_transitive (u : leechIntegral)
    (hs : leechSquareSum u.val = 64) (hu : generatedStandardOctadSupported u.val) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedStandardOctadPreserves e ∧
      (leechIntegralAction e u).val = Pi.single 0 8 := by
  have hmain : ∀ n : ℕ, ∀ s : Fin 8, leechNormEightShapeRank s = n →
      ∀ u : leechIntegral, leechSquareSum u.val = 64 →
        generatedStandardOctadSupported u.val →
        leechNormEightMultiplicity u.val = leechNormEightShapeCounts s →
        ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
          generatedStandardOctadPreserves e ∧
          (leechIntegralAction e u).val = Pi.single 0 8 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn u hs hu hshape
      by_cases hz : s = 0
      · subst s
        exact generatedStandardOctad_normEight_terminal u hs hu hshape
      · have hall : s = 0 ∨ s = 1 ∨ s = 2 := by
          have hc := generatedStandardOctad_zero_multiplicity u.val hu
          rw [hshape] at hc
          fin_cases s
          all_goals try simp
          all_goals norm_num [leechNormEightShapeCounts] at hc
        have hs12 : s = 1 ∨ s = 2 := hall.resolve_left hz
        obtain ⟨e, he, hep, hr⟩ :=
          generatedStandardOctad_normEight_preparation u s hshape hu hs12
        have hnorm : leechSquareSum (leechIntegralAction e u).val = 64 := by
          rw [leechIntegralAction_squareSum, hs]
        obtain ⟨t, ht, hlt⟩ := leechNormEightXi_prepared_rank
          (leechIntegralAction e u) s hnorm hz hr
        have hprep : generatedStandardOctadSupported (leechIntegralAction e u).val :=
          (hep u).mpr hu
        have hxi : generatedStandardOctadSupported
            (leechIntegralAction co1XiIsometry (leechIntegralAction e u)).val :=
          (generatedStandardOctadPreserves_xi _).mpr hprep
        have hnormxi : leechSquareSum
            (leechIntegralAction co1XiIsometry (leechIntegralAction e u)).val = 64 := by
          rw [leechIntegralAction_squareSum, hnorm]
        obtain ⟨f, hf, hfp, haxis⟩ := ih (leechNormEightShapeRank t) (by omega)
          t rfl _ hnormxi hxi ht
        refine ⟨f * (co1XiIsometry * e),
          leechConcreteGeneratorSubgroup.mul_mem hf
            (leechConcreteGeneratorSubgroup.mul_mem co1XiIsometry_mem_concrete he),
          generatedStandardOctadPreserves_mul _ _ hfp
            (generatedStandardOctadPreserves_mul _ _ generatedStandardOctadPreserves_xi hep), ?_⟩
        simpa only [map_mul, LinearEquiv.mul_apply] using haxis
  obtain ⟨s, hshape⟩ := leechNormEight_catalog u hs
  exact hmain (leechNormEightShapeRank s) s rfl u hs hu hshape

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
