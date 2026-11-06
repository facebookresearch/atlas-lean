/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthCoverage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPrototypeOrbits
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTrialityPhaseMerge
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQRootLower

/-! Reduction of the triality coverage of the actual Sixth family to twelve explicit vectors.

The checked Sixth singular forest reduces every Sixth transition to ten root words and both
triality signs. The identity root word is bound without computation: its inverse transition
is the literal Odd source of the Sixth prototype, and its positive transition is the inverse
Odd root-eight transition, which lies in the Sixth class. Six genuine extraspecial phase
merges identify both signs at six further roots. The twelve remaining vectors are explicit
hypotheses here; they are not asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual triality square is the inverse triality. -/
theorem generatedAxisGlobalTwelveSixth_triality_square (x : GriessSpace) :
    sExtra (sExtra x) = sExtra⁻¹ x := by
  have ht : sExtra * sExtra * sExtra = 1 := by
    simpa only [pow_succ, pow_zero, one_mul] using sExtra_pow_three
  have hs : sExtra * sExtra = sExtra⁻¹ := by
    calc
      sExtra * sExtra = (sExtra * sExtra * sExtra) * sExtra⁻¹ := by group
      _ = sExtra⁻¹ := by rw [ht, one_mul]
  exact LinearEquiv.congr_fun hs x

/-- The listed Odd representative is the actual Odd axis. -/
theorem generatedAxisGlobalTwelveSixth_rep_odd :
    generatedAxisGlobalTwelveRepresentative 2 = generatedOddAxis := rfl

/-- The listed Sixth representative is the actual Sixth axis. -/
theorem generatedAxisGlobalTwelveSixth_rep_sixth :
    generatedAxisGlobalTwelveRepresentative 5 = generatedSixthAxis := rfl

/-- The inverse transition at the identity root word is the literal Odd source. -/
theorem generatedAxisGlobalTwelveSixth_root00_negative :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSixthRootWord 0) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine generatedAxisGlobalTwelve_mem_of_transport 2
    (localFiberIntoH generatedSixthLocalFiber) ?_
  change sExtra⁻¹ (rhoLocal 1 generatedSixthAxis) = _
  rw [map_one, LinearEquiv.coe_one, id_eq, generatedSixthAxis_local_expression,
    generatedAxisGlobalTwelveSixth_rep_odd]
  exact LinearEquiv.symm_apply_apply _ _

/-- The inverse triality image of the literal Odd source of the Sixth prototype lies in the
actual Sixth class: it is an inverse Odd root-eight transition. -/
theorem generatedAxisGlobalTwelveSixth_odd_source_inverse :
    ∃ h : H, sExtra⁻¹ (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis) =
      rhoLocal h generatedSixthAxis := by
  let s : H := inclQ singletonCocodeQ
  have hs : s * s = 1 := by
    change inclQ singletonCocodeQ * inclQ singletonCocodeQ = 1
    rw [← map_mul]
    change inclQ (cocodeQ _ * cocodeQ _) = 1
    rw [cocodeQ_square, map_one]
  have hroot : generatedAxisGlobalBinaryRoot (s * generatedAxisGlobalOddPrototypeLocal 0) =
      generatedAxisGlobalBinaryRoot (generatedAxisGlobalOddPrototypeLocal 0) := by
    apply Subtype.ext
    change co1BinaryAction (projH (s * generatedAxisGlobalOddPrototypeLocal 0)⁻¹) _ =
      co1BinaryAction (projH (generatedAxisGlobalOddPrototypeLocal 0)⁻¹) _
    have hq : projH s = 1 := by
      have hk : s ∈ projH.ker := by
        rw [← inclQ_range_eq_projH_ker]
        exact ⟨singletonCocodeQ, rfl⟩
      exact hk
    rw [mul_inv_rev, map_mul, map_inv projH s, hq, inv_one, mul_one]
  have hfix : rhoLocal (generatedAxisGlobalOddPrototypeTransport 0).val generatedOddAxis =
      generatedOddAxis := (generatedAxisGlobalOddPrototypeTransport 0).property
  have hrel := generatedAxisGlobal_triality_root_relation generatedOddAxis
    (s * generatedAxisGlobalOddPrototypeLocal 0)
    (generatedAxisGlobalOddSourceRootLocalWord (generatedAxisGlobalOddPrototypeRootIndex 0))
    (generatedAxisGlobalOddPrototypeTransport 0).val hfix
    ((generatedAxisGlobalOddPrototypeTransport_actual 0).trans hroot.symm)
  have hex : sExtra (rhoLocal (s * generatedAxisGlobalOddPrototypeLocal 0) generatedOddAxis) =
      rhoLocal s (sExtra⁻¹
        (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)) := by
    rw [map_mul, LinearEquiv.mul_apply]
    exact generatedAxisGlobal_singleton_triality_exchange _
  have hback : ∀ y : GriessSpace, rhoLocal s (rhoLocal s y) = y := by
    intro y
    rw [← LinearEquiv.mul_apply, ← map_mul, hs, map_one]
    rfl
  rcases hrel with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨m, hm⟩ := generatedAxisGlobalOddPrototype_positive_orbit 0
    refine ⟨s * k * m, ?_⟩
    rw [← hback (sExtra⁻¹ _), ← hex, hk, hm]
    simp only [map_mul, LinearEquiv.mul_apply]
    rfl
  · obtain ⟨m, hm⟩ := generatedAxisGlobalOddPrototype_negative_orbit 0
    refine ⟨s * k * m, ?_⟩
    rw [← hback (sExtra⁻¹ _), ← hex, hk, hm]
    simp only [map_mul, LinearEquiv.mul_apply]
    rfl

/-- The positive transition at the identity root word lies in the actual Sixth class. -/
theorem generatedAxisGlobalTwelveSixth_root00_positive :
    sExtra (rhoLocal (generatedAxisGlobalTwelveSixthRootWord 0) generatedSixthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨h, hh⟩ := generatedAxisGlobalTwelveSixth_odd_source_inverse
  refine generatedAxisGlobalTwelve_mem_of_transport 5 h ?_
  change sExtra (rhoLocal 1 generatedSixthAxis) = _
  rw [map_one, LinearEquiv.coe_one, id_eq, generatedAxisGlobalTwelveSixth_rep_sixth]
  conv_lhs => rw [generatedSixthAxis_local_expression]
  rw [generatedAxisGlobalTwelveSixth_triality_square]
  exact hh

/-- The cocode index of the actual Sixth-axis Q fixer used at each merged root. -/
def generatedAxisGlobalTwelveSixthPhaseFixer (i : Fin 10) : Fin 4 :=
  if i = 6 then 1 else 2

set_option maxHeartbeats 4000000 in
-- Check the odd root pairings of the actual Q fixers at the six merged roots.
/-- The actual Sixth-axis Q fixers have odd pairing with the six merged root masks. -/
theorem generatedAxisGlobalTwelveSixthPhaseFixer_pairing : ∀ i : Fin 10,
    i ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 10)) →
      qBeta (binaryCocodeEmbedding
          (generatedSixthRootQModulation (generatedAxisGlobalTwelveSixthPhaseFixer i)))
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSixthLongRootMask i)) +
        qBeta (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSixthLongRootMask i))
          (binaryCocodeEmbedding
            (generatedSixthRootQModulation (generatedAxisGlobalTwelveSixthPhaseFixer i))) = 1 := by
  decide +kernel

/-- At the six merged roots both actual triality signs give the same local class. -/
theorem generatedAxisGlobalTwelveSixth_phase_merge (i : Fin 10)
    (hi : i ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 10))) :
    ∃ k : H, sExtra (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis) =
      rhoLocal k (sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i)
        generatedSixthAxis)) := by
  apply generatedAxisGlobal_triality_phase_merge generatedSixthAxis _
    (cocodeQ (generatedSixthRootQModulation (generatedAxisGlobalTwelveSixthPhaseFixer i)))
    (generatedSixth_root_Q_mem _)
  rw [generatedAxisGlobalTwelveSixthRootWord_root]
  exact generatedAxisGlobalTwelveSixthPhaseFixer_pairing i hi

/-- Root words whose positive transition is not yet bound to the catalogue. -/
def generatedAxisGlobalTwelveSixthOpenPositive : Finset (Fin 10) :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9}

/-- Root words whose inverse transition is neither bound nor phase merged. -/
def generatedAxisGlobalTwelveSixthOpenNegative : Finset (Fin 10) :=
  {1, 2, 8}

/-- Triality coverage of the actual Sixth family from the twelve open vectors. -/
theorem generatedAxisGlobalTwelve_sixth_covered_of
    (hpos : ∀ i ∈ generatedAxisGlobalTwelveSixthOpenPositive,
      sExtra (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ generatedAxisGlobalTwelveSixthOpenNegative,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 5 := by
  have hp : ∀ i : Fin 10,
      sExtra (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases h0 : i = 0
    · rw [h0]
      exact generatedAxisGlobalTwelveSixth_root00_positive
    · apply hpos
      fin_cases i <;> simp_all [generatedAxisGlobalTwelveSixthOpenPositive]
  have hn : ∀ i : Fin 10,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases h0 : i = 0
    · rw [h0]
      exact generatedAxisGlobalTwelveSixth_root00_negative
    by_cases hm : i ∈ ({3, 4, 5, 6, 7, 9} : Finset (Fin 10))
    · obtain ⟨k, hk⟩ := generatedAxisGlobalTwelveSixth_phase_merge i hm
      have he : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis) =
          rhoLocal k⁻¹
            (sExtra (rhoLocal (generatedAxisGlobalTwelveSixthRootWord i) generatedSixthAxis)) := by
        rw [hk, map_inv]
        exact (LinearEquiv.symm_apply_apply _ _).symm
      rw [he]
      exact generatedLocalOrbitUnion_local _ _ (hp i)
    · apply hneg
      fin_cases i <;> simp_all [generatedAxisGlobalTwelveSixthOpenNegative]
  intro h
  rw [generatedAxisGlobalTwelveSixth_rep_sixth]
  exact generatedAxisGlobalTwelveSixth_triality_of_actual_destinations _ hp hn h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
