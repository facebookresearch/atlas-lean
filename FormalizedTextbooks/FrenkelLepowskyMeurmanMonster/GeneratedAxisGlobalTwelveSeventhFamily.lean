/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhCoverage
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthFamily
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPrototypeOrbits
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTrialityPhaseMerge
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQRootLower

/-! Reduction of the triality coverage of the actual Seventh family to 33 explicit vectors.

The checked Seventh singular forest reduces every Seventh transition to 23 root words and both
triality signs. The identity root word is bound without computation: its inverse transition
is the literal Odd source of the Seventh prototype, and its positive transition is the inverse
Odd root-seven transition, which lies in the Seventh class. Eleven genuine extraspecial phase
merges identify both signs at eleven further roots. The 33 remaining vectors are explicit
hypotheses here; they are not asserted. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The listed Seventh representative is the actual Seventh axis. -/
theorem generatedAxisGlobalTwelveSeventh_rep_seventh :
    generatedAxisGlobalTwelveRepresentative 6 = generatedSeventhAxis := rfl

/-- The inverse transition at the identity root word is the literal Odd source. -/
theorem generatedAxisGlobalTwelveSeventh_root00_negative :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord 0) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine generatedAxisGlobalTwelve_mem_of_transport 2
    (localFiberIntoH generatedSeventhLocalFiber) ?_
  change sExtra⁻¹ (rhoLocal 1 generatedSeventhAxis) = _
  rw [map_one, LinearEquiv.coe_one, id_eq, generatedSeventhAxis_local_expression,
    generatedAxisGlobalTwelveSixth_rep_odd]
  exact LinearEquiv.symm_apply_apply _ _

/-- The inverse triality image of the literal Odd source of the Seventh prototype lies in the
actual Seventh class: it is an inverse Odd root-seven transition. -/
theorem generatedAxisGlobalTwelveSeventh_odd_source_inverse :
    ∃ h : H, sExtra⁻¹ (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis) =
      rhoLocal h generatedSeventhAxis := by
  let s : H := inclQ singletonCocodeQ
  have hs : s * s = 1 := by
    change inclQ singletonCocodeQ * inclQ singletonCocodeQ = 1
    rw [← map_mul]
    change inclQ (cocodeQ _ * cocodeQ _) = 1
    rw [cocodeQ_square, map_one]
  have hroot : generatedAxisGlobalBinaryRoot (s * generatedAxisGlobalOddPrototypeLocal 1) =
      generatedAxisGlobalBinaryRoot (generatedAxisGlobalOddPrototypeLocal 1) := by
    apply Subtype.ext
    change co1BinaryAction (projH (s * generatedAxisGlobalOddPrototypeLocal 1)⁻¹) _ =
      co1BinaryAction (projH (generatedAxisGlobalOddPrototypeLocal 1)⁻¹) _
    have hq : projH s = 1 := by
      have hk : s ∈ projH.ker := by
        rw [← inclQ_range_eq_projH_ker]
        exact ⟨singletonCocodeQ, rfl⟩
      exact hk
    rw [mul_inv_rev, map_mul, map_inv projH s, hq, inv_one, mul_one]
  have hfix : rhoLocal (generatedAxisGlobalOddPrototypeTransport 1).val generatedOddAxis =
      generatedOddAxis := (generatedAxisGlobalOddPrototypeTransport 1).property
  have hrel := generatedAxisGlobal_triality_root_relation generatedOddAxis
    (s * generatedAxisGlobalOddPrototypeLocal 1)
    (generatedAxisGlobalOddSourceRootLocalWord (generatedAxisGlobalOddPrototypeRootIndex 1))
    (generatedAxisGlobalOddPrototypeTransport 1).val hfix
    ((generatedAxisGlobalOddPrototypeTransport_actual 1).trans hroot.symm)
  have hex : sExtra (rhoLocal (s * generatedAxisGlobalOddPrototypeLocal 1) generatedOddAxis) =
      rhoLocal s (sExtra⁻¹
        (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)) := by
    rw [map_mul, LinearEquiv.mul_apply]
    exact generatedAxisGlobal_singleton_triality_exchange _
  have hback : ∀ y : GriessSpace, rhoLocal s (rhoLocal s y) = y := by
    intro y
    rw [← LinearEquiv.mul_apply, ← map_mul, hs, map_one]
    rfl
  rcases hrel with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨m, hm⟩ := generatedAxisGlobalOddPrototype_positive_orbit 1
    refine ⟨s * k * m, ?_⟩
    rw [← hback (sExtra⁻¹ _), ← hex, hk, hm]
    simp only [map_mul, LinearEquiv.mul_apply]
    rfl
  · obtain ⟨m, hm⟩ := generatedAxisGlobalOddPrototype_negative_orbit 1
    refine ⟨s * k * m, ?_⟩
    rw [← hback (sExtra⁻¹ _), ← hex, hk, hm]
    simp only [map_mul, LinearEquiv.mul_apply]
    rfl

/-- The positive transition at the identity root word lies in the actual Seventh class. -/
theorem generatedAxisGlobalTwelveSeventh_root00_positive :
    sExtra (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord 0) generatedSeventhAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨h, hh⟩ := generatedAxisGlobalTwelveSeventh_odd_source_inverse
  refine generatedAxisGlobalTwelve_mem_of_transport 6 h ?_
  change sExtra (rhoLocal 1 generatedSeventhAxis) = _
  rw [map_one, LinearEquiv.coe_one, id_eq, generatedAxisGlobalTwelveSeventh_rep_seventh]
  conv_lhs => rw [generatedSeventhAxis_local_expression]
  rw [generatedAxisGlobalTwelveSixth_triality_square]
  exact hh

/-- The cocode index of the actual Seventh-axis Q fixer used at each merged root. -/
def generatedAxisGlobalTwelveSeventhPhaseFixer (i : Fin 23) : Fin 4 :=
  if i = 7 ∨ i = 16 then 1 else 2

set_option maxHeartbeats 4000000 in
-- Check the odd root pairings of the actual Q fixers at the eleven merged roots.
/-- The actual Seventh-axis Q fixers have odd pairing with the eleven merged root masks. -/
theorem generatedAxisGlobalTwelveSeventhPhaseFixer_pairing : ∀ i : Fin 23,
    i ∈ ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23)) →
      qBeta (binaryCocodeEmbedding
          (generatedSeventhRootQModulation (generatedAxisGlobalTwelveSeventhPhaseFixer i)))
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSeventhLongRootMask i)) +
        qBeta (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveSeventhLongRootMask i))
          (binaryCocodeEmbedding
            (generatedSeventhRootQModulation
              (generatedAxisGlobalTwelveSeventhPhaseFixer i))) = 1 := by
  decide +kernel

/-- At the eleven merged roots both actual triality signs give the same local class. -/
theorem generatedAxisGlobalTwelveSeventh_phase_merge (i : Fin 23)
    (hi : i ∈ ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23))) :
    ∃ k : H, sExtra (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis) =
      rhoLocal k (sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i)
        generatedSeventhAxis)) := by
  apply generatedAxisGlobal_triality_phase_merge generatedSeventhAxis _
    (cocodeQ (generatedSeventhRootQModulation (generatedAxisGlobalTwelveSeventhPhaseFixer i)))
    (generatedSeventh_root_Q_mem _)
  rw [generatedAxisGlobalTwelveSeventhRootWord_root]
  exact generatedAxisGlobalTwelveSeventhPhaseFixer_pairing i hi

/-- Root words whose positive transition is not yet bound to the catalogue. -/
def generatedAxisGlobalTwelveSeventhOpenPositive : Finset (Fin 23) :=
  Finset.univ.erase 0

/-- Root words whose inverse transition is neither bound nor phase merged. -/
def generatedAxisGlobalTwelveSeventhOpenNegative : Finset (Fin 23) :=
  {1, 2, 3, 10, 11, 12, 17, 18, 20, 21, 22}

/-- Triality coverage of the actual Seventh family from the 33 open vectors. -/
theorem generatedAxisGlobalTwelve_seventh_covered_of
    (hpos : ∀ i ∈ generatedAxisGlobalTwelveSeventhOpenPositive,
      sExtra (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ i ∈ generatedAxisGlobalTwelveSeventhOpenNegative,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 6 := by
  have hp : ∀ i : Fin 23,
      sExtra (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases h0 : i = 0
    · rw [h0]
      exact generatedAxisGlobalTwelveSeventh_root00_positive
    · exact hpos i (Finset.mem_erase.mpr ⟨h0, Finset.mem_univ _⟩)
  have hn : ∀ i : Fin 23,
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases h0 : i = 0
    · rw [h0]
      exact generatedAxisGlobalTwelveSeventh_root00_negative
    by_cases hm : i ∈ ({4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 19} : Finset (Fin 23))
    · obtain ⟨k, hk⟩ := generatedAxisGlobalTwelveSeventh_phase_merge i hm
      have he : sExtra⁻¹
          (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis) =
          rhoLocal k⁻¹ (sExtra
            (rhoLocal (generatedAxisGlobalTwelveSeventhRootWord i) generatedSeventhAxis)) := by
        rw [hk, map_inv]
        exact (LinearEquiv.symm_apply_apply _ _).symm
      rw [he]
      exact generatedLocalOrbitUnion_local _ _ (hp i)
    · apply hneg
      fin_cases i <;> simp_all [generatedAxisGlobalTwelveSeventhOpenNegative]
  intro h
  rw [generatedAxisGlobalTwelveSeventh_rep_seventh]
  exact generatedAxisGlobalTwelveSeventh_triality_of_actual_destinations _ hp hn h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
