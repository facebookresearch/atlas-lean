/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLocalWord

/-! Triality coverage of the actual Octad family by the twelve-family catalogue, reduced to an
explicit octad-diagonal binding and an actual Octad-to-Odd transition.

The checked binary octad forest gives five roots. The Ω root has positive Octad and negative First
destinations. The other four roots are phase merged. The literal Fourth and Fifth words and an
Octad-to-Odd transition are genuine octad-family transitions with Fourth,
Fifth and Odd destinations; since local orbit lengths separate these classes from each other and
from the First and Octad classes, they occupy three distinct merged roots. The remaining merged
root is the octad-diagonal root, whose binding is the explicit hypothesis
`GeneratedAxisGlobalTwelveOctadDiagonalBound`. The Odd transition is the hypothesis
`GeneratedAxisGlobalTwelveOctadOddLink`, discharged from the odd root-six transport separately. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual local class of a vector. -/
abbrev generatedAxisGlobalTwelveOctadClass (y : GriessSpace) : generatedAxisLocalOrbitSpace :=
  Quotient.mk (MulAction.orbitRel H GriessSpace) y

/-- The octad-diagonal binding: some actual octad-family transition whose binary root lies in the
stabilizer orbit of the second forest root has the actual Octad destination. -/
def GeneratedAxisGlobalTwelveOctadDiagonalBound : Prop :=
  ∃ t c : H, c ∈ generatedOctadLocalAxisStabilizer 0 0 ∧
    generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot t) =
      generatedAxisGlobalTwelveOctadRootPoint 1 ∧
    generatedAxisGlobalTwelveOctadClass (sExtra (rhoLocal t (generatedOctadLocalAxis 0 0))) =
      generatedAxisGlobalTwelveOctadClass (generatedOctadLocalAxis 0 0)

/-- An actual octad-family transition with the actual Odd destination. -/
def GeneratedAxisGlobalTwelveOctadOddLink : Prop :=
  ∃ t : H, generatedAxisGlobalTwelveOctadClass
    (sExtra (rhoLocal t (generatedOctadLocalAxis 0 0))) =
      generatedAxisGlobalTwelveOctadClass generatedOddAxis

/-- Equal local classes have equal local orbit lengths. -/
theorem generatedAxisGlobalTwelveOctadClass_card {y a : GriessSpace}
    (h : generatedAxisGlobalTwelveOctadClass y = generatedAxisGlobalTwelveOctadClass a) :
    Nat.card (MulAction.orbit H y) = Nat.card (MulAction.orbit H a) := by
  have hm : y ∈ MulAction.orbit H a := MulAction.orbitRel_apply.mp (Quotient.exact h)
  rw [MulAction.orbit_eq_iff.mpr hm]

/-- A local transport preserves the local class. -/
theorem generatedAxisGlobalTwelveOctadClass_local (k : H) (y : GriessSpace) :
    generatedAxisGlobalTwelveOctadClass (rhoLocal k y) = generatedAxisGlobalTwelveOctadClass y :=
  (generatedAxis_local_class_eq_iff _ _).mpr ⟨k⁻¹, by
    rw [map_inv]
    exact LinearEquiv.symm_apply_apply _ _⟩

/-- The listed local orbit lengths of the First, Octad, Odd, Fourth and Fifth families. -/
theorem generatedAxisGlobalTwelveOctad_cards :
    Nat.card (MulAction.orbit H (conwayShortAxis (Sum.inl (0, 0)) 0)) = 196560 ∧
    Nat.card (MulAction.orbit H (generatedOctadLocalAxis 0 0)) = 11935123200 ∧
    Nat.card (MulAction.orbit H generatedOddAxis) = 1630347264000 ∧
    Nat.card (MulAction.orbit H generatedFourthAxis) = 1466587938816000 ∧
    Nat.card (MulAction.orbit H generatedFifthAxis) = 6599645724672000 :=
  ⟨generatedCountedAxisOrbit_card 0, generatedCountedAxisOrbit_card 1,
    generatedCountedAxisOrbit_card 2, generatedCountedAxisOrbit_card 3,
    generatedFifth_local_axis_orbit_card⟩

/-- The positive transition at a root. -/
abbrev generatedAxisGlobalTwelveOctadPositive (i : Fin 5) : GriessSpace :=
  sExtra (rhoLocal (generatedAxisGlobalTwelveOctadRootLocal i) (generatedOctadLocalAxis 0 0))

/-- The negative transition at a root. -/
abbrev generatedAxisGlobalTwelveOctadNegative (i : Fin 5) : GriessSpace :=
  sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveOctadRootLocal i) (generatedOctadLocalAxis 0 0))

/-- At every non-Ω root both triality signs have one local class. -/
theorem generatedAxisGlobalTwelveOctad_merged_class (i : Fin 5) (hi : i ≠ 0) :
    generatedAxisGlobalTwelveOctadClass (generatedAxisGlobalTwelveOctadNegative i) =
      generatedAxisGlobalTwelveOctadClass (generatedAxisGlobalTwelveOctadPositive i) := by
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelveOctad_merged_orbit j
  rw [generatedAxisGlobalTwelveOctadPositive, hk, generatedAxisGlobalTwelveOctadClass_local]

/-- The signed octad axis of the listed representative, before triality. -/
abbrev generatedAxisGlobalTwelveOctadShort : GriessSpace :=
  conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0

/-- The listed representative is the triality image of the signed octad axis. -/
theorem generatedAxisGlobalTwelveOctad_axis_eq :
    generatedOctadLocalAxis 0 0 = sExtra generatedAxisGlobalTwelveOctadShort := rfl

/-- The positive Ω transition has the actual Octad class. -/
theorem generatedAxisGlobalTwelveOctad_omega_positive :
    generatedAxisGlobalTwelveOctadClass (generatedAxisGlobalTwelveOctadPositive 0) =
      generatedAxisGlobalTwelveOctadClass (generatedOctadLocalAxis 0 0) := by
  have hr : generatedAxisGlobalTwelveOctadRootLocal 0 = 1 := by
    simp [generatedAxisGlobalTwelveOctadRootLocal]
  have hsq : sExtra (sExtra generatedAxisGlobalTwelveOctadShort) =
      sExtra⁻¹ generatedAxisGlobalTwelveOctadShort := by
    have h := sExtra_triple (sExtra⁻¹ generatedAxisGlobalTwelveOctadShort)
    change sExtra (sExtra (sExtra (sExtra.symm _))) = sExtra.symm _ at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have hx := generatedAxisGlobal_singleton_triality_exchange generatedAxisGlobalTwelveOctadShort
  have himg := generatedAxis_localFiber_image (localFiberIncl singletonCocodeQ)
    (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0
  have hp : griessShortPermutation (localFiberIncl singletonCocodeQ).val.2
      (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) =
        Sum.inr (Sum.inl (generatedOctadBasisOctad, 0)) := by
    change griessShortPermutation 1 _ = _
    rw [map_one]
    rfl
  rw [hp] at himg
  change rhoLocal (inclQ singletonCocodeQ) generatedAxisGlobalTwelveOctadShort = _ at himg
  rw [generatedAxisGlobalTwelveOctadPositive, hr, map_one, LinearEquiv.coe_one, id_eq,
    generatedAxisGlobalTwelveOctad_axis_eq, hsq]
  calc generatedAxisGlobalTwelveOctadClass (sExtra⁻¹ generatedAxisGlobalTwelveOctadShort)
      = generatedAxisGlobalTwelveOctadClass
          (rhoLocal (inclQ singletonCocodeQ) (sExtra⁻¹ generatedAxisGlobalTwelveOctadShort)) :=
        (generatedAxisGlobalTwelveOctadClass_local _ _).symm
    _ = generatedAxisOctadDestination := by
        rw [← hx, himg]
        exact (generatedAxis_triality_octad_class_iff _ _).mpr ⟨_, _, rfl⟩
    _ = _ := generatedAxisGlobalTwelve_octad_destination.symm

/-- The negative Ω transition is the signed octad axis, of the actual First class. -/
theorem generatedAxisGlobalTwelveOctad_omega_negative :
    generatedAxisGlobalTwelveOctadClass (generatedAxisGlobalTwelveOctadNegative 0) =
      generatedAxisGlobalTwelveOctadClass (conwayShortAxis (Sum.inl (0, 0)) 0) := by
  have hr : generatedAxisGlobalTwelveOctadRootLocal 0 = 1 := by
    simp [generatedAxisGlobalTwelveOctadRootLocal]
  rw [generatedAxisGlobalTwelveOctadNegative, hr, map_one, LinearEquiv.coe_one, id_eq,
    generatedAxisGlobalTwelveOctad_axis_eq]
  change generatedAxisGlobalTwelveOctadClass (sExtra.symm (sExtra _)) = _
  rw [LinearEquiv.symm_apply_apply]
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive (Sum.inl (0, 0))
    (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0 0
  change generatedAxisGlobalTwelveOctadClass
    (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0) = _
  rw [← hh]
  exact generatedAxisGlobalTwelveOctadClass_local _ _

/-- A transition with a class of orbit length other than First and Octad occupies a merged root. -/
theorem generatedAxisGlobalTwelveOctad_prototype_root (t : H) (a : GriessSpace)
    (hX : generatedAxisGlobalTwelveOctadClass (sExtra (rhoLocal t (generatedOctadLocalAxis 0 0))) =
      generatedAxisGlobalTwelveOctadClass a)
    (hfirst : Nat.card (MulAction.orbit H a) ≠ 196560)
    (hoctad : Nat.card (MulAction.orbit H a) ≠ 11935123200) :
    ∃ i : Fin 5, i ≠ 0 ∧
      generatedAxisGlobalTwelveOctadClass (generatedAxisGlobalTwelveOctadPositive i) =
        generatedAxisGlobalTwelveOctadClass a := by
  obtain ⟨i, ⟨k, hk⟩ | ⟨k, hk⟩⟩ := generatedAxisGlobalTwelveOctad_transition_root t
  · rw [hk, generatedAxisGlobalTwelveOctadClass_local] at hX
    by_cases hi : i = 0
    · subst hi
      exfalso
      apply hoctad
      rw [← generatedAxisGlobalTwelveOctadClass_card hX,
        generatedAxisGlobalTwelveOctadClass_card generatedAxisGlobalTwelveOctad_omega_positive]
      exact generatedAxisGlobalTwelveOctad_cards.2.1
    · exact ⟨i, hi, hX⟩
  · rw [hk, generatedAxisGlobalTwelveOctadClass_local] at hX
    by_cases hi : i = 0
    · subst hi
      exfalso
      apply hfirst
      rw [← generatedAxisGlobalTwelveOctadClass_card hX,
        generatedAxisGlobalTwelveOctadClass_card generatedAxisGlobalTwelveOctad_omega_negative]
      exact generatedAxisGlobalTwelveOctad_cards.1
    · exact ⟨i, hi, (generatedAxisGlobalTwelveOctad_merged_class i hi).symm.trans hX⟩

/-- A monomial octad move carries the listed axis to the triality image at the fourth octad. -/
theorem generatedAxisGlobalTwelveOctad_fourth_octad_move :
    ∃ k : H, rhoLocal k (generatedOctadLocalAxis 0 0) =
      sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0) := by
  obtain ⟨a, ha, hl⟩ := generatedAxis_octad_monomial_transitive generatedOctadBasisOctad
    generatedFourthOctad 0 0
  obtain ⟨n, hn⟩ := generatedAxis_monomial_signed_localOmega _ _ a ha hl 0 0
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit n generatedAxisGlobalTwelveOctadShort
  exact ⟨k, by rw [generatedAxisGlobalTwelveOctad_axis_eq, hk, hn]⟩

/-- The literal Fourth representative is an actual octad-family transition. -/
theorem generatedAxisGlobalTwelveOctad_fourth_prototype :
    ∃ t : H, sExtra (rhoLocal t (generatedOctadLocalAxis 0 0)) = generatedFourthAxis := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelveOctad_fourth_octad_move
  exact ⟨localFiberIntoH generatedFourthLocalFiber * k, by
    rw [map_mul, LinearEquiv.mul_apply, hk, generatedFourthAxis_local_expression]⟩

/-- The literal Fifth representative is an actual octad-family transition. -/
theorem generatedAxisGlobalTwelveOctad_fifth_prototype :
    ∃ t : H, sExtra (rhoLocal t (generatedOctadLocalAxis 0 0)) = generatedFifthAxis := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelveOctad_fourth_octad_move
  exact ⟨localFiberIntoH generatedFifthLocalFiber * k, by
    rw [map_mul, LinearEquiv.mul_apply, hk, generatedFifthAxis_local_expression]⟩

/-- Membership in the catalogue union from the class of a listed representative. -/
theorem generatedAxisGlobalTwelveOctad_mem_of_class {y : GriessSpace} (j : Fin 12)
    (hy : generatedAxisGlobalTwelveOctadClass y =
      generatedAxisGlobalTwelveOctadClass (generatedAxisGlobalTwelveRepresentative j)) :
    y ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_class j hy

/-- The finite pigeonhole step of the root elimination. -/
theorem generatedAxisGlobalTwelveOctad_pigeonhole : ∀ a b d i : Fin 5,
    a ≠ 0 → a ≠ 1 → b ≠ 0 → b ≠ 1 → d ≠ 0 → d ≠ 1 → a ≠ b → a ≠ d → b ≠ d →
      i ≠ 0 → i ≠ 1 → i = a ∨ i = b ∨ i = d := by
  decide

/-- Under the octad-diagonal binding, every actual Octad-family transition lies in the twelve-family
catalogue union. -/
theorem generatedAxisGlobalTwelve_octad_covered_of_links
    (hdiag : GeneratedAxisGlobalTwelveOctadDiagonalBound) (hodd : GeneratedAxisGlobalTwelveOctadOddLink) :
    GeneratedAxisGlobalTwelveFamilyCovered 1 := by
  have hcards := generatedAxisGlobalTwelveOctad_cards
  -- the octad-diagonal root has the Octad class
  have hdiagClass : generatedAxisGlobalTwelveOctadClass (generatedAxisGlobalTwelveOctadPositive 1) =
      generatedAxisGlobalTwelveOctadClass (generatedOctadLocalAxis 0 0) := by
    obtain ⟨t, c, hc, hroot, hcls⟩ := hdiag
    have hroot' : generatedAxisGlobalBinaryAct c⁻¹
        (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveOctadRootLocal 1)) =
          generatedAxisGlobalBinaryRoot t := by
      rw [generatedAxisGlobalTwelveOctadRootLocal_root, ← hroot, ← generatedAxisGlobalBinaryAct_mul,
        inv_mul_cancel]
      apply Subtype.ext
      change co1BinaryAction (projH 1) _ = _
      rw [map_one, map_one]
      rfl
    have hfix : rhoLocal c⁻¹ (generatedOctadLocalAxis 0 0) = generatedOctadLocalAxis 0 0 :=
      Subgroup.inv_mem _ hc
    rcases generatedAxisGlobal_triality_root_relation _ t _ c⁻¹ hfix hroot' with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk, generatedAxisGlobalTwelveOctadClass_local] at hcls
      exact hcls
    · rw [hk, generatedAxisGlobalTwelveOctadClass_local] at hcls
      exact (generatedAxisGlobalTwelveOctad_merged_class 1 (by decide)).symm.trans hcls
  -- three literal prototypes occupy three distinct merged roots
  obtain ⟨t4, ht4⟩ := generatedAxisGlobalTwelveOctad_fourth_prototype
  obtain ⟨t5, ht5⟩ := generatedAxisGlobalTwelveOctad_fifth_prototype
  obtain ⟨tod, hto⟩ := hodd
  obtain ⟨i4, hi4, hc4⟩ := generatedAxisGlobalTwelveOctad_prototype_root t4 generatedFourthAxis
    (by rw [ht4]) (by rw [hcards.2.2.2.1]; decide) (by rw [hcards.2.2.2.1]; decide)
  obtain ⟨i5, hi5, hc5⟩ := generatedAxisGlobalTwelveOctad_prototype_root t5 generatedFifthAxis
    (by rw [ht5]) (by rw [hcards.2.2.2.2]; decide) (by rw [hcards.2.2.2.2]; decide)
  obtain ⟨io, hio, hco⟩ := generatedAxisGlobalTwelveOctad_prototype_root tod generatedOddAxis
    hto (by rw [hcards.2.2.1]; decide) (by rw [hcards.2.2.1]; decide)
  have hne (i j : Fin 5) (a b : GriessSpace)
      (hia : generatedAxisGlobalTwelveOctadClass (generatedAxisGlobalTwelveOctadPositive i) =
        generatedAxisGlobalTwelveOctadClass a)
      (hjb : generatedAxisGlobalTwelveOctadClass (generatedAxisGlobalTwelveOctadPositive j) =
        generatedAxisGlobalTwelveOctadClass b)
      (hab : Nat.card (MulAction.orbit H a) ≠ Nat.card (MulAction.orbit H b)) : i ≠ j := by
    rintro rfl
    exact hab ((generatedAxisGlobalTwelveOctadClass_card hia).symm.trans
      (generatedAxisGlobalTwelveOctadClass_card hjb))
  have h41 := hne i4 1 _ _ hc4 hdiagClass (by rw [hcards.2.2.2.1, hcards.2.1]; decide)
  have h51 := hne i5 1 _ _ hc5 hdiagClass (by rw [hcards.2.2.2.2, hcards.2.1]; decide)
  have ho1 := hne io 1 _ _ hco hdiagClass (by rw [hcards.2.2.1, hcards.2.1]; decide)
  have h45 := hne i4 i5 _ _ hc4 hc5 (by rw [hcards.2.2.2.1, hcards.2.2.2.2]; decide)
  have h4o := hne i4 io _ _ hc4 hco (by rw [hcards.2.2.2.1, hcards.2.2.1]; decide)
  have h5o := hne i5 io _ _ hc5 hco (by rw [hcards.2.2.2.2, hcards.2.2.1]; decide)
  -- every positive root transition lies in the union
  have hpos : ∀ i : Fin 5, generatedAxisGlobalTwelveOctadPositive i ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      exact generatedAxisGlobalTwelveOctad_mem_of_class 1 generatedAxisGlobalTwelveOctad_omega_positive
    by_cases h1 : i = 1
    · subst h1
      exact generatedAxisGlobalTwelveOctad_mem_of_class 1 hdiagClass
    rcases generatedAxisGlobalTwelveOctad_pigeonhole i4 i5 io i hi4 h41 hi5 h51 hio ho1 h45 h4o h5o
      h0 h1 with rfl | rfl | rfl
    · exact generatedAxisGlobalTwelveOctad_mem_of_class 3 hc4
    · exact generatedAxisGlobalTwelveOctad_mem_of_class 4 hc5
    · exact generatedAxisGlobalTwelveOctad_mem_of_class 2 hco
  have hneg : ∀ i : Fin 5, generatedAxisGlobalTwelveOctadNegative i ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      exact generatedAxisGlobalTwelveOctad_mem_of_class 0 generatedAxisGlobalTwelveOctad_omega_negative
    · have hp := hpos i
      rw [generatedAxisGlobal_mem_union_iff] at hp ⊢
      obtain ⟨j, hj⟩ := hp
      exact ⟨j, (generatedAxisGlobalTwelveOctad_merged_class i h0).trans hj⟩
  intro h
  exact generatedAxisGlobalTwelveOctad_triality_of_actual_destinations _ hpos hneg h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
