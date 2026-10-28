/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! # Triality triangles of the Fourth roots

Triality has order three, so the inverse triality image of a vector is the forward image of its
forward image.  If the forward image of a Fourth root vector lies in the local orbit of a family
whose coverage is known, the inverse image lies in the union of the twelve local orbits.  This
replaces the second identification at an unmerged root by the coverage of the family of the first
one (for example root twelve: the forward image is Odd-class, and the Odd family is covered).

`generatedAxisGlobalTwelve_fourth_covered_of_idents_odd` is the assembly with this replacement at
root twelve: the Fourth-class identification at the translated pair representative of root twelve
is replaced by the coverage of the Odd family.  Coverage of other families enters only as a
hypothesis; nothing is asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The inverse triality image is the forward image of the forward image. -/
theorem fourth_sExtra_inv_eq (x : GriessSpace) : sExtra⁻¹ x = sExtra (sExtra x) := by
  rw [LinearEquiv.coe_inv]
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, sExtra_triple]

/-- If the forward image of a vector lies in the orbit of a covered family, its inverse image
lies in the union of the twelve local orbits. -/
theorem fourth_triangle_inverse (x : GriessSpace) (k : Fin 12)
    (hx : sExtra x ∈ MulAction.orbit H (generatedAxisGlobalTwelveRepresentative k))
    (hk : GeneratedAxisGlobalTwelveFamilyCovered k) :
    sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨g, hg⟩ := hx
  rw [fourth_sExtra_inv_eq, ← hg]
  exact hk g

/-- A forward identification at a translated root word and the coverage of the identified family
bind both images of the root. -/
theorem fourth_root_pair_of_forward_covered (j : Fin 16) (k : Fin 12) (g : H)
    (hid : sExtra (rhoLocal (identWordLocal
      (fourthSourceWord (generatedAxisGlobalTwelveFourthRootWords j)))
        (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative k))
    (hk : GeneratedAxisGlobalTwelveFamilyCovered k) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal j) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal j) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have ho := fourth_forward_orbit (generatedAxisGlobalTwelveFourthRootWords j) k g hid
  exact ⟨fourth_mem_union_of_orbit ho, fourth_triangle_inverse _ k ho hk⟩

/-- Fourth-family coverage with the Odd family covering the inverse image at root twelve. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of_idents_odd
    (h3 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 3))
    (h4 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 4))
    (h6 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 6))
    (h7 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 7))
    (h9 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 9))
    (h10 : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 10))
    (h14p : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords 14))
    (h14n : FourthIdentInverse (generatedAxisGlobalTwelveFourthRootWords 14))
    (h2 : FourthIdentInverse (generatedAxisGlobalTwelveFourthSelfWord 0))
    (h13 : FourthIdentInverse (generatedAxisGlobalTwelveFourthSelfWord 1))
    (h15 : FourthSelfInverse (generatedAxisGlobalTwelveFourthSelfWord 2))
    (h1 : FourthSelfForward (generatedAxisGlobalTwelveFourthPairWord 0))
    (p0 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 0) (generatedAxisGlobalTwelveRepresentative i))
    (p1 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧
      FourthPartner n (fourthPartnerWord 1) (generatedAxisGlobalTwelveRepresentative 4))
    (p5 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 2) (generatedAxisGlobalTwelveRepresentative i))
    (p8 : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
      FourthPartner n (fourthPartnerWord 3) (generatedAxisGlobalTwelveRepresentative i))
    (hodd12 : sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis)
    (hodd15 : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15)
      generatedFourthAxis) ∈ MulAction.orbit H generatedOddAxis)
    (hoddc : GeneratedAxisGlobalTwelveFamilyCovered 2) :
    GeneratedAxisGlobalTwelveFamilyCovered 3 := by
  have hodd_mem : ∀ {x : GriessSpace}, x ∈ MulAction.orbit H generatedOddAxis →
      x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
    fun hx => fourth_mem_union_of_orbit (k := 2) hx
  obtain ⟨n0, hn0, i0, q0⟩ := p0
  obtain ⟨n1, hn1, q1⟩ := p1
  obtain ⟨n5, hn5, i5, q5⟩ := p5
  obtain ⟨n8, hn8, i8, q8⟩ := p8
  have c0 := fourthPartner_certificate 0
  have c1 := fourthPartner_certificate 1
  have c5 := fourthPartner_certificate 2
  have c8 := fourthPartner_certificate 3
  have r0 := fourth_partner_merged 0 n0 hn0 _ _ c0.1 _ c0.2 i0 q0
  have r5 := fourth_partner_merged 4 n5 hn5 _ _ c5.1 _ c5.2 i5 q5
  have r8 := fourth_partner_merged 7 n8 hn8 _ _ c8.1 _ c8.2 i8 q8
  have r1 := generatedAxisGlobalTwelveFourth_root1_of_classes (fourth_root1_fourth_of_ident h1)
    (fourth_partner_orbit 1 n1 hn1 _ _ c1.1 _ c1.2 _ q1)
  have r2 := fourth_root2_of_ident h2
  have r13 := fourth_root13_of_ident h13
  have r3 := fourth_merged_forward 2 h3
  have r4 := fourth_merged_forward 3 h4
  have r6 := fourth_merged_forward 5 h6
  have r7 := fourth_merged_forward 6 h7
  have r9 := fourth_merged_forward 8 h9
  have r10 := fourth_merged_forward 9 h10
  have r14p := fourth_root_forward 14 h14p
  have r14n := fourth_root_inverse 14 h14n
  have r12n := fourth_triangle_inverse _ 2 hodd12 hoddc
  have r15p := fourth_root15_of_ident h15 hodd15
  apply generatedAxisGlobalTwelve_fourth_covered_of_open
  · intro i hi
    simp only [generatedAxisGlobalTwelveFourthOpenPositive, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact r0.1
    · exact r1.1
    · exact r2.1
    · exact r3.1
    · exact r4.1
    · exact r5.1
    · exact r6.1
    · exact r7.1
    · exact r8.1
    · exact r9.1
    · exact r10.1
    · exact hodd_mem hodd12
    · exact r13.1
    · exact r14p
    · exact r15p
  · intro i hi
    simp only [generatedAxisGlobalTwelveFourthOpenNegative, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact r1.2
    · exact r12n
    · exact r14n
    · exact hodd_mem hodd15

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
