/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthBindPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightFrame

/-! # Fourth identifications in the packed-identification alphabet

Each odd source letter is written as a word of `IdentLetter`s: Xi, the code signs `16` and `32`
and the four permutation letters exactly, the inverse Xi as Xi twice (Xi has cube one), and the
inverse code signs as the code signs themselves.  The code signs `16` and `32` are octad signs, so
their extraspecial square is trivial and they act on the Griess space as involutions
(`fourth_sign_rhoLocal_inv`).  Hence every translated source word acts on the Griess space
exactly as the original word (`fourthSourceWord_rhoLocal`) and has its binary root
(`fourthSourceWord_binaryRoot`).

The wrappers turn whole-vector identifications at translated words (the equations produced by
`ident_forward_packed` / `ident_inverse_packed`) into the root memberships required by
`generatedAxisGlobalTwelve_fourth_covered_of_open`, and
`generatedAxisGlobalTwelve_fourth_covered_of_idents` assembles Fourth-family coverage from the
identification statements alone (with the two Odd-class memberships of roots twelve and fifteen
as hypotheses).  No identification is asserted in this module. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
open scoped Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! ## Translation of source letters -/

/-- The identification-alphabet word of an odd source letter. -/
def fourthSourceIdent : Fin 10 → List IdentLetter :=
  ![[.xi], [.xi, .xi], [.sign 16 0], [.sign 16 0], [.sign 32 0], [.sign 32 0],
    [.mono (0, false)], [.mono (0, true)], [.mono (1, false)], [.mono (1, true)]]

/-- The identification-alphabet word of an odd source word. -/
def fourthSourceWord (ls : List (Fin 10)) : List IdentLetter := ls.flatMap fourthSourceIdent

/-- A translated word has the product of the translated letters as local element. -/
theorem fourthSourceWord_local (ls : List (Fin 10)) :
    identWordLocal (fourthSourceWord ls) =
      (ls.map fun l => identWordLocal (fourthSourceIdent l)).prod := by
  unfold fourthSourceWord
  induction ls with
  | nil => simp [identWordLocal, identWordFiber]
  | cons l ls ih =>
    rw [List.flatMap_cons, identWordLocal_append, ih, List.map_cons, List.prod_cons]

/-- The local Xi has cube one. -/
theorem fourth_xi_sq :
    localFiberIntoH xiSpinLocalFiber * localFiberIntoH xiSpinLocalFiber =
      (localFiberIntoH xiSpinLocalFiber)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, show xiSpinLocalFiber * xiSpinLocalFiber * xiSpinLocalFiber =
    xiSpinLocalFiber ^ 3 by rw [pow_three, mul_assoc], xiSpinLocalFiber_cube, map_one]

/-- A source code sign whose code has even quarter weight acts as an involution. -/
theorem fourth_sign_rhoLocal_inv (a : Fin 4096)
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) :
    rhoLocal (generatedFifthSignLocal a 0)⁻¹ = rhoLocal (generatedFifthSignLocal a 0) := by
  have hq : rhoLocal (inclQ (sourceQCode a 0)) * rhoLocal (inclQ (sourceQCode a 0)) = 1 := by
    rw [← map_mul, ← map_mul, ← pow_two, sourceQCode_square, ha]
    have h0 : qCentral 0 = 1 := rfl
    rw [h0, map_one, map_one]
  have hsq : rhoLocal (generatedFifthSignLocal a 0) * rhoLocal (generatedFifthSignLocal a 0) =
      1 := by
    apply LinearEquiv.ext
    intro x
    have hx : rhoLocal (inclQ (sourceQCode a 0)) (rhoLocal (inclQ (sourceQCode a 0))
        (sExtra x)) = sExtra x := by
      rw [← LinearEquiv.mul_apply, hq, LinearEquiv.coe_one, id_eq]
    rw [LinearEquiv.mul_apply, generatedFifth_sign_local_apply, generatedFifth_sign_local_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, hx, LinearEquiv.symm_apply_apply,
      LinearEquiv.coe_one, id_eq]
  rw [map_inv]
  exact inv_eq_of_mul_eq_one_right hsq

set_option maxRecDepth 20000 in
/-- Each translated letter acts on the Griess space as the original source letter. -/
theorem fourthSourceIdent_rhoLocal (l : Fin 10) :
    rhoLocal (generatedAxisGlobalOddSourceLocalLetter l) =
      rhoLocal (identWordLocal (fourthSourceIdent l)) := by
  rw [← generatedAxisGlobalOddSourceFiberLetter_local]
  fin_cases l
  · rfl
  · change rhoLocal (localFiberIntoH xiSpinLocalFiber⁻¹) =
      rhoLocal (localFiberIntoH (xiSpinLocalFiber * xiSpinLocalFiber))
    rw [map_mul, fourth_xi_sq, map_inv]
  · rfl
  · change rhoLocal (localFiberIntoH (generatedFifthSignFiber 16 0)⁻¹) =
      rhoLocal (localFiberIntoH (generatedFifthSignFiber 16 0))
    rw [map_inv, generatedFifth_sign_fiber_local, fourth_sign_rhoLocal_inv 16 (by decide +kernel)]
  · rfl
  · change rhoLocal (localFiberIntoH (generatedFifthSignFiber 32 0)⁻¹) =
      rhoLocal (localFiberIntoH (generatedFifthSignFiber 32 0))
    rw [map_inv, generatedFifth_sign_fiber_local, fourth_sign_rhoLocal_inv 32 (by decide +kernel)]
  · rfl
  · rfl
  · rfl
  · rfl

/-- Every translated source word acts on the Griess space as the original word. -/
theorem fourthSourceWord_rhoLocal (ls : List (Fin 10)) :
    rhoLocal ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod) =
      rhoLocal (identWordLocal (fourthSourceWord ls)) := by
  rw [fourthSourceWord_local, map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  exact fourthSourceIdent_rhoLocal l

/-- Every Golay sign isometry is an involution. -/
theorem fourth_golaySign_sq (d : golayCode) :
    golaySignIsometry d * golaySignIsometry d = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  change golayRealSign d.val (golayRealSign d.val x) i = x i
  rw [golayRealSign_apply, golayRealSign_apply, ← mul_assoc, qSign_sq]
  exact one_mul _

/-- The projection of a source code sign letter is an involution. -/
theorem fourth_sign_projection_inv (a : Fin 4096) :
    (projH (generatedFifthSignLocal a 0))⁻¹ = projH (generatedFifthSignLocal a 0) := by
  rw [generatedFifth_sign_local_projection, ← QuotientGroup.mk_inv,
    inv_eq_of_mul_eq_one_left (fourth_golaySign_sq _)]

set_option maxRecDepth 20000 in
/-- Each translated letter has the Conway projection of the original source letter. -/
theorem fourthSourceIdent_projection (l : Fin 10) :
    projH (identWordLocal (fourthSourceIdent l)) =
      projH (generatedAxisGlobalOddSourceLocalLetter l) := by
  rw [← generatedAxisGlobalOddSourceFiberLetter_local]
  fin_cases l
  · rfl
  · change projH (localFiberIntoH (xiSpinLocalFiber * xiSpinLocalFiber)) =
      projH (localFiberIntoH xiSpinLocalFiber⁻¹)
    rw [map_mul, fourth_xi_sq]
    simp only [map_inv]
  · rfl
  · change projH (localFiberIntoH (generatedFifthSignFiber 16 0)) =
      projH (localFiberIntoH (generatedFifthSignFiber 16 0)⁻¹)
    rw [map_inv, map_inv, generatedFifth_sign_fiber_local, fourth_sign_projection_inv]
  · rfl
  · change projH (localFiberIntoH (generatedFifthSignFiber 32 0)) =
      projH (localFiberIntoH (generatedFifthSignFiber 32 0)⁻¹)
    rw [map_inv, map_inv, generatedFifth_sign_fiber_local, fourth_sign_projection_inv]
  · rfl
  · rfl
  · rfl
  · rfl

/-- Every translated source word has the Conway projection of the original word. -/
theorem fourthSourceWord_projection (ls : List (Fin 10)) :
    projH (identWordLocal (fourthSourceWord ls)) =
      projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod) := by
  rw [fourthSourceWord_local, map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  exact fourthSourceIdent_projection l

/-- Every translated source word has the actual binary root of the original word. -/
theorem fourthSourceWord_binaryRoot (ls : List (Fin 10)) :
    generatedAxisGlobalBinaryRoot (identWordLocal (fourthSourceWord ls)) =
      generatedAxisGlobalBinaryRoot ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod) := by
  apply Subtype.ext
  change co1BinaryAction (projH (identWordLocal (fourthSourceWord ls))⁻¹)
      (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
    co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod)⁻¹)
      (Multiplicative.toAdd (qQuotHom sourceOmegaQ))
  simp only [map_inv]
  rw [fourthSourceWord_projection]

/-! ## Identifications at translated words -/

/-- The translated word of a source word applied to the Fourth axis. -/
theorem fourthSourceWord_apply (ls : List (Fin 10)) :
    rhoLocal ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod) generatedFourthAxis =
      rhoLocal (identWordLocal (fourthSourceWord ls))
        (generatedAxisGlobalTwelveRepresentative 3) := by
  rw [fourthSourceWord_rhoLocal]
  rfl

/-- A forward identification at a translated word places the forward image of the source word in
the identified local orbit. -/
theorem fourth_forward_orbit (ls : List (Fin 10)) (k : Fin 12) (g : H)
    (hid : sExtra (rhoLocal (identWordLocal (fourthSourceWord ls))
      (generatedAxisGlobalTwelveRepresentative 3)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative k)) :
    sExtra (rhoLocal ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod) generatedFourthAxis) ∈
      MulAction.orbit H (generatedAxisGlobalTwelveRepresentative k) := by
  rw [fourthSourceWord_apply, hid]
  exact ⟨g, rfl⟩

/-- An inverse identification at a translated word places the inverse image of the source word in
the identified local orbit. -/
theorem fourth_inverse_orbit (ls : List (Fin 10)) (k : Fin 12) (g : H)
    (hid : sExtra.symm (rhoLocal (identWordLocal (fourthSourceWord ls))
      (generatedAxisGlobalTwelveRepresentative 3)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative k)) :
    sExtra⁻¹ (rhoLocal ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod)
      generatedFourthAxis) ∈ MulAction.orbit H (generatedAxisGlobalTwelveRepresentative k) := by
  rw [fourthSourceWord_apply, LinearEquiv.coe_inv, hid]
  exact ⟨g, rfl⟩

/-- Orbit membership gives union membership. -/
theorem fourth_mem_union_of_orbit {x : GriessSpace} {k : Fin 12}
    (hx : x ∈ MulAction.orbit H (generatedAxisGlobalTwelveRepresentative k)) :
    x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨g, hg⟩ := hx
  exact generatedAxisGlobalTwelve_mem_of_transport k g hg.symm

/-- A forward identification at the translated word of a source word, into any family. -/
def FourthIdentForward (ls : List (Fin 10)) : Prop :=
  ∃ (k : Fin 12) (g : H), sExtra (rhoLocal (identWordLocal (fourthSourceWord ls))
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative k)

/-- An inverse identification at the translated word of a source word, into any family. -/
def FourthIdentInverse (ls : List (Fin 10)) : Prop :=
  ∃ (k : Fin 12) (g : H), sExtra.symm (rhoLocal (identWordLocal (fourthSourceWord ls))
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative k)

/-- A forward identification at a translated word gives union membership. -/
theorem fourth_forward_mem (ls : List (Fin 10)) (h : FourthIdentForward ls) :
    sExtra (rhoLocal ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, g, hid⟩ := h
  exact fourth_mem_union_of_orbit (fourth_forward_orbit ls k g hid)

/-- An inverse identification at a translated word gives union membership. -/
theorem fourth_inverse_mem (ls : List (Fin 10)) (h : FourthIdentInverse ls) :
    sExtra⁻¹ (rhoLocal ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod)
      generatedFourthAxis) ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, g, hid⟩ := h
  exact fourth_mem_union_of_orbit (fourth_inverse_orbit ls k g hid)

/-- A forward identification at the translated root word binds the forward image of the root. -/
theorem fourth_root_forward (j : Fin 16)
    (h : FourthIdentForward (generatedAxisGlobalTwelveFourthRootWords j)) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal j) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_forward_mem _ h

/-- An inverse identification at the translated root word binds the inverse image of the root. -/
theorem fourth_root_inverse (j : Fin 16)
    (h : FourthIdentInverse (generatedAxisGlobalTwelveFourthRootWords j)) :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal j) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_inverse_mem _ h

/-- At a phase-merged root, a forward identification at the translated root word binds both
images. -/
theorem fourth_merged_forward (j : Fin 11)
    (h : FourthIdentForward
      (generatedAxisGlobalTwelveFourthRootWords (generatedAxisGlobalTwelveFourthMergedRoot j))) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨fourth_root_forward _ h,
    generatedAxisGlobalTwelveFourthMerged_negative_of_positive _ j (fourth_root_forward _ h)⟩

/-! ## Self identifications (Fourth-class images at one-xi representatives) -/

/-- An inverse identification at the translated representative of a merged self root binds both
images of the root. -/
theorem fourth_self_merged (i : Fin 3) (j : Fin 11)
    (hj : generatedAxisGlobalTwelveFourthMergedRoot j = generatedAxisGlobalTwelveFourthSelfRoot i)
    (h : FourthIdentInverse (generatedAxisGlobalTwelveFourthSelfWord i)) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hk := fourth_inverse_mem _ h
  have hroot := generatedAxisGlobalTwelveFourthSelf_relation i
  rw [← hj] at hroot
  have hpos := generatedAxisGlobalTwelveFourth_reverse_merged
    generatedAxisGlobalTwelveRepresentative j (generatedAxisGlobalTwelveFourthSelfLocal i)
    (generatedAxisGlobalTwelveFourthGeneratorWord (generatedAxisGlobalTwelveFourthSelfPath i))
    (generatedAxisGlobalTwelveFourthGeneratorWord_mem _) hroot (Or.inr hk)
  exact ⟨hpos, generatedAxisGlobalTwelveFourthMerged_negative_of_positive _ j hpos⟩

/-- Root two from the inverse self identification at its translated representative. -/
theorem fourth_root2_of_ident
    (h : FourthIdentInverse (generatedAxisGlobalTwelveFourthSelfWord 0)) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 2) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 2) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_self_merged 0 1 rfl h

/-- Root thirteen from the inverse self identification at its translated representative. -/
theorem fourth_root13_of_ident
    (h : FourthIdentInverse (generatedAxisGlobalTwelveFourthSelfWord 1)) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 13) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 13) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  fourth_self_merged 1 10 rfl h

/-- A Fourth-class identification at the translated word of a source word. -/
def FourthSelfForward (ls : List (Fin 10)) : Prop :=
  ∃ g : H, sExtra (rhoLocal (identWordLocal (fourthSourceWord ls))
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative 3)

/-- A Fourth-class inverse identification at the translated word of a source word. -/
def FourthSelfInverse (ls : List (Fin 10)) : Prop :=
  ∃ g : H, sExtra.symm (rhoLocal (identWordLocal (fourthSourceWord ls))
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative 3)

/-- Root fifteen: the Fourth-class inverse self identification and the Odd class of the inverse
image bind the forward image. -/
theorem fourth_root15_of_ident (h : FourthSelfInverse (generatedAxisGlobalTwelveFourthSelfWord 2))
    (hodd : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨g, hg⟩ := h
  refine generatedAxisGlobalTwelveFourth_root15_of_self ⟨g, ?_⟩ hodd
  have e := fourthSourceWord_apply (generatedAxisGlobalTwelveFourthSelfWord 2)
  change sExtra⁻¹ (rhoLocal ((generatedAxisGlobalTwelveFourthSelfWord 2).map
    generatedAxisGlobalOddSourceLocalLetter).prod generatedFourthAxis) = _
  rw [e, LinearEquiv.coe_inv, hg]
  rfl

/-- Root one: a Fourth-class forward identification at the translated pair representative puts
one image of the root in the Fourth class. -/
theorem fourth_root1_fourth_of_ident
    (h : FourthSelfForward (generatedAxisGlobalTwelveFourthPairWord 0)) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 1) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) := by
  obtain ⟨g, hg⟩ := h
  refine generatedAxisGlobalTwelveFourth_root1_fourth_of_self ⟨g, ?_⟩
  have e := fourthSourceWord_apply (generatedAxisGlobalTwelveFourthPairWord 0)
  change sExtra (rhoLocal ((generatedAxisGlobalTwelveFourthPairWord 0).map
    generatedAxisGlobalOddSourceLocalLetter).prod generatedFourthAxis) = _
  rw [e, hg]
  rfl

/-- Root twelve: a Fourth-class inverse identification at the translated pair representative puts
one image of the root in the Fourth class. -/
theorem fourth_root12_fourth_of_ident
    (h : FourthSelfInverse (generatedAxisGlobalTwelveFourthPairWord 1)) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
        MulAction.orbit H (generatedAxisGlobalTwelveRepresentative 3) := by
  obtain ⟨g, hg⟩ := h
  refine generatedAxisGlobalTwelveFourth_root12_fourth_of_self ⟨g, ?_⟩
  have e := fourthSourceWord_apply (generatedAxisGlobalTwelveFourthPairWord 1)
  change sExtra⁻¹ (rhoLocal ((generatedAxisGlobalTwelveFourthPairWord 1).map
    generatedAxisGlobalOddSourceLocalLetter).prod generatedFourthAxis) = _
  rw [e, LinearEquiv.coe_inv, hg]
  rfl

/-! ## Partner identifications into the Fourth family -/

/-- The binary root of a frame-fixing prefix times a translated source word is read off from a
mask certificate of the source word and a Fourth generator path. -/
theorem fourth_partner_root (r : Fin 16) (n : List IdentLetter) (hn : ∀ l ∈ n, l ≠ IdentLetter.xi)
    (ls : List (Fin 10)) (m : ℕ)
    (hm : ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) m = 2048)
    (ws : List (Fin 5))
    (hpath : ws.foldr (fun k b => generatedAxisGlobalMaskColumnAction
      (generatedAxisGlobalTwelveFourthBinaryColumns k) b)
        (generatedAxisGlobalTwelveFourthRootMask r) = m) :
    generatedAxisGlobalBinaryAct (generatedAxisGlobalTwelveFourthGeneratorWord ws)
        (generatedAxisGlobalTwelveFourthRoot r) =
      generatedAxisGlobalBinaryRoot (identWordLocal (n ++ fourthSourceWord ls)) := by
  rw [identWordLocal_append, rootEightFrame_binaryRoot _ _ (rootEightFrame_identWord n hn),
    fourthSourceWord_binaryRoot]
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFourthGeneratorWord_binary _ _ _
      (generatedAxisGlobalTwelveFourthRoot_val r), hpath,
    generatedAxisGlobalTwelveFourth_sourceWord_root ls m hm]

/-- A partner identification landing on a frame-fixing prefix times a translated source word. -/
def FourthPartner (n : List IdentLetter) (ls : List (Fin 10)) (w : GriessSpace) : Prop :=
  ∃ h : H, sExtra (rhoLocal h w) =
      rhoLocal (identWordLocal (n ++ fourthSourceWord ls))
        (generatedAxisGlobalTwelveRepresentative 3) ∨
    sExtra.symm (rhoLocal h w) =
      rhoLocal (identWordLocal (n ++ fourthSourceWord ls))
        (generatedAxisGlobalTwelveRepresentative 3)

/-- A partner identification puts one triality image of the transporter in the partner orbit. -/
theorem fourth_partner_images (n : List IdentLetter) (ls : List (Fin 10)) (w : GriessSpace)
    (h : FourthPartner n ls w) :
    sExtra (rhoLocal (identWordLocal (n ++ fourthSourceWord ls)) generatedFourthAxis) ∈
        MulAction.orbit H w ∨
      sExtra⁻¹ (rhoLocal (identWordLocal (n ++ fourthSourceWord ls)) generatedFourthAxis) ∈
        MulAction.orbit H w := by
  obtain ⟨h, hh | hh⟩ := h
  · right
    change sExtra⁻¹ (rhoLocal (identWordLocal (n ++ fourthSourceWord ls))
      (generatedAxisGlobalTwelveRepresentative 3)) ∈ _
    rw [← hh, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact ⟨h, rfl⟩
  · left
    change sExtra (rhoLocal (identWordLocal (n ++ fourthSourceWord ls))
      (generatedAxisGlobalTwelveRepresentative 3)) ∈ _
    rw [← hh, LinearEquiv.apply_symm_apply]
    exact ⟨h, rfl⟩

/-- A partner identification from a listed family at a merged root binds both images. -/
theorem fourth_partner_merged (j : Fin 11) (n : List IdentLetter)
    (hn : ∀ l ∈ n, l ≠ IdentLetter.xi) (ls : List (Fin 10)) (m : ℕ)
    (hm : ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) m = 2048)
    (ws : List (Fin 5))
    (hpath : ws.foldr (fun k b => generatedAxisGlobalMaskColumnAction
      (generatedAxisGlobalTwelveFourthBinaryColumns k) b)
        (generatedAxisGlobalTwelveFourthRootMask (generatedAxisGlobalTwelveFourthMergedRoot j)) = m)
    (i : Fin 12) (h : FourthPartner n ls (generatedAxisGlobalTwelveRepresentative i)) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal
        (generatedAxisGlobalTwelveFourthMergedRoot j)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hk := fourth_partner_images n ls _ h
  have hk' : sExtra (rhoLocal (identWordLocal (n ++ fourthSourceWord ls)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal (identWordLocal (n ++ fourthSourceWord ls)) generatedFourthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
    hk.imp fourth_mem_union_of_orbit fourth_mem_union_of_orbit
  have hpos := generatedAxisGlobalTwelveFourth_reverse_merged
    generatedAxisGlobalTwelveRepresentative j (identWordLocal (n ++ fourthSourceWord ls))
    (generatedAxisGlobalTwelveFourthGeneratorWord ws)
    (generatedAxisGlobalTwelveFourthGeneratorWord_mem ws)
    (fourth_partner_root _ n hn ls m hm ws hpath) hk'
  exact ⟨hpos, generatedAxisGlobalTwelveFourthMerged_negative_of_positive _ j hpos⟩

/-- A partner identification at an unmerged root puts one image of the root in the partner
orbit. -/
theorem fourth_partner_orbit (r : Fin 16) (n : List IdentLetter)
    (hn : ∀ l ∈ n, l ≠ IdentLetter.xi) (ls : List (Fin 10)) (m : ℕ)
    (hm : ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
      (generatedAxisGlobalOddSourceRows l) x) m = 2048)
    (ws : List (Fin 5))
    (hpath : ws.foldr (fun k b => generatedAxisGlobalMaskColumnAction
      (generatedAxisGlobalTwelveFourthBinaryColumns k) b)
        (generatedAxisGlobalTwelveFourthRootMask r) = m)
    (w : GriessSpace) (h : FourthPartner n ls w) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal r) generatedFourthAxis) ∈
        MulAction.orbit H w ∨
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal r) generatedFourthAxis) ∈
        MulAction.orbit H w :=
  generatedAxisGlobalTwelveFourth_reverse_pair_orbit w r (identWordLocal (n ++ fourthSourceWord ls))
    (generatedAxisGlobalTwelveFourthGeneratorWord ws)
    (generatedAxisGlobalTwelveFourthGeneratorWord_mem ws)
    (fourth_partner_root r n hn ls m hm ws hpath) (fourth_partner_images n ls w h)

/-! ## The four listed partner transports into the Fourth family

Records (gfifth `F0+`, `F12+`; gtenth `T64+`, `T61-`): the Fourth root, the source word of the
transporter's coset part, its binary root mask and a Fourth generator path from the root. -/

/-- Fourth roots of the partner records. -/
def fourthPartnerRoot : Fin 4 → Fin 16 := ![0, 1, 5, 8]

/-- Source words of the coset parts of the partner transporters. -/
def fourthPartnerWord : Fin 4 → List (Fin 10) :=
  ![[0, 7, 7, 8, 6, 6, 6, 8, 7, 7, 8, 7, 7, 7], [0, 7, 8, 6, 6, 6, 8, 6, 6, 8, 6, 8, 7, 8, 7, 7],
    [0, 6, 0, 8, 0, 7, 8], [0, 8, 6, 0, 8, 6]]

/-- Binary root masks of the coset parts. -/
def fourthPartnerMask : Fin 4 → ℕ := ![337920, 5883904, 7980904, 2285660]

/-- Fourth generator paths from the roots to the binary roots of the coset parts. -/
def fourthPartnerPath : Fin 4 → List (Fin 5) :=
  ![[0, 4, 3, 4, 2, 1, 0, 3], [2, 0, 2, 3, 2, 3], [], []]

set_option maxHeartbeats 20000000 in
-- Evaluate four source words and four generator words on their masks.
/-- The finite mask certificates of the partner records. -/
theorem fourthPartner_certificate : ∀ t : Fin 4,
    (fourthPartnerWord t).foldr (fun l x =>
        generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
      (fourthPartnerMask t) = 2048 ∧
    (fourthPartnerPath t).foldr (fun k m =>
        generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveFourthBinaryColumns k) m)
      (generatedAxisGlobalTwelveFourthRootMask (fourthPartnerRoot t)) = fourthPartnerMask t := by
  decide +kernel

/-! ## Assembly -/

/-- Fourth-family coverage from identification statements alone.  Hypotheses: forward
identifications at the translated root words of roots `3, 4, 6, 7, 9, 10, 14` and an inverse one at
root `14`; inverse identifications at the translated self representatives of roots `2, 13` and a
Fourth-class one at root `15`; Fourth-class identifications at the translated pair representatives
of roots `1, 12`; the four partner records (roots `0, 1, 5, 8`); and the Odd classes of the forward
image of root `12` and of the inverse image of root `15`. -/
theorem generatedAxisGlobalTwelve_fourth_covered_of_idents
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
    (h12 : FourthSelfInverse (generatedAxisGlobalTwelveFourthPairWord 1))
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
      generatedFourthAxis) ∈ MulAction.orbit H generatedOddAxis) :
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
  have r12n := generatedAxisGlobalTwelveFourth_root12_of_classes
    (fourth_root12_fourth_of_ident h12) hodd12
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
