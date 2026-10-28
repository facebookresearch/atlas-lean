/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthLink
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthPhase

/-! # Identification words of the Tenth root words; pure-Tenth and partner bindings

Every original odd source letter is the local element of a word in the shared identification
alphabet `IdentLetter` (`xi⁻¹ = xi xi` by `xiSpinLocalFiber_cube`; the two octad source signs are
involutions), so every Tenth root word is the local element of an explicit identification word.

An identification `sExtra^{±1} (r_k · v₁₁) = (M ++ T_j) · v₁₁` with an Xi-free prefix `M` whose
computed Q-phase fixes (or negates) the Ω mask also binds triality images at the target root word
`j` (Ω-stabilizer or singleton-cocode transfer, `GeneratedAxisGlobalTwelveSixthPhase`). Twelve such
identifications (nine with computed phase, three plain positive images) bind both triality images at
all thirteen pure-Tenth root words; the identifications are hypotheses here, to be supplied by
whole-vector identification certificates. The prefixes found numerically are recorded, and their
Ω-phases are computed. A partner identification landing on a Tenth root vector, together with the
partner's opposite image, binds both images at that Tenth root word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-! ## Identification words of odd source letters and Tenth root words -/

/-- The identification word of each original odd source letter. -/
def generatedAxisGlobalTwelveTenthOddIdent : Fin 10 → List IdentLetter :=
  ![[.xi], [.xi, .xi], [.sign 16 0], [.sign 16 0], [.sign 32 0], [.sign 32 0],
    [.mono (0, false)], [.mono (0, true)], [.mono (1, false)], [.mono (1, true)]]

private theorem tenthIdent_sign_sq (a : Fin 4096)
    (hp : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) :
    generatedFifthSignLocal a 0 ^ 2 = 1 := by
  have hx : sourceGeneratedCode a 0 * sourceGeneratedCode a 0 = 1 := by
    rw [← pow_two, sourceGeneratedCode_square, hp]
    change qIntoGenerated 1 = 1
    exact map_one _
  apply localIntoGenerated_injective
  rw [map_pow, map_one, generatedFifth_sign_local_generated]
  change (extraIntoGenerated⁻¹ * sourceGeneratedCode a 0 * extraIntoGenerated) ^ 2 = 1
  calc
    _ = extraIntoGenerated⁻¹ *
        (sourceGeneratedCode a 0 * sourceGeneratedCode a 0) * extraIntoGenerated := by
          rw [pow_two]
          group
    _ = 1 := by rw [hx]; group

private theorem tenthIdent_sign_inv (a : Fin 4096)
    (hp : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) :
    (generatedFifthSignLocal a 0)⁻¹ = generatedFifthSignLocal a 0 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact tenthIdent_sign_sq a hp)

private theorem tenthIdent_xi_inv :
    (localFiberIntoH xiSpinLocalFiber)⁻¹ =
      localFiberIntoH (xiSpinLocalFiber * xiSpinLocalFiber) := by
  have h : xiSpinLocalFiber⁻¹ = xiSpinLocalFiber * xiSpinLocalFiber := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using xiSpinLocalFiber_cube
  rw [← h, map_inv]

private theorem tenthIdent0 :
    identWordLocal [IdentLetter.xi] = generatedAxisGlobalOddSourceLocalLetter 0 :=
  identWordLocal_singleton _

private theorem tenthIdent1 :
    identWordLocal [IdentLetter.xi, IdentLetter.xi] =
      generatedAxisGlobalOddSourceLocalLetter 1 := by
  have h : identWordLocal [IdentLetter.xi, IdentLetter.xi] =
      localFiberIntoH (xiSpinLocalFiber * xiSpinLocalFiber) := by
    simp [identWordLocal, identWordFiber, IdentLetter.fiber]
  rw [h, ← tenthIdent_xi_inv]
  rfl

private theorem tenthIdent2 :
    identWordLocal [IdentLetter.sign 16 0] = generatedAxisGlobalOddSourceLocalLetter 2 := by
  rw [identWordLocal_singleton]
  exact generatedFifth_sign_fiber_local 16 0

private theorem tenthIdent3 :
    identWordLocal [IdentLetter.sign 16 0] = generatedAxisGlobalOddSourceLocalLetter 3 := by
  rw [identWordLocal_singleton]
  change localFiberIntoH (generatedFifthSignFiber 16 0) = (generatedFifthSignLocal 16 0)⁻¹
  rw [generatedFifth_sign_fiber_local, tenthIdent_sign_inv 16 (by decide +kernel)]

private theorem tenthIdent4 :
    identWordLocal [IdentLetter.sign 32 0] = generatedAxisGlobalOddSourceLocalLetter 4 := by
  rw [identWordLocal_singleton]
  exact generatedFifth_sign_fiber_local 32 0

private theorem tenthIdent5 :
    identWordLocal [IdentLetter.sign 32 0] = generatedAxisGlobalOddSourceLocalLetter 5 := by
  rw [identWordLocal_singleton]
  change localFiberIntoH (generatedFifthSignFiber 32 0) = (generatedFifthSignLocal 32 0)⁻¹
  rw [generatedFifth_sign_fiber_local, tenthIdent_sign_inv 32 (by decide +kernel)]

private theorem tenthIdent6 :
    identWordLocal [IdentLetter.mono (0, false)] = generatedAxisGlobalOddSourceLocalLetter 6 := by
  rw [identWordLocal_singleton]
  rfl

private theorem tenthIdent7 :
    identWordLocal [IdentLetter.mono (0, true)] = generatedAxisGlobalOddSourceLocalLetter 7 := by
  rw [identWordLocal_singleton]
  exact map_inv localFiberIntoH _

private theorem tenthIdent8 :
    identWordLocal [IdentLetter.mono (1, false)] = generatedAxisGlobalOddSourceLocalLetter 8 := by
  rw [identWordLocal_singleton]
  rfl

private theorem tenthIdent9 :
    identWordLocal [IdentLetter.mono (1, true)] = generatedAxisGlobalOddSourceLocalLetter 9 := by
  rw [identWordLocal_singleton]
  exact map_inv localFiberIntoH _

/-- Each odd source letter is the local element of its identification word. -/
theorem generatedAxisGlobalTwelveTenthOddIdent_local (l : Fin 10) :
    identWordLocal (generatedAxisGlobalTwelveTenthOddIdent l) =
      generatedAxisGlobalOddSourceLocalLetter l := by
  fin_cases l
  · exact tenthIdent0
  · exact tenthIdent1
  · exact tenthIdent2
  · exact tenthIdent3
  · exact tenthIdent4
  · exact tenthIdent5
  · exact tenthIdent6
  · exact tenthIdent7
  · exact tenthIdent8
  · exact tenthIdent9

/-- A product of odd source letters is the local element of the joined identification words. -/
theorem generatedAxisGlobalTwelveTenthOddIdent_word (ls : List (Fin 10)) :
    (ls.map generatedAxisGlobalOddSourceLocalLetter).prod =
      identWordLocal (ls.flatMap generatedAxisGlobalTwelveTenthOddIdent) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rw [List.map_cons, List.prod_cons, List.flatMap_cons, identWordLocal_append,
      generatedAxisGlobalTwelveTenthOddIdent_local l, ih]

/-- The identification word of a Tenth root word. -/
def generatedAxisGlobalTwelveTenthRootIdent (k : Fin 65) : List IdentLetter :=
  (generatedAxisGlobalTwelveTenthRootLetters k).flatMap generatedAxisGlobalTwelveTenthOddIdent

/-- Each Tenth root word is the local element of its identification word. -/
theorem generatedAxisGlobalTwelveTenthRootWord_ident (k : Fin 65) :
    generatedAxisGlobalTwelveTenthRootWord k =
      identWordLocal (generatedAxisGlobalTwelveTenthRootIdent k) :=
  generatedAxisGlobalTwelveTenthOddIdent_word _

/-! ## Prefixes with computed Ω-phase -/

/-- Letters allowed in an identification prefix: no Xi, and source signs with `ε = 0`. -/
def generatedAxisGlobalTwelveTenthPrefixLetter : IdentLetter → Bool
  | .xi => false
  | .sign _ ε => ε == 0
  | _ => true

/-- An admissible prefix whose computed Q-phase fixes the Ω mask. -/
def GeneratedAxisGlobalTwelveTenthFixPrefix (M : List IdentLetter) : Prop :=
  M.all generatedAxisGlobalTwelveTenthPrefixLetter = true ∧
    qmWord (M.map sixthPhaseData) (2048, false) = (2048, false)

/-- An admissible prefix whose computed Q-phase sends the Ω mask to its negative. -/
def GeneratedAxisGlobalTwelveTenthFlipPrefix (M : List IdentLetter) : Prop :=
  M.all generatedAxisGlobalTwelveTenthPrefixLetter = true ∧
    qmWord (M.map sixthPhaseData) (2048, false) = (2048, true)

private theorem tenthPrefix_letters {M : List IdentLetter}
    (h : M.all generatedAxisGlobalTwelveTenthPrefixLetter = true) :
    (∀ l ∈ M, SixthPhaseLetter l) ∧ ∀ l ∈ M, l ≠ IdentLetter.xi := by
  rw [List.all_eq_true] at h
  constructor
  · intro l hl
    have hl' := h l hl
    cases l with
    | xi => exact True.intro
    | sign a ε =>
      change ε = 0
      simpa [generatedAxisGlobalTwelveTenthPrefixLetter] using hl'
    | mono m => exact True.intro
    | qel g => exact True.intro
  · intro l hl he
    subst he
    have hl' := h _ hl
    simp [generatedAxisGlobalTwelveTenthPrefixLetter] at hl'

/-! ## Identification statements and transfers -/

/-- The Tenth root vector `r_k · v₁₁`. -/
abbrev generatedAxisGlobalTwelveTenthRootVector (k : Fin 65) : GriessSpace :=
  rhoLocal (generatedAxisGlobalTwelveTenthRootWord k) (generatedAxisGlobalTwelveRepresentative 11)

/-- A positive Tenth identification `sExtra (T_k · v₁₁) = (M ++ T_j) · v₁₁`. -/
def GeneratedAxisGlobalTwelveTenthIdentPos (k j : Fin 65) (M : List IdentLetter) : Prop :=
  sExtra (rhoLocal (identWordLocal (generatedAxisGlobalTwelveTenthRootIdent k))
      (generatedAxisGlobalTwelveRepresentative 11)) =
    rhoLocal (identWordLocal (M ++ generatedAxisGlobalTwelveTenthRootIdent j))
      (generatedAxisGlobalTwelveRepresentative 11)

/-- An inverse Tenth identification `sExtra⁻¹ (T_k · v₁₁) = (M ++ T_j) · v₁₁`. -/
def GeneratedAxisGlobalTwelveTenthIdentNeg (k j : Fin 65) (M : List IdentLetter) : Prop :=
  sExtra⁻¹ (rhoLocal (identWordLocal (generatedAxisGlobalTwelveTenthRootIdent k))
      (generatedAxisGlobalTwelveRepresentative 11)) =
    rhoLocal (identWordLocal (M ++ generatedAxisGlobalTwelveTenthRootIdent j))
      (generatedAxisGlobalTwelveRepresentative 11)

private theorem tenth_inv_eq_sq (y : GriessSpace) : sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

private theorem tenth_inv_inv (y : GriessSpace) : sExtra⁻¹ (sExtra⁻¹ y) = sExtra y := by
  rw [tenth_inv_eq_sq (sExtra⁻¹ y), LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

private theorem tenth_lhs (k : Fin 65) :
    rhoLocal (identWordLocal (generatedAxisGlobalTwelveTenthRootIdent k))
      (generatedAxisGlobalTwelveRepresentative 11) =
      generatedAxisGlobalTwelveTenthRootVector k := by
  rw [generatedAxisGlobalTwelveTenthRootVector, generatedAxisGlobalTwelveTenthRootWord_ident]

private theorem tenth_rhs (M : List IdentLetter) (j : Fin 65) :
    rhoLocal (identWordLocal (M ++ generatedAxisGlobalTwelveTenthRootIdent j))
      (generatedAxisGlobalTwelveRepresentative 11) =
      rhoLocal (identWordLocal M * generatedAxisGlobalTwelveTenthRootWord j)
        (generatedAxisGlobalTwelveRepresentative 11) := by
  rw [identWordLocal_append, generatedAxisGlobalTwelveTenthRootWord_ident]

private theorem identPos_norm {k j : Fin 65} {M : List IdentLetter}
    (h : GeneratedAxisGlobalTwelveTenthIdentPos k j M) :
    sExtra (generatedAxisGlobalTwelveTenthRootVector k) =
      rhoLocal (identWordLocal M * generatedAxisGlobalTwelveTenthRootWord j)
        (generatedAxisGlobalTwelveRepresentative 11) := by
  rw [← tenth_lhs, ← tenth_rhs]
  exact h

private theorem identNeg_norm {k j : Fin 65} {M : List IdentLetter}
    (h : GeneratedAxisGlobalTwelveTenthIdentNeg k j M) :
    sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector k) =
      rhoLocal (identWordLocal M * generatedAxisGlobalTwelveTenthRootWord j)
        (generatedAxisGlobalTwelveRepresentative 11) := by
  rw [← tenth_lhs, ← tenth_rhs]
  exact h

/-- A positive identification gives the positive image at its source root word. -/
theorem generatedAxisGlobalTwelveTenth_pos_of_identPos {k j : Fin 65} {M : List IdentLetter}
    (h : GeneratedAxisGlobalTwelveTenthIdentPos k j M) :
    sExtra (generatedAxisGlobalTwelveTenthRootVector k) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 11 _ (identPos_norm h)

/-- An inverse identification gives the inverse image at its source root word. -/
theorem generatedAxisGlobalTwelveTenth_neg_of_identNeg {k j : Fin 65} {M : List IdentLetter}
    (h : GeneratedAxisGlobalTwelveTenthIdentNeg k j M) :
    sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector k) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 11 _ (identNeg_norm h)

/-- A positive identification with a phase-fixing prefix gives the inverse image at the target. -/
theorem generatedAxisGlobalTwelveTenth_target_neg_of_identPos {k j : Fin 65}
    {M : List IdentLetter} (hM : GeneratedAxisGlobalTwelveTenthFixPrefix M)
    (h : GeneratedAxisGlobalTwelveTenthIdentPos k j M) :
    sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector j) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hl, hx⟩ := tenthPrefix_letters hM.1
  have := (sixthPhase_of_forward_identity 11 _ M _ hl hx _ h).1 hM.2
  rwa [tenth_lhs] at this

/-- A positive identification with a phase-negating prefix gives the positive image at the
target. -/
theorem generatedAxisGlobalTwelveTenth_target_pos_of_identPos_flip {k j : Fin 65}
    {M : List IdentLetter} (hM : GeneratedAxisGlobalTwelveTenthFlipPrefix M)
    (h : GeneratedAxisGlobalTwelveTenthIdentPos k j M) :
    sExtra (generatedAxisGlobalTwelveTenthRootVector j) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hl, hx⟩ := tenthPrefix_letters hM.1
  have := (sixthPhase_of_forward_identity 11 _ M _ hl hx _ h).2 hM.2
  rwa [tenth_lhs] at this

/-- An inverse identification with a phase-fixing prefix gives the positive image at the
target. -/
theorem generatedAxisGlobalTwelveTenth_target_pos_of_identNeg {k j : Fin 65}
    {M : List IdentLetter} (hM : GeneratedAxisGlobalTwelveTenthFixPrefix M)
    (h : GeneratedAxisGlobalTwelveTenthIdentNeg k j M) :
    sExtra (generatedAxisGlobalTwelveTenthRootVector j) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hl, hx⟩ := tenthPrefix_letters hM.1
  have := (sixthPhase_of_inverse_identity 11 _ M _ hl hx _ h).1 hM.2
  rwa [tenth_lhs] at this

/-- A positive identification with a phase-fixing prefix moves the positive image at the target
to the inverse image at the source. -/
theorem generatedAxisGlobalTwelveTenth_source_neg_of_identPos {k j : Fin 65}
    {M : List IdentLetter} (hM : GeneratedAxisGlobalTwelveTenthFixPrefix M)
    (h : GeneratedAxisGlobalTwelveTenthIdentPos k j M)
    (hj : sExtra (generatedAxisGlobalTwelveTenthRootVector j) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector k) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hl, _⟩ := tenthPrefix_letters hM.1
  have hn := sixthPhase_mem M hl hM.2
  rw [tenth_inv_eq_sq, identPos_norm h]
  apply sixthPhase_forward_of_mem _ (identWordLocal M)⁻¹ _ _ (inv_mem hn)
  rw [inv_mul_cancel_left]
  exact hj

/-- An inverse identification with a phase-fixing prefix moves the positive image at the source
to the inverse image at the target. -/
theorem generatedAxisGlobalTwelveTenth_target_neg_of_identNeg {k j : Fin 65}
    {M : List IdentLetter} (hM : GeneratedAxisGlobalTwelveTenthFixPrefix M)
    (h : GeneratedAxisGlobalTwelveTenthIdentNeg k j M)
    (hk : sExtra (generatedAxisGlobalTwelveTenthRootVector k) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector j) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hl, _⟩ := tenthPrefix_letters hM.1
  apply sixthPhase_inverse_of_mem _ (identWordLocal M) _ _ (sixthPhase_mem M hl hM.2)
  rw [← identNeg_norm h, tenth_inv_inv]
  exact hk

/-- A positive identification with a phase-negating prefix moves the inverse image at the source
to the inverse image at the target. -/
theorem generatedAxisGlobalTwelveTenth_target_neg_of_identPos_flip {k j : Fin 65}
    {M : List IdentLetter} (hM : GeneratedAxisGlobalTwelveTenthFlipPrefix M)
    (h : GeneratedAxisGlobalTwelveTenthIdentPos k j M)
    (hk : sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector k) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector j) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hl, hx⟩ := tenthPrefix_letters hM.1
  apply sixthPhase_forward_of_flip _ (identWordLocal M) _ _ (sixthPhase_flip_mem M hl hx hM.2)
  rw [← identPos_norm h, ← tenth_inv_eq_sq]
  exact hk

/-! ## Partner identifications landing on a Tenth root vector -/

/-- A forward partner identification landing on `M · r_k · v₁₁` (admissible prefix `M` of either
Ω-phase), with the partner's inverse image known, binds both images at Tenth root word `k`. -/
theorem generatedAxisGlobalTwelveTenth_pair_of_partner_forward (j : Fin 12) (h : H) (k : Fin 65)
    (M : List IdentLetter)
    (hM : GeneratedAxisGlobalTwelveTenthFixPrefix M ∨ GeneratedAxisGlobalTwelveTenthFlipPrefix M)
    (he : sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal (identWordLocal (M ++ generatedAxisGlobalTwelveTenthRootIdent k))
        (generatedAxisGlobalTwelveRepresentative 11))
    (hother : sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (generatedAxisGlobalTwelveTenthRootVector k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hmem : sExtra (rhoLocal (identWordLocal M * generatedAxisGlobalTwelveTenthRootWord k)
      (generatedAxisGlobalTwelveRepresentative 11)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    rw [← tenth_rhs, ← he, ← tenth_inv_eq_sq]
    exact hother
  rcases hM with hM | hM
  · obtain ⟨hl, hx⟩ := tenthPrefix_letters hM.1
    have hneg := (sixthPhase_of_forward_identity j h M _ hl hx _ he).1 hM.2
    rw [tenth_lhs] at hneg
    exact ⟨sixthPhase_forward_of_mem _ _ _ _ (sixthPhase_mem M hl hM.2) hmem, hneg⟩
  · obtain ⟨hl, hx⟩ := tenthPrefix_letters hM.1
    have hpos := (sixthPhase_of_forward_identity j h M _ hl hx _ he).2 hM.2
    rw [tenth_lhs] at hpos
    exact ⟨hpos, sixthPhase_forward_of_flip _ _ _ _ (sixthPhase_flip_mem M hl hx hM.2) hmem⟩

/-- An inverse partner identification landing on `M · r_k · v₁₁` (admissible prefix `M` of either
Ω-phase), with the partner's positive image known, binds both images at Tenth root word `k`. -/
theorem generatedAxisGlobalTwelveTenth_pair_of_partner_inverse (j : Fin 12) (h : H) (k : Fin 65)
    (M : List IdentLetter)
    (hM : GeneratedAxisGlobalTwelveTenthFixPrefix M ∨ GeneratedAxisGlobalTwelveTenthFlipPrefix M)
    (he : sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal (identWordLocal (M ++ generatedAxisGlobalTwelveTenthRootIdent k))
        (generatedAxisGlobalTwelveRepresentative 11))
    (hother : sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (generatedAxisGlobalTwelveTenthRootVector k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hmem : sExtra⁻¹ (rhoLocal (identWordLocal M * generatedAxisGlobalTwelveTenthRootWord k)
      (generatedAxisGlobalTwelveRepresentative 11)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    rw [← tenth_rhs, ← he, tenth_inv_inv]
    exact hother
  rcases hM with hM | hM
  · obtain ⟨hl, hx⟩ := tenthPrefix_letters hM.1
    have hpos := (sixthPhase_of_inverse_identity j h M _ hl hx _ he).1 hM.2
    rw [tenth_lhs] at hpos
    exact ⟨hpos, sixthPhase_inverse_of_mem _ _ _ _ (sixthPhase_mem M hl hM.2) hmem⟩
  · obtain ⟨hl, hx⟩ := tenthPrefix_letters hM.1
    have hneg := (sixthPhase_of_inverse_identity j h M _ hl hx _ he).2 hM.2
    rw [tenth_lhs] at hneg
    exact ⟨sixthPhase_inverse_of_flip _ _ _ _ (sixthPhase_flip_mem M hl hx hM.2) hmem, hneg⟩

/-! ## The pure-Tenth root words -/

/-- The thirteen pure-Tenth root words (both triality images in the Tenth class). -/
def generatedAxisGlobalTwelveTenthPureRoots : List (Fin 65) :=
  [3, 11, 13, 15, 18, 22, 24, 30, 40, 42, 46, 47, 59]

/-- Pure-Tenth identification data: nine identifications whose prefixes have the stated Ω-phase,
and the positive images at root words 3, 15 and 30. -/
def GeneratedAxisGlobalTwelveTenthPureIdentified : Prop :=
  (∃ M, GeneratedAxisGlobalTwelveTenthFixPrefix M ∧
    GeneratedAxisGlobalTwelveTenthIdentPos 59 59 M) ∧
  (∃ M, GeneratedAxisGlobalTwelveTenthFixPrefix M ∧
    GeneratedAxisGlobalTwelveTenthIdentPos 11 11 M) ∧
  (∃ M, GeneratedAxisGlobalTwelveTenthFixPrefix M ∧
    GeneratedAxisGlobalTwelveTenthIdentNeg 18 18 M) ∧
  (∃ M, GeneratedAxisGlobalTwelveTenthFixPrefix M ∧
    GeneratedAxisGlobalTwelveTenthIdentPos 22 22 M) ∧
  sExtra (generatedAxisGlobalTwelveTenthRootVector 3) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
  (∃ M, GeneratedAxisGlobalTwelveTenthFixPrefix M ∧
    GeneratedAxisGlobalTwelveTenthIdentPos 13 3 M) ∧
  sExtra (generatedAxisGlobalTwelveTenthRootVector 15) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
  (∃ M, GeneratedAxisGlobalTwelveTenthFixPrefix M ∧
    GeneratedAxisGlobalTwelveTenthIdentPos 24 15 M) ∧
  sExtra (generatedAxisGlobalTwelveTenthRootVector 30) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
  (∃ M, GeneratedAxisGlobalTwelveTenthFixPrefix M ∧
    GeneratedAxisGlobalTwelveTenthIdentNeg 30 40 M) ∧
  (∃ M, GeneratedAxisGlobalTwelveTenthFlipPrefix M ∧
    GeneratedAxisGlobalTwelveTenthIdentPos 42 46 M) ∧
  (∃ M, GeneratedAxisGlobalTwelveTenthFixPrefix M ∧
    GeneratedAxisGlobalTwelveTenthIdentNeg 42 47 M)

/-- The pure-Tenth identification data bind both triality images at all thirteen pure-Tenth root
words. -/
theorem generatedAxisGlobalTwelveTenth_pure_of_identified
    (hid : GeneratedAxisGlobalTwelveTenthPureIdentified) (k : Fin 65)
    (hk : k ∈ generatedAxisGlobalTwelveTenthPureRoots) :
    sExtra (generatedAxisGlobalTwelveTenthRootVector k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector k) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨⟨M59, f59, h59⟩, ⟨M11, f11, h11⟩, ⟨M18, f18, h18⟩, ⟨M22, f22, h22⟩, p3,
    ⟨M13, f13, h13⟩, p15, ⟨M24, f24, h24⟩, p30, ⟨M30, f30, h30⟩, ⟨M42, f42, h42⟩,
    ⟨M42', f42', h42'⟩⟩ := hid
  have p42 := generatedAxisGlobalTwelveTenth_pos_of_identPos h42
  have n42 := generatedAxisGlobalTwelveTenth_neg_of_identNeg h42'
  simp only [generatedAxisGlobalTwelveTenthPureRoots, List.mem_cons, List.not_mem_nil,
    or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨p3, generatedAxisGlobalTwelveTenth_target_neg_of_identPos f13 h13⟩
  · exact ⟨generatedAxisGlobalTwelveTenth_pos_of_identPos h11,
      generatedAxisGlobalTwelveTenth_target_neg_of_identPos f11 h11⟩
  · exact ⟨generatedAxisGlobalTwelveTenth_pos_of_identPos h13,
      generatedAxisGlobalTwelveTenth_source_neg_of_identPos f13 h13 p3⟩
  · exact ⟨p15, generatedAxisGlobalTwelveTenth_target_neg_of_identPos f24 h24⟩
  · exact ⟨generatedAxisGlobalTwelveTenth_target_pos_of_identNeg f18 h18,
      generatedAxisGlobalTwelveTenth_neg_of_identNeg h18⟩
  · exact ⟨generatedAxisGlobalTwelveTenth_pos_of_identPos h22,
      generatedAxisGlobalTwelveTenth_target_neg_of_identPos f22 h22⟩
  · exact ⟨generatedAxisGlobalTwelveTenth_pos_of_identPos h24,
      generatedAxisGlobalTwelveTenth_source_neg_of_identPos f24 h24 p15⟩
  · exact ⟨p30, generatedAxisGlobalTwelveTenth_neg_of_identNeg h30⟩
  · exact ⟨generatedAxisGlobalTwelveTenth_target_pos_of_identNeg f30 h30,
      generatedAxisGlobalTwelveTenth_target_neg_of_identNeg f30 h30 p30⟩
  · exact ⟨p42, n42⟩
  · exact ⟨generatedAxisGlobalTwelveTenth_target_pos_of_identPos_flip f42 h42,
      generatedAxisGlobalTwelveTenth_target_neg_of_identPos_flip f42 h42 n42⟩
  · exact ⟨generatedAxisGlobalTwelveTenth_target_pos_of_identNeg f42' h42',
      generatedAxisGlobalTwelveTenth_target_neg_of_identNeg f42' h42' p42⟩
  · exact ⟨generatedAxisGlobalTwelveTenth_pos_of_identPos h59,
      generatedAxisGlobalTwelveTenth_target_neg_of_identPos f59 h59⟩

/-- Tenth family coverage from the two fixers, the pure-Tenth identification data, and both
triality images at the fifty-one remaining non-identity root words. -/
theorem generatedAxisGlobalTwelve_tenth_covered_of_pure
    (hfix : GeneratedAxisGlobalTwelveTenthFixers)
    (hid : GeneratedAxisGlobalTwelveTenthPureIdentified)
    (hmixed : ∀ k : Fin 65, k ≠ 0 → k ∉ generatedAxisGlobalTwelveTenthPureRoots →
      sExtra (generatedAxisGlobalTwelveTenthRootVector k) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
        sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector k) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 11 := by
  have hall : ∀ k : Fin 65, k ≠ 0 →
      sExtra (generatedAxisGlobalTwelveTenthRootVector k) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
        sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector k) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    intro k hk
    by_cases hp : k ∈ generatedAxisGlobalTwelveTenthPureRoots
    · exact generatedAxisGlobalTwelveTenth_pure_of_identified hid k hp
    · exact hmixed k hk hp
  exact generatedAxisGlobalTwelve_tenth_covered_of hfix (fun k hk => (hall k hk).1)
    (fun k hk => (hall k hk).2)

/-! ## The numerically found prefixes -/

/-- Numeric transporter prefix (gtenth guide) for the positive image at root 59 (target root 59). -/
def generatedAxisGlobalTwelveTenthPrefix59p : List IdentLetter :=
  [.qel (qmElt (915955, false)), .sign 247 0]

/-- Numeric transporter prefix (gtenth guide) for the positive image at root 11 (target root 11). -/
def generatedAxisGlobalTwelveTenthPrefix11p : List IdentLetter :=
  [.qel (qmElt (1453592, true)), .sign 346 0, .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, true),
    .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false),
    .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, true)]

/-- Numeric transporter prefix (gtenth guide) for the inverse image at root 18 (target root 18). -/
def generatedAxisGlobalTwelveTenthPrefix18n : List IdentLetter :=
  [.qel (qmElt (5471441, true)), .sign 453 0, .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false)]

/-- Numeric transporter prefix (gtenth guide) for the positive image at root 22 (target root 22). -/
def generatedAxisGlobalTwelveTenthPrefix22p : List IdentLetter :=
  [.qel (qmElt (4027564, true)), .sign 1403 0, .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, true),
    .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
    .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, true), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (0, true)]

/-- Numeric transporter prefix (gtenth guide) for the positive image at root 3 (target root 3). -/
def generatedAxisGlobalTwelveTenthPrefix3p : List IdentLetter :=
  [.qel (qmElt (9525928, true)), .sign 1745 0, .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true),
    .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false)]

/-- Numeric transporter prefix (gtenth guide) for the positive image at root 13 (target root 3). -/
def generatedAxisGlobalTwelveTenthPrefix13p : List IdentLetter :=
  [.qel (qmElt (7366097, false)), .sign 711 0, .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true),
    .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, true),
    .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
    .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true)]

/-- Numeric transporter prefix (gtenth guide) for the positive image at root 15 (target root 15). -/
def generatedAxisGlobalTwelveTenthPrefix15p : List IdentLetter :=
  [.qel (qmElt (12151567, true)), .sign 1147 0, .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true),
    .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true),
    .mono (0, true), .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, true),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true),
    .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (0, true)]

/-- Numeric transporter prefix (gtenth guide) for the positive image at root 24 (target root 15). -/
def generatedAxisGlobalTwelveTenthPrefix24p : List IdentLetter :=
  [.qel (qmElt (2905320, false)), .sign 566 0, .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false)]

/-- Numeric transporter prefix (gtenth guide) for the positive image at root 30 (target root 30). -/
def generatedAxisGlobalTwelveTenthPrefix30p : List IdentLetter :=
  [.qel (qmElt (12439386, false)), .sign 1768 0, .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, true), .mono (0, true),
    .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, true),
    .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true),
    .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, true),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true)]

/-- Numeric transporter prefix (gtenth guide) for the inverse image at root 30 (target root 40). -/
def generatedAxisGlobalTwelveTenthPrefix30n : List IdentLetter :=
  [.qel (qmElt (3624659, true)), .sign 1453 0, .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true),
    .mono (1, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false)]

/-- Numeric transporter prefix (gtenth guide) for the positive image at root 42 (target root 46). -/
def generatedAxisGlobalTwelveTenthPrefix42p : List IdentLetter :=
  [.qel (qmElt (8791320, true)), .sign 1127 0, .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (0, true)]

/-- Numeric transporter prefix (gtenth guide) for the inverse image at root 42 (target root 47). -/
def generatedAxisGlobalTwelveTenthPrefix42n : List IdentLetter :=
  [.qel (qmElt (4437584, true)), .sign 755 0, .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
    .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, true), .mono (0, true),
    .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, true),
    .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (1, false)]

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the numerically found prefix `59p` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveTenthPrefix59p_phase :
    GeneratedAxisGlobalTwelveTenthFixPrefix generatedAxisGlobalTwelveTenthPrefix59p :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the numerically found prefix `11p` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveTenthPrefix11p_phase :
    GeneratedAxisGlobalTwelveTenthFixPrefix generatedAxisGlobalTwelveTenthPrefix11p :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the numerically found prefix `18n` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveTenthPrefix18n_phase :
    GeneratedAxisGlobalTwelveTenthFixPrefix generatedAxisGlobalTwelveTenthPrefix18n :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the numerically found prefix `22p` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveTenthPrefix22p_phase :
    GeneratedAxisGlobalTwelveTenthFixPrefix generatedAxisGlobalTwelveTenthPrefix22p :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the numerically found prefix `13p` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveTenthPrefix13p_phase :
    GeneratedAxisGlobalTwelveTenthFixPrefix generatedAxisGlobalTwelveTenthPrefix13p :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the numerically found prefix `24p` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveTenthPrefix24p_phase :
    GeneratedAxisGlobalTwelveTenthFixPrefix generatedAxisGlobalTwelveTenthPrefix24p :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the numerically found prefix `30n` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveTenthPrefix30n_phase :
    GeneratedAxisGlobalTwelveTenthFixPrefix generatedAxisGlobalTwelveTenthPrefix30n :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the numerically found prefix `42p` negates the Ω mask. -/
theorem generatedAxisGlobalTwelveTenthPrefix42p_phase :
    GeneratedAxisGlobalTwelveTenthFlipPrefix generatedAxisGlobalTwelveTenthPrefix42p :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the numerically found prefix `42n` fixes the Ω mask. -/
theorem generatedAxisGlobalTwelveTenthPrefix42n_phase :
    GeneratedAxisGlobalTwelveTenthFixPrefix generatedAxisGlobalTwelveTenthPrefix42n :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The twelve numerically found identifications (to be certified as whole-vector identities)
give the pure-Tenth identification data. -/
theorem generatedAxisGlobalTwelveTenthPureIdentified_of_transporters
    (h59 : GeneratedAxisGlobalTwelveTenthIdentPos 59 59 generatedAxisGlobalTwelveTenthPrefix59p)
    (h11 : GeneratedAxisGlobalTwelveTenthIdentPos 11 11 generatedAxisGlobalTwelveTenthPrefix11p)
    (h18 : GeneratedAxisGlobalTwelveTenthIdentNeg 18 18 generatedAxisGlobalTwelveTenthPrefix18n)
    (h22 : GeneratedAxisGlobalTwelveTenthIdentPos 22 22 generatedAxisGlobalTwelveTenthPrefix22p)
    (h3 : GeneratedAxisGlobalTwelveTenthIdentPos 3 3 generatedAxisGlobalTwelveTenthPrefix3p)
    (h13 : GeneratedAxisGlobalTwelveTenthIdentPos 13 3 generatedAxisGlobalTwelveTenthPrefix13p)
    (h15 : GeneratedAxisGlobalTwelveTenthIdentPos 15 15 generatedAxisGlobalTwelveTenthPrefix15p)
    (h24 : GeneratedAxisGlobalTwelveTenthIdentPos 24 15 generatedAxisGlobalTwelveTenthPrefix24p)
    (h30 : GeneratedAxisGlobalTwelveTenthIdentPos 30 30 generatedAxisGlobalTwelveTenthPrefix30p)
    (h30' : GeneratedAxisGlobalTwelveTenthIdentNeg 30 40 generatedAxisGlobalTwelveTenthPrefix30n)
    (h42 : GeneratedAxisGlobalTwelveTenthIdentPos 42 46 generatedAxisGlobalTwelveTenthPrefix42p)
    (h42' : GeneratedAxisGlobalTwelveTenthIdentNeg 42 47 generatedAxisGlobalTwelveTenthPrefix42n) :
    GeneratedAxisGlobalTwelveTenthPureIdentified := by
  exact ⟨⟨_, generatedAxisGlobalTwelveTenthPrefix59p_phase, h59⟩,
    ⟨_, generatedAxisGlobalTwelveTenthPrefix11p_phase, h11⟩,
    ⟨_, generatedAxisGlobalTwelveTenthPrefix18n_phase, h18⟩,
    ⟨_, generatedAxisGlobalTwelveTenthPrefix22p_phase, h22⟩,
    generatedAxisGlobalTwelveTenth_pos_of_identPos h3,
    ⟨_, generatedAxisGlobalTwelveTenthPrefix13p_phase, h13⟩,
    generatedAxisGlobalTwelveTenth_pos_of_identPos h15,
    ⟨_, generatedAxisGlobalTwelveTenthPrefix24p_phase, h24⟩,
    generatedAxisGlobalTwelveTenth_pos_of_identPos h30,
    ⟨_, generatedAxisGlobalTwelveTenthPrefix30n_phase, h30'⟩,
    ⟨_, generatedAxisGlobalTwelveTenthPrefix42p_phase, h42⟩,
    ⟨_, generatedAxisGlobalTwelveTenthPrefix42n_phase, h42'⟩⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
