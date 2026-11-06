/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionCo1FrameOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignActions

/-! Generic binding infrastructure for the Eighth family.

Representative cosets are words in the shared identification alphabet: a prefix of extraspecial,
Golay sign and permutation letters (it fixes the binary Ω point) followed by a word in Xi and the
permutation letters. The binary root of such a coset is an explicit mask, so a root binding reduces
to the two triality images at one explicit coset. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Xi and the four permutation letters of the odd source alphabet as identification letters;
the remaining odd source letters are not used and are sent to Xi. -/
def eighthBindIdent (l : Fin 10) : IdentLetter :=
  if l.val = 6 then IdentLetter.mono (0, false)
  else if l.val = 7 then IdentLetter.mono (0, true)
  else if l.val = 8 then IdentLetter.mono (1, false)
  else if l.val = 9 then IdentLetter.mono (1, true)
  else IdentLetter.xi

/-- The odd source letters used in representative words: Xi and the permutation letters. -/
def eighthBindAllowed (l : Fin 10) : Bool := l.val = 0 ∨ 6 ≤ l.val

/-- Each allowed identification letter is the actual odd source letter. -/
theorem eighthBindIdent_local (l : Fin 10) (hl : eighthBindAllowed l = true) :
    localFiberIntoH (eighthBindIdent l).fiber = generatedAxisGlobalOddSourceLocalLetter l := by
  fin_cases l <;> simp [eighthBindAllowed] at hl <;>
    simp [eighthBindIdent, IdentLetter.fiber, generatedFourthMonomialFiberLetter,
      generatedAxisGlobalOddSourceLocalLetter, generatedAxisGlobalOddSourceBaseLocal]

/-- An allowed odd source word is the local element of its identification word. -/
theorem eighthBind_identWord (w : List (Fin 10)) (hw : w.all eighthBindAllowed = true) :
    identWordLocal (w.map eighthBindIdent) =
      (w.map generatedAxisGlobalOddSourceLocalLetter).prod := by
  induction w with
  | nil => simp [identWordLocal, identWordFiber]
  | cons l w ih =>
    rw [List.all_cons, Bool.and_eq_true] at hw
    rw [List.map_cons, List.map_cons, List.prod_cons, ← ih hw.2,
      show eighthBindIdent l :: w.map eighthBindIdent =
        [eighthBindIdent l] ++ w.map eighthBindIdent from rfl,
      identWordLocal_append, identWordLocal_singleton, eighthBindIdent_local l hw.1]

/-- The binary action of an odd source word on masks is the composed row action. -/
theorem eighthBind_oddProduct_binary (ls : List (Fin 10)) (b : ℕ) :
    co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode
        (ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalOddSourceRows l) x) b) := by
  induction ls generalizing b with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, LinearEquiv.mul_apply]
    rw [ih, generatedAxisGlobalOddSourceLocalLetter_binary]

/-- The inverse letter of an odd source letter. -/
def eighthBindFlip (l : Fin 10) : Fin 10 :=
  if h : l.val % 2 = 0 then ⟨l.val + 1, by have := l.isLt; omega⟩
  else ⟨l.val - 1, by have := l.isLt; omega⟩

/-- The inverse of an odd source letter is its flipped letter. -/
theorem eighthBind_letter_inv (l : Fin 10) :
    (generatedAxisGlobalOddSourceLocalLetter l)⁻¹ =
      generatedAxisGlobalOddSourceLocalLetter (eighthBindFlip l) := by
  fin_cases l <;> simp [generatedAxisGlobalOddSourceLocalLetter, eighthBindFlip]

/-- The inverse of an odd source word is the reversed word of flipped letters. -/
theorem eighthBind_prod_inv (w : List (Fin 10)) :
    ((w.map generatedAxisGlobalOddSourceLocalLetter).prod)⁻¹ =
      ((w.reverse.map eighthBindFlip).map generatedAxisGlobalOddSourceLocalLetter).prod := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, mul_inv_rev, ih, eighthBind_letter_inv,
      List.reverse_cons, List.map_append, List.map_append, List.prod_append]
    simp

/-- The binary-root mask of an odd source word. -/
def eighthBindRootMask (w : List (Fin 10)) : ℕ :=
  (w.reverse.map eighthBindFlip).foldr
    (fun l x => generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x) 2048

/-- The actual binary root of an odd source word has the computed mask. -/
theorem eighthBind_binaryRoot_odd (w : List (Fin 10)) :
    (generatedAxisGlobalBinaryRoot ((w.map generatedAxisGlobalOddSourceLocalLetter).prod)).val =
      monsterCo1GeometryBinaryMaskDecode (eighthBindRootMask w) := by
  change co1BinaryAction (projH ((w.map generatedAxisGlobalOddSourceLocalLetter).prod)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [eighthBind_prod_inv, ← generatedAxisGlobalTwelveEighthOmega_mask,
    eighthBind_oddProduct_binary]
  rfl

/-- A Conway element fixing the Ω mask lies in the binary Ω stabilizer. -/
theorem eighthBind_mem_frame_of_binary (g : Co1)
    (h : co1BinaryAction g (monsterCo1GeometryBinaryMaskDecode (n := 24) 2048) =
      monsterCo1GeometryBinaryMaskDecode (n := 24) 2048) :
    g ∈ co1OmegaFrameStabilizer := by
  change co1BinaryAction g (toAdd (qQuotHom sourceOmegaQ)) = toAdd (qQuotHom sourceOmegaQ)
  rw [← generatedAxisGlobalTwelveEighthOmega_mask]
  exact h

/-- The twelve Golay basis signs fix the binary Ω point. -/
theorem eighthBind_basis_sign_frame (k : Fin 12) :
    (QuotientGroup.mk (monsterCo1GeometrySignIsometry k) : Co1) ∈ co1OmegaFrameStabilizer := by
  apply eighthBind_mem_frame_of_binary
  rw [monsterCo1GeometrySign_binary]
  revert k
  decide +kernel

/-- Golay sign isometries multiply along the code. -/
theorem eighthBind_sign_add (a b : golayCode) :
    (QuotientGroup.mk (golaySignIsometry (a + b)) : Co1) =
      QuotientGroup.mk (golaySignIsometry a) * QuotientGroup.mk (golaySignIsometry b) := by
  have h := golaySignHom.map_mul (ofAdd a) (ofAdd b)
  change golaySignIsometry (a + b) = golaySignIsometry a * golaySignIsometry b at h
  rw [h]
  rfl

/-- Every Golay sign isometry fixes the binary Ω point. -/
theorem eighthBind_sign_frame (c : golayCode) :
    (QuotientGroup.mk (golaySignIsometry c) : Co1) ∈ co1OmegaFrameStabilizer := by
  obtain ⟨x, hx⟩ := c.property
  let f : Fin 12 → golayCode := fun k => ⟨golayEncoder (Pi.single k (x k)), ⟨_, rfl⟩⟩
  have hc : c = ∑ k : Fin 12, f k := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change c.val = ∑ k : Fin 12, golayEncoder (Pi.single k (x k))
    rw [← map_sum, Finset.univ_sum_single, hx]
  have hf : ∀ k : Fin 12, (QuotientGroup.mk (golaySignIsometry (f k)) : Co1) ∈
      co1OmegaFrameStabilizer := by
    intro k
    have hk : x k = 0 ∨ x k = 1 := by
      generalize x k = t
      fin_cases t <;> simp
    rcases hk with hk | hk
    · have h0 : f k = 0 := by
        apply Subtype.ext
        change golayEncoder (Pi.single k (x k)) = 0
        rw [hk, Pi.single_zero, map_zero]
      rw [h0]
      have h1 : golaySignIsometry 0 = 1 := golaySignHom.map_one
      rw [h1]
      exact one_mem _
    · have h1 : f k = monsterCo1GeometrySignCode k := by
        apply Subtype.ext
        change golayEncoder (Pi.single k (x k)) = golayEncoder (Pi.single k 1)
        rw [hk]
      rw [h1]
      exact eighthBind_basis_sign_frame k
  have hs : ∀ s : Finset (Fin 12), (QuotientGroup.mk (golaySignIsometry (∑ k ∈ s, f k)) : Co1) ∈
      co1OmegaFrameStabilizer := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      have h1 : golaySignIsometry 0 = 1 := golaySignHom.map_one
      rw [h1]
      exact one_mem _
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, eighthBind_sign_add]
      exact mul_mem (hf a) ih
  rw [hc]
  exact hs Finset.univ

/-- Letters other than Xi. -/
def eighthBindNoXi : IdentLetter → Bool
  | .xi => false
  | _ => true

/-- Every identification letter other than Xi fixes the binary Ω point. -/
theorem eighthBind_letter_frame (l : IdentLetter) (hl : eighthBindNoXi l = true) :
    projH (localFiberIntoH l.fiber) ∈ co1OmegaFrameStabilizer := by
  cases l with
  | xi => simp [eighthBindNoXi] at hl
  | sign a ε =>
    change projH (localFiberIntoH (generatedFifthSignFiber a ε)) ∈ _
    rw [generatedFifth_sign_fiber_local, generatedFifth_sign_local_projection]
    exact eighthBind_sign_frame _
  | mono l =>
    apply eighthBind_mem_frame_of_binary
    obtain ⟨i, b⟩ := l
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl <;> cases b
    · rw [show IdentLetter.mono (0, false) = eighthBindIdent 6 from rfl,
        eighthBindIdent_local 6 rfl, generatedAxisGlobalOddSourceLocalLetter_binary]
      decide +kernel
    · rw [show IdentLetter.mono (0, true) = eighthBindIdent 7 from rfl,
        eighthBindIdent_local 7 rfl, generatedAxisGlobalOddSourceLocalLetter_binary]
      decide +kernel
    · rw [show IdentLetter.mono (1, false) = eighthBindIdent 8 from rfl,
        eighthBindIdent_local 8 rfl, generatedAxisGlobalOddSourceLocalLetter_binary]
      decide +kernel
    · rw [show IdentLetter.mono (1, true) = eighthBindIdent 9 from rfl,
        eighthBindIdent_local 9 rfl, generatedAxisGlobalOddSourceLocalLetter_binary]
      decide +kernel
  | qel g =>
    change projH (inclQ g) ∈ _
    rw [projH_inclQ]
    exact one_mem _

/-- A word without Xi letters fixes the binary Ω point. -/
theorem eighthBind_prefix_frame (pre : List IdentLetter) (hp : pre.all eighthBindNoXi = true) :
    projH (identWordLocal pre) ∈ co1OmegaFrameStabilizer := by
  induction pre with
  | nil =>
    rw [show identWordLocal [] = 1 by simp [identWordLocal, identWordFiber], map_one]
    exact one_mem _
  | cons l pre ih =>
    rw [List.all_cons, Bool.and_eq_true] at hp
    rw [show l :: pre = [l] ++ pre from rfl, identWordLocal_append, identWordLocal_singleton,
      map_mul]
    exact mul_mem (eighthBind_letter_frame l hp.1) (ih hp.2)

/-- A left factor fixing the binary Ω point does not change the binary root. -/
theorem eighthBind_binaryRoot_frame (n r : H) (hn : projH n ∈ co1OmegaFrameStabilizer) :
    generatedAxisGlobalBinaryRoot (n * r) = generatedAxisGlobalBinaryRoot r := by
  apply Subtype.ext
  change co1BinaryAction (projH (n * r)⁻¹) (toAdd (qQuotHom sourceOmegaQ)) =
    co1BinaryAction (projH r⁻¹) (toAdd (qQuotHom sourceOmegaQ))
  have hn' : co1BinaryAction (projH n⁻¹) (toAdd (qQuotHom sourceOmegaQ)) =
      toAdd (qQuotHom sourceOmegaQ) := by
    have h1 := co1OmegaFrameStabilizer.inv_mem hn
    rw [← map_inv] at h1
    exact h1
  rw [mul_inv_rev, map_mul, map_mul, LinearEquiv.mul_apply, hn']

/-- The representative coset of a prefix and an allowed word has the binary root of the word. -/
theorem eighthBind_binaryRoot_rep (pre : List IdentLetter) (hp : pre.all eighthBindNoXi = true)
    (w : List (Fin 10)) (hw : w.all eighthBindAllowed = true) :
    (generatedAxisGlobalBinaryRoot (identWordLocal (pre ++ w.map eighthBindIdent))).val =
      monsterCo1GeometryBinaryMaskDecode (eighthBindRootMask w) := by
  rw [identWordLocal_append, eighthBind_binaryRoot_frame _ _ (eighthBind_prefix_frame pre hp),
    eighthBind_identWord w hw, eighthBind_binaryRoot_odd]

/-- The representative coset of a prefix and an allowed word. -/
def eighthBindRep (pre : List IdentLetter) (w : List (Fin 10)) : H :=
  identWordLocal (pre ++ w.map eighthBindIdent)

/-- A root binding from both triality images at one representative coset, matched to the root
mask by a word in the sixteen Eighth letters. -/
theorem eighthBind_rootBound (j : Fin 37) (pre : List IdentLetter)
    (hp : pre.all eighthBindNoXi = true) (w : List (Fin 10)) (hw : w.all eighthBindAllowed = true)
    (u : List (Fin 16))
    (hu : eighthForestWordApply u (generatedAxisGlobalTwelveEighthRootMask j) =
      eighthBindRootMask w)
    (hpos : sExtra (rhoLocal (eighthBindRep pre w) generatedEighthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : sExtra⁻¹ (rhoLocal (eighthBindRep pre w) generatedEighthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveEighthRootBound j :=
  generatedAxisGlobalTwelveEighthRootBound_of_word j _ u
    (generatedAxisGlobalTwelveEighthWord_root_mask j _ u _
      (eighthBind_binaryRoot_rep pre hp w hw) hu)
    hpos hneg

/-- A root binding from two explicit identifications of the triality images at the coset. -/
theorem eighthBind_rootBound_of_ids (j : Fin 37) (pre : List IdentLetter)
    (hp : pre.all eighthBindNoXi = true) (w : List (Fin 10)) (hw : w.all eighthBindAllowed = true)
    (u : List (Fin 16))
    (hu : eighthForestWordApply u (generatedAxisGlobalTwelveEighthRootMask j) =
      eighthBindRootMask w)
    (hpos : ∃ i : Fin 12, ∃ g : H, sExtra (rhoLocal (eighthBindRep pre w) generatedEighthAxis) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H, sExtra⁻¹ (rhoLocal (eighthBindRep pre w) generatedEighthAxis) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound j := by
  obtain ⟨i, g, hg⟩ := hpos
  obtain ⟨i', g', hg'⟩ := hneg
  exact eighthBind_rootBound j pre hp w hw u hu (generatedAxisGlobalTwelve_mem_of_transport i g hg)
    (generatedAxisGlobalTwelve_mem_of_transport i' g' hg')

/-- A root binding from a forward transport of a listed family into the representative coset,
with the other image of the source in the union. -/
theorem eighthBind_rootBound_of_forward (j : Fin 37) (pre : List IdentLetter)
    (hp : pre.all eighthBindNoXi = true) (w : List (Fin 10)) (hw : w.all eighthBindAllowed = true)
    (u : List (Fin 16))
    (hu : eighthForestWordApply u (generatedAxisGlobalTwelveEighthRootMask j) =
      eighthBindRootMask w)
    (i : Fin 12) (x : H)
    (htr : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal (eighthBindRep pre w) generatedEighthAxis)
    (hother : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveEighthRootBound j := by
  obtain ⟨c, hc, hcp⟩ := generatedAxisGlobalTwelveEighthWord_lift u
  have hroot : co1BinaryAction (projH c) (monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveEighthRootMask j)) =
        (generatedAxisGlobalBinaryRoot (eighthBindRep pre w)).val := by
    rw [hcp]
    exact generatedAxisGlobalTwelveEighthWord_root_mask j _ u _
      (eighthBind_binaryRoot_rep pre hp w hw) hu
  exact generatedAxisGlobalTwelveEighthRootBound_of_positive_transport j i x _ c hc hroot htr
    hother

/-- A root binding from an inverse transport of a listed family into the representative coset,
with the other image of the source in the union. -/
theorem eighthBind_rootBound_of_inverse (j : Fin 37) (pre : List IdentLetter)
    (hp : pre.all eighthBindNoXi = true) (w : List (Fin 10)) (hw : w.all eighthBindAllowed = true)
    (u : List (Fin 16))
    (hu : eighthForestWordApply u (generatedAxisGlobalTwelveEighthRootMask j) =
      eighthBindRootMask w)
    (i : Fin 12) (x : H)
    (htr : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal (eighthBindRep pre w) generatedEighthAxis)
    (hother : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveEighthRootBound j := by
  obtain ⟨c, hc, hcp⟩ := generatedAxisGlobalTwelveEighthWord_lift u
  have hroot : co1BinaryAction (projH c) (monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveEighthRootMask j)) =
        (generatedAxisGlobalBinaryRoot (eighthBindRep pre w)).val := by
    rw [hcp]
    exact generatedAxisGlobalTwelveEighthWord_root_mask j _ u _
      (eighthBind_binaryRoot_rep pre hp w hw) hu
  exact generatedAxisGlobalTwelveEighthRootBound_of_negative_transport j i x _ c hc hroot htr
    hother

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
