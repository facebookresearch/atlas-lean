/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentWords

/-! # The Tenth-Fourth identification T64+ (gtenth)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the Tenth root image is the Fourth image
    (`ident_forward_GMZ`); restated as
the Fourth partner record for Fourth partner word `2` (`tf64p_partner`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem tf64p_pair : pairTriGMZ 32 64 true tf64pL tf64pW tf64pHX tf64pGX ((tensorWordDenAll tf64pH
    : ℚ) * 32 / 2 ^ 13) ((tensorWordDenAll tf64pG : ℚ) * 1 / 2 ^ 8) = 128 := by
  rw [pairTriGMZ_parts tf64p_hok tf64p_hm tf64p_hp tf64p_hn tf64p_ha tf64p_hb tf64p_hc,
      tf64pH_den, tf64pG_den]
  norm_num [tf64pL, tf64pW]

/-- The identification T64+ (gtenth): the triality image of the Tenth root image is the Fourth
    image. -/
theorem tf64p_ident : sExtra (rhoLocal (identWordLocal tf64pH)
    (generatedAxisGlobalTwelveRepresentative 11)) =
    rhoLocal (identWordLocal tf64pG) (generatedAxisGlobalTwelveRepresentative 3) :=
  ident_forward_GMZ 11 3 _ _ tf64pL tf64pW (ofList_ok tf64pHT tf64pHT_labels) (ofList_ok tf64pGT
      tf64pGT_labels) rfl rfl
    tf64pH_tensor.1 tf64pG_tensor.1 (by norm_num) (by norm_num) tf64pL_actual tf64pW_actual
        tf64p_pair

/-- The Xi-free prefix of the Fourth-side word. -/
def tf64pPrefix : List IdentLetter :=
  [.qel (qmElt (10686720, false)),
    .sign 250 0,
    .mono (0, false),
    .mono (1, false),
    .mono (0, false),
    .mono (1, false),
    .mono (0, false),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, false),
    .mono (1, false),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, false),
    .mono (0, false),
    .mono (0, false),
    .mono (1, true),
    .mono (0, true),
    .mono (1, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, true),
    .mono (0, false),
    .mono (1, true),
    .mono (0, false),
    .mono (0, false),
    .mono (1, true),
    .mono (0, false),
    .mono (1, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, true),
    .mono (0, false),
    .mono (1, true),
    .mono (0, true),
    .mono (1, true),
    .mono (0, false),
    .mono (1, false),
    .mono (0, true),
    .mono (1, false),
    .mono (0, false),
    .mono (0, false),
    .mono (0, false),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, false),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (1, false),
    .mono (0, false),
    .mono (0, false)]

/-- The prefix of the Fourth-side word is Xi-free. -/
theorem tf64pPrefix_noXi : ∀ l ∈ tf64pPrefix, l ≠ IdentLetter.xi := by
  have h : tf64pPrefix.all (fun l => match l with | .xi => false | _ => true) = true := by
    decide +kernel
  intro l hl he
  subst he
  have h' := List.all_eq_true.mp h _ hl
  simp at h'

/-- The Fourth-side word is the Xi-free prefix times the translated Fourth partner word. -/
theorem tf64pG_eq : tf64pG = tf64pPrefix ++ fourthSourceWord (fourthPartnerWord 2) := rfl

/-- The partner record T64+ in the form used by the Fourth assembly (Fourth partner word 2). -/
theorem tf64p_partner : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
    FourthPartner n (fourthPartnerWord 2) (generatedAxisGlobalTwelveRepresentative i) := by
  refine ⟨tf64pPrefix, tf64pPrefix_noXi, 11, identWordLocal tf64pH, Or.inl ?_⟩
  rw [← tf64pG_eq]
  exact tf64p_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
