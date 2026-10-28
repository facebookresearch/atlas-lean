/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF61nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF61nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF61nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentWords

/-! # The Tenth-Fourth identification T61- (gtenth)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the Tenth root image is the Fourth image
    (`ident_inverse_GMZ`); restated as
the Fourth partner record for Fourth partner word `3` (`tf61n_partner`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem tf61n_pair : pairTriGMZ 32 64 false tf61nL tf61nW tf61nHX tf61nGX ((tensorWordDenAll
    tf61nH : ℚ) * 32 / 2 ^ 21) ((tensorWordDenAll tf61nG : ℚ) * 1 / 2 ^ 4) = 128 := by
  rw [pairTriGMZ_parts tf61n_hok tf61n_hm tf61n_hp tf61n_hn tf61n_ha tf61n_hb tf61n_hc,
      tf61nH_den, tf61nG_den]
  norm_num [tf61nL, tf61nW]

/-- The identification T61- (gtenth): the triality image of the Tenth root image is the Fourth
    image. -/
theorem tf61n_ident : sExtra.symm (rhoLocal (identWordLocal tf61nH)
    (generatedAxisGlobalTwelveRepresentative 11)) =
    rhoLocal (identWordLocal tf61nG) (generatedAxisGlobalTwelveRepresentative 3) :=
  ident_inverse_GMZ 11 3 _ _ tf61nL tf61nW (ofList_ok tf61nHT tf61nHT_labels) (ofList_ok tf61nGT
      tf61nGT_labels) rfl rfl
    tf61nH_tensor.1 tf61nG_tensor.1 (by norm_num) (by norm_num) tf61nL_actual tf61nW_actual
        tf61n_pair

/-- The Xi-free prefix of the Fourth-side word. -/
def tf61nPrefix : List IdentLetter :=
  [.qel (qmElt (8886016, false)),
    .sign 460 0,
    .mono (1, false),
    .mono (0, false),
    .mono (1, false),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, false),
    .mono (0, false),
    .mono (0, false),
    .mono (0, false),
    .mono (0, false),
    .mono (1, true),
    .mono (0, true),
    .mono (1, true),
    .mono (0, false),
    .mono (1, true),
    .mono (0, false),
    .mono (0, false),
    .mono (1, true),
    .mono (0, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, true),
    .mono (0, true),
    .mono (1, true),
    .mono (0, false),
    .mono (0, false),
    .mono (1, true),
    .mono (0, false),
    .mono (0, false),
    .mono (0, false),
    .mono (1, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (1, false),
    .mono (0, false),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false),
    .mono (0, false),
    .mono (0, false),
    .mono (1, false),
    .mono (0, true),
    .mono (1, false),
    .mono (0, true),
    .mono (0, true),
    .mono (0, true),
    .mono (1, false)]

/-- The prefix of the Fourth-side word is Xi-free. -/
theorem tf61nPrefix_noXi : ∀ l ∈ tf61nPrefix, l ≠ IdentLetter.xi := by
  have h : tf61nPrefix.all (fun l => match l with | .xi => false | _ => true) = true := by
    decide +kernel
  intro l hl he
  subst he
  have h' := List.all_eq_true.mp h _ hl
  simp at h'

/-- The Fourth-side word is the Xi-free prefix times the translated Fourth partner word. -/
theorem tf61nG_eq : tf61nG = tf61nPrefix ++ fourthSourceWord (fourthPartnerWord 3) := rfl

/-- The partner record T61- in the form used by the Fourth assembly (Fourth partner word 3). -/
theorem tf61n_partner : ∃ n : List IdentLetter, (∀ l ∈ n, l ≠ IdentLetter.xi) ∧ ∃ i : Fin 12,
    FourthPartner n (fourthPartnerWord 3) (generatedAxisGlobalTwelveRepresentative i) := by
  refine ⟨tf61nPrefix, tf61nPrefix_noXi, 11, identWordLocal tf61nH, Or.inr ?_⟩
  rw [← tf61nG_eq]
  exact tf61n_ident

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
