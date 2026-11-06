/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentR3p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root 37 from grecip's identification Fourth[9]+ <-> Twelfth[37]+ (record grecip:F3+)

`fourthR3p_ident` identifies the positive image of the Fourth root 3 vector with the Twelfth root
37 vector behind an Xi-free prefix whose Q-phase flips the Ω mask: this binds the positive image of
the Twelfth root 37 vector.  The inverse image of the Fourth root 3 vector is bound by grecip's
`fourth_root3_bound` (Fourth root 3 is phase merged), and the partner-vertex transport turns it into
the inverse image of the Twelfth root 37 vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word of `fourthR3p_ident`. -/
def tbR3pPrefix : List IdentLetter :=
  [.qel (qmElt (10253170, true)), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (1, true), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false),
  .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, true),
  .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, true),
  .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false)]

set_option maxRecDepth 100000 in
/-- The target word is the prefix followed by the identification word of Twelfth root `37`. -/
theorem tbR3pG_split :
    fourthR3pG = tbR3pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 37 :=
  rfl

set_option maxRecDepth 100000 in
/-- The prefix consists of qualifying letters. -/
theorem tbR3pPrefix_ok : ∀ l ∈ tbR3pPrefix, SixthPhaseLetter l := by
  simp [tbR3pPrefix, SixthPhaseLetter]

set_option maxRecDepth 100000 in
/-- The prefix is Xi-free. -/
theorem tbR3pPrefix_xi : ∀ l ∈ tbR3pPrefix, l ≠ IdentLetter.xi := by
  simp [tbR3pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (flips the Ω mask). -/
theorem tbR3pPrefix_phase :
    qmWord (tbR3pPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbR3p_eq : sExtra (rhoLocal (identWordLocal fourthR3pH)
    (generatedAxisGlobalTwelveRepresentative 3)) =
      rhoLocal (identWordLocal (tbR3pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 37))
        generatedTwelfthAxis := by
  rw [← tbR3pG_split]
  exact fourthR3p_ident

/-- The positive image of the Twelfth root 37 vector. -/
theorem twelfthRoot37_pos_R3p : sExtra (twelfthRootX 37) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_forward 37 3 (identWordLocal fourthR3pH) tbR3pPrefix tbR3pPrefix_ok
    tbR3pPrefix_xi tbR3p_eq).2 tbR3pPrefix_phase

/-- The inverse image of the Fourth root 3 vector, written as the source of `fourthR3p_ident`. -/
theorem tbR3p_src_neg : sExtra⁻¹ (rhoLocal (identWordLocal fourthR3pH)
    (generatedAxisGlobalTwelveRepresentative 3)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have h := fourth_root3_bound.2
  rw [show generatedAxisGlobalTwelveFourthRootLocal 3 =
      ((generatedAxisGlobalTwelveFourthRootWords 3).map
        generatedAxisGlobalOddSourceLocalLetter).prod from rfl, fourthSourceWord_apply] at h
  exact h

/-- The inverse image of the Twelfth root 37 vector (partner vertex of `fourthR3p_ident`). -/
theorem twelfthRoot37_neg_R3p : sExtra⁻¹ (twelfthRootX 37) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ((twelfth_partner_forward _ tbR3pPrefix (generatedAxisGlobalTwelveTwelfthRootIdentWord 37)
    generatedTwelfthAxis tbR3pPrefix_ok tbR3pPrefix_xi tbR3p_eq).2 tbR3pPrefix_phase).mp
    tbR3p_src_neg

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
