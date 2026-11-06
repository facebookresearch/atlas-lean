/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Twelfth[9]+ <-> Twelfth[21]- (record gtwelfth:W9+, e = 1)

The factory identification `twGtwelfthW9p_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The source word is the identification word of Twelfth root `9`. -/
theorem tbW9pH_eq : twGtwelfthW9pH = generatedAxisGlobalTwelveTwelfthRootIdentWord 9 := rfl

/-- The Xi-free prefix of the target word. -/
def tbW9pPrefix : List IdentLetter :=
  [.qel (qmElt (4978302, false)), .sign 471 0, .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false)]

/-- The target word is the prefix followed by the identification word of Twelfth root `21`. -/
theorem tbW9pG_split :
    twGtwelfthW9pG = tbW9pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 21 :=
  rfl

/-- The prefix consists of qualifying letters. -/
theorem tbW9pPrefix_ok : ∀ l ∈ tbW9pPrefix, SixthPhaseLetter l := by
  simp [tbW9pPrefix, SixthPhaseLetter]

/-- The prefix is Xi-free. -/
theorem tbW9pPrefix_xi : ∀ l ∈ tbW9pPrefix, l ≠ IdentLetter.xi := by
  simp [tbW9pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (fixes the Ω mask). -/
theorem tbW9pPrefix_phase :
    qmWord (tbW9pPrefix.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbW9p_eq : sExtra (twelfthRootX 9) =
    rhoLocal (identWordLocal (tbW9pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 21))
      generatedTwelfthAxis := by
  have h := twGtwelfthW9p_ident
  rw [tbW9pH_eq, tbW9pG_split] at h
  exact h

/-- The source image of Twelfth root `9`. -/
theorem twelfthRoot9_pos_W9p : sExtra (twelfthRootX 9) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbW9p_eq

/-- The target image of Twelfth root `21` (sign from the phase of the prefix). -/
theorem twelfthRoot21_neg_W9p : sExtra⁻¹ (twelfthRootX 21) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_forward 21 10
    (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord 9))
    tbW9pPrefix tbW9pPrefix_ok tbW9pPrefix_xi tbW9p_eq).1 tbW9pPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbW9p_partner : sExtra⁻¹ (twelfthRootX 9) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra (twelfthRootX 21) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_forward _ tbW9pPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 21) generatedTwelfthAxis
    tbW9pPrefix_ok tbW9pPrefix_xi tbW9p_eq).1 tbW9pPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
