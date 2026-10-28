/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Twelfth[9]+ <-> Twelfth[21]+ (record gtwelfth:W21+, e = 1)

The factory identification `twGtwelfthW21p_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The source word is the identification word of Twelfth root `21`. -/
theorem tbW21pH_eq : twGtwelfthW21pH = generatedAxisGlobalTwelveTwelfthRootIdentWord 21 := rfl

/-- The Xi-free prefix of the target word. -/
def tbW21pPrefix : List IdentLetter :=
  [.qel (qmElt (10930072, true)), .sign 860 0, .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true)]

/-- The target word is the prefix followed by the identification word of Twelfth root `9`. -/
theorem tbW21pG_split :
    twGtwelfthW21pG = tbW21pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 9 :=
  rfl

/-- The prefix consists of qualifying letters. -/
theorem tbW21pPrefix_ok : ∀ l ∈ tbW21pPrefix, SixthPhaseLetter l := by
  simp [tbW21pPrefix, SixthPhaseLetter]

/-- The prefix is Xi-free. -/
theorem tbW21pPrefix_xi : ∀ l ∈ tbW21pPrefix, l ≠ IdentLetter.xi := by
  simp [tbW21pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (flips the Ω mask). -/
theorem tbW21pPrefix_phase :
    qmWord (tbW21pPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbW21p_eq : sExtra (twelfthRootX 21) =
    rhoLocal (identWordLocal (tbW21pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 9))
      generatedTwelfthAxis := by
  have h := twGtwelfthW21p_ident
  rw [tbW21pH_eq, tbW21pG_split] at h
  exact h

/-- The source image of Twelfth root `21`. -/
theorem twelfthRoot21_pos_W21p : sExtra (twelfthRootX 21) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbW21p_eq

/-- The target image of Twelfth root `9` (sign from the phase of the prefix). -/
theorem twelfthRoot9_pos_W21p : sExtra (twelfthRootX 9) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_forward 9 10
    (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord 21))
    tbW21pPrefix tbW21pPrefix_ok tbW21pPrefix_xi tbW21p_eq).2 tbW21pPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbW21p_partner : sExtra⁻¹ (twelfthRootX 21) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra⁻¹ (twelfthRootX 9) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_forward _ tbW21pPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 9) generatedTwelfthAxis
    tbW21pPrefix_ok tbW21pPrefix_xi tbW21p_eq).2 tbW21pPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
