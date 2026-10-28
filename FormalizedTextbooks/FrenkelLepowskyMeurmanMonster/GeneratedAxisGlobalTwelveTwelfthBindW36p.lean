/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Twelfth[36]+ <-> Twelfth[36]+ (record gtwelfth:W36+, e = 1)

The identification `twGtwelfthW36p_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The source word is the identification word of Twelfth root `36`. -/
theorem tbW36pH_eq : twGtwelfthW36pH = generatedAxisGlobalTwelveTwelfthRootIdentWord 36 := rfl

/-- The Xi-free prefix of the target word. -/
def tbW36pPrefix : List IdentLetter :=
  [.qel (qmElt (15709496, true)), .sign 1336 0]

set_option maxRecDepth 100000 in
/-- The target word is the prefix followed by the identification word of Twelfth root `36`. -/
theorem tbW36pG_split :
    twGtwelfthW36pG = tbW36pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 36 :=
  rfl

set_option maxRecDepth 100000 in
/-- The prefix consists of qualifying letters. -/
theorem tbW36pPrefix_ok : ∀ l ∈ tbW36pPrefix, SixthPhaseLetter l := by
  simp [tbW36pPrefix, SixthPhaseLetter]

set_option maxRecDepth 100000 in
/-- The prefix is Xi-free. -/
theorem tbW36pPrefix_xi : ∀ l ∈ tbW36pPrefix, l ≠ IdentLetter.xi := by
  simp [tbW36pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (flips the Ω mask). -/
theorem tbW36pPrefix_phase :
    qmWord (tbW36pPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbW36p_eq : sExtra (twelfthRootX 36) =
    rhoLocal (identWordLocal (tbW36pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 36))
      generatedTwelfthAxis := by
  have h := twGtwelfthW36p_ident
  rw [tbW36pH_eq, tbW36pG_split] at h
  exact h

/-- The source image of Twelfth root `36`. -/
theorem twelfthRoot36_pos_W36p : sExtra (twelfthRootX 36) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbW36p_eq

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
