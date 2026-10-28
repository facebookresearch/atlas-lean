/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGtwelfthW30p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Twelfth[30]- <-> Twelfth[30]+ (record gtwelfth:W30+, e = 1)

The factory identification `wGtwelfthW30p_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The source word is the identification word of Twelfth root `30`. -/
theorem tbW30pH_eq : wGtwelfthW30pH = generatedAxisGlobalTwelveTwelfthRootIdentWord 30 := rfl

/-- The Xi-free prefix of the target word. -/
def tbW30pPrefix : List IdentLetter :=
  [.qel (qmElt (1393900, true)), .sign 1188 0]

/-- The target word is the prefix followed by the identification word of Twelfth root `30`. -/
theorem tbW30pG_split :
    wGtwelfthW30pG = tbW30pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 30 :=
  rfl

/-- The prefix consists of qualifying letters. -/
theorem tbW30pPrefix_ok : ∀ l ∈ tbW30pPrefix, SixthPhaseLetter l := by
  simp [tbW30pPrefix, SixthPhaseLetter]

/-- The prefix is Xi-free. -/
theorem tbW30pPrefix_xi : ∀ l ∈ tbW30pPrefix, l ≠ IdentLetter.xi := by
  simp [tbW30pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (fixes the Ω mask). -/
theorem tbW30pPrefix_phase :
    qmWord (tbW30pPrefix.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbW30p_eq : sExtra (twelfthRootX 30) =
    rhoLocal (identWordLocal (tbW30pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 30))
      generatedTwelfthAxis := by
  have h := wGtwelfthW30p_ident
  rw [tbW30pH_eq, tbW30pG_split] at h
  exact h

/-- The source image of Twelfth root `30`. -/
theorem twelfthRoot30_pos_W30p : sExtra (twelfthRootX 30) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbW30p_eq

/-- The target image of Twelfth root `30` (sign from the phase of the prefix). -/
theorem twelfthRoot30_neg_W30p : sExtra⁻¹ (twelfthRootX 30) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_forward 30 10
    (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord 30))
    tbW30pPrefix tbW30pPrefix_ok tbW30pPrefix_xi tbW30p_eq).1 tbW30pPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
