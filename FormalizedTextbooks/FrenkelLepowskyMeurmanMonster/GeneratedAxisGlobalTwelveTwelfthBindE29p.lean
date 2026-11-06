/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Eighth[42]+ <-> Twelfth[5]+ (record goctad:E29+, e = 1)

The identification `e29p_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word. -/
def tbE29pPrefix : List IdentLetter :=
  [.qel (qmElt (12278529, true)), .sign 497 0, .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, true),
  .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true)]

set_option maxRecDepth 100000 in
/-- The target word is the prefix followed by the identification word of Twelfth root `5`. -/
theorem tbE29pG_split :
    e29pW = tbE29pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 5 :=
  rfl

set_option maxRecDepth 100000 in
/-- The prefix consists of qualifying letters. -/
theorem tbE29pPrefix_ok : ∀ l ∈ tbE29pPrefix, SixthPhaseLetter l := by
  simp [tbE29pPrefix, SixthPhaseLetter]

set_option maxRecDepth 100000 in
/-- The prefix is Xi-free. -/
theorem tbE29pPrefix_xi : ∀ l ∈ tbE29pPrefix, l ≠ IdentLetter.xi := by
  simp [tbE29pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (flips the Ω mask). -/
theorem tbE29pPrefix_phase :
    qmWord (tbE29pPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbE29p_eq : sExtra (rhoLocal (identWordLocal e29H)
      (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal (tbE29pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 5))
      generatedTwelfthAxis := by
  have h := e29p_ident
  rw [tbE29pG_split] at h
  exact h

/-- The source image of the partner vector. -/
theorem tbE29p_src_mem : sExtra (rhoLocal (identWordLocal e29H)
      (generatedAxisGlobalTwelveRepresentative 7)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbE29p_eq

/-- The target image of Twelfth root `5` (sign from the phase of the prefix). -/
theorem twelfthRoot5_pos_E29p : sExtra (twelfthRootX 5) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_forward 5 7
    (identWordLocal e29H)
    tbE29pPrefix tbE29pPrefix_ok tbE29pPrefix_xi tbE29p_eq).2 tbE29pPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbE29p_partner : sExtra⁻¹ (rhoLocal (identWordLocal e29H)
      (generatedAxisGlobalTwelveRepresentative 7)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra⁻¹ (twelfthRootX 5) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_forward _ tbE29pPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 5) generatedTwelfthAxis
    tbE29pPrefix_ok tbE29pPrefix_xi tbE29p_eq).2 tbE29pPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
