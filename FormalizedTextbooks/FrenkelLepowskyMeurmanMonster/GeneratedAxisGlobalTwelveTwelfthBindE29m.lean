/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29m
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Eighth[42]- <-> Twelfth[5]+ (record goctad:E29-, e = -1)

The identification `e29m_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word. -/
def tbE29mPrefix : List IdentLetter :=
  [.qel (qmElt (2878259, true)), .sign 512 0, .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, true),
  .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, true),
  .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true),
  .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false),
  .mono (1, true), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true)]

set_option maxRecDepth 100000 in
/-- The target word is the prefix followed by the identification word of Twelfth root `5`. -/
theorem tbE29mG_split :
    e29mW = tbE29mPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 5 :=
  rfl

set_option maxRecDepth 100000 in
/-- The prefix consists of qualifying letters. -/
theorem tbE29mPrefix_ok : ∀ l ∈ tbE29mPrefix, SixthPhaseLetter l := by
  simp [tbE29mPrefix, SixthPhaseLetter]

set_option maxRecDepth 100000 in
/-- The prefix is Xi-free. -/
theorem tbE29mPrefix_xi : ∀ l ∈ tbE29mPrefix, l ≠ IdentLetter.xi := by
  simp [tbE29mPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (fixes the Ω mask). -/
theorem tbE29mPrefix_phase :
    qmWord (tbE29mPrefix.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbE29m_eq : sExtra⁻¹ (rhoLocal (identWordLocal e29H)
      (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal (tbE29mPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 5))
      generatedTwelfthAxis := by
  have h := e29m_ident
  rw [tbE29mG_split] at h
  exact h

/-- The source image of the partner vector. -/
theorem tbE29m_src_mem : sExtra⁻¹ (rhoLocal (identWordLocal e29H)
      (generatedAxisGlobalTwelveRepresentative 7)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbE29m_eq

/-- The target image of Twelfth root `5` (sign from the phase of the prefix). -/
theorem twelfthRoot5_pos_E29m : sExtra (twelfthRootX 5) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_inverse 5 7
    (identWordLocal e29H)
    tbE29mPrefix tbE29mPrefix_ok tbE29mPrefix_xi tbE29m_eq).1 tbE29mPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbE29m_partner : sExtra (rhoLocal (identWordLocal e29H)
      (generatedAxisGlobalTwelveRepresentative 7)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra⁻¹ (twelfthRootX 5) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_inverse _ tbE29mPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 5) generatedTwelfthAxis
    tbE29mPrefix_ok tbE29mPrefix_xi tbE29m_eq).1 tbE29mPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
