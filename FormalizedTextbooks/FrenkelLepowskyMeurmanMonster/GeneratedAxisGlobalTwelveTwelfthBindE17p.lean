/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Eighth[22]+ <-> Twelfth[35]- (record goctad:E17+, e = 1)

The identification `e17p_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word. -/
def tbE17pPrefix : List IdentLetter :=
  [.qel (qmElt (2555742, true)), .sign 37 0, .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, true),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true),
  .mono (1, true), .mono (0, true), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (1, true), .mono (0, false), .mono (1, true),
  .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false)]

set_option maxRecDepth 100000 in
/-- The target word is the prefix followed by the identification word of Twelfth root `35`. -/
theorem tbE17pG_split :
    e17pW = tbE17pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 35 :=
  rfl

set_option maxRecDepth 100000 in
/-- The prefix consists of qualifying letters. -/
theorem tbE17pPrefix_ok : ∀ l ∈ tbE17pPrefix, SixthPhaseLetter l := by
  simp [tbE17pPrefix, SixthPhaseLetter]

set_option maxRecDepth 100000 in
/-- The prefix is Xi-free. -/
theorem tbE17pPrefix_xi : ∀ l ∈ tbE17pPrefix, l ≠ IdentLetter.xi := by
  simp [tbE17pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (fixes the Ω mask). -/
theorem tbE17pPrefix_phase :
    qmWord (tbE17pPrefix.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbE17p_eq : sExtra (rhoLocal (identWordLocal e17H)
      (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal (tbE17pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 35))
      generatedTwelfthAxis := by
  have h := e17p_ident
  rw [tbE17pG_split] at h
  exact h

/-- The source image of the partner vector. -/
theorem tbE17p_src_mem : sExtra (rhoLocal (identWordLocal e17H)
      (generatedAxisGlobalTwelveRepresentative 7)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbE17p_eq

/-- The target image of Twelfth root `35` (sign from the phase of the prefix). -/
theorem twelfthRoot35_neg_E17p : sExtra⁻¹ (twelfthRootX 35) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_forward 35 7
    (identWordLocal e17H)
    tbE17pPrefix tbE17pPrefix_ok tbE17pPrefix_xi tbE17p_eq).1 tbE17pPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbE17p_partner : sExtra⁻¹ (rhoLocal (identWordLocal e17H)
      (generatedAxisGlobalTwelveRepresentative 7)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra (twelfthRootX 35) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_forward _ tbE17pPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 35) generatedTwelfthAxis
    tbE17pPrefix_ok tbE17pPrefix_xi tbE17p_eq).1 tbE17pPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
