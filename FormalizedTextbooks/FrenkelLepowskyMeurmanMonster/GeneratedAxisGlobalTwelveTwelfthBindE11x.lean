/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11x
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Eighth[15]- <-> Twelfth[23]- (record goctad:E11-, e = -1)

The identification `e11x_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word. -/
def tbE11xPrefix : List IdentLetter :=
  [.qel (qmElt (9394757, false)), .sign 1023 0, .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, true),
  .mono (0, true), .mono (1, true), .mono (0, true), .mono (0, true),
  .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false),
  .mono (1, true), .mono (0, true), .mono (0, true), .mono (1, true),
  .mono (0, true), .mono (1, true), .mono (0, true), .mono (0, true),
  .mono (0, true), .mono (1, true), .mono (0, false), .mono (1, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false)]

set_option maxRecDepth 100000 in
/-- The target word is the prefix followed by the identification word of Twelfth root `23`. -/
theorem tbE11xG_split :
    e11xW = tbE11xPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 23 :=
  rfl

set_option maxRecDepth 100000 in
/-- The prefix consists of qualifying letters. -/
theorem tbE11xPrefix_ok : ∀ l ∈ tbE11xPrefix, SixthPhaseLetter l := by
  simp [tbE11xPrefix, SixthPhaseLetter]

set_option maxRecDepth 100000 in
/-- The prefix is Xi-free. -/
theorem tbE11xPrefix_xi : ∀ l ∈ tbE11xPrefix, l ≠ IdentLetter.xi := by
  simp [tbE11xPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (flips the Ω mask). -/
theorem tbE11xPrefix_phase :
    qmWord (tbE11xPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbE11x_eq : sExtra⁻¹ (rhoLocal (identWordLocal e11H)
      (generatedAxisGlobalTwelveRepresentative 7)) =
    rhoLocal (identWordLocal (tbE11xPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 23))
      generatedTwelfthAxis := by
  have h := e11x_ident
  rw [tbE11xG_split] at h
  exact h

/-- The source image of the partner vector. -/
theorem tbE11x_src_mem : sExtra⁻¹ (rhoLocal (identWordLocal e11H)
      (generatedAxisGlobalTwelveRepresentative 7)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbE11x_eq

/-- The target image of Twelfth root `23` (sign from the phase of the prefix). -/
theorem twelfthRoot23_neg_E11x : sExtra⁻¹ (twelfthRootX 23) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_inverse 23 7
    (identWordLocal e11H)
    tbE11xPrefix tbE11xPrefix_ok tbE11xPrefix_xi tbE11x_eq).2 tbE11xPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbE11x_partner : sExtra (rhoLocal (identWordLocal e11H)
      (generatedAxisGlobalTwelveRepresentative 7)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra (twelfthRootX 23) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_inverse _ tbE11xPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 23) generatedTwelfthAxis
    tbE11xPrefix_ok tbE11xPrefix_xi tbE11x_eq).2 tbE11xPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
