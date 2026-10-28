/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Root8[12]- <-> Twelfth[34]- (record r8f:R86-, e = -1)

The identification `wR8fR86n_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word. -/
def tbR86nPrefix : List IdentLetter :=
  [.qel (qmElt (10279572, false)), .sign 1857 0, .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false)]

set_option maxRecDepth 100000 in
/-- The target word is the prefix followed by the identification word of Twelfth root `34`. -/
theorem tbR86nG_split :
    wR8fR86nG = tbR86nPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 34 :=
  rfl

set_option maxRecDepth 100000 in
/-- The prefix consists of qualifying letters. -/
theorem tbR86nPrefix_ok : ∀ l ∈ tbR86nPrefix, SixthPhaseLetter l := by
  simp [tbR86nPrefix, SixthPhaseLetter]

set_option maxRecDepth 100000 in
/-- The prefix is Xi-free. -/
theorem tbR86nPrefix_xi : ∀ l ∈ tbR86nPrefix, l ≠ IdentLetter.xi := by
  simp [tbR86nPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (flips the Ω mask). -/
theorem tbR86nPrefix_phase :
    qmWord (tbR86nPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbR86n_eq : sExtra⁻¹ (rhoLocal (identWordLocal wR8fR86nH)
      (generatedAxisGlobalTwelveRepresentative 9)) =
    rhoLocal (identWordLocal (tbR86nPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 34))
      generatedTwelfthAxis := by
  have h := wR8fR86n_ident
  rw [tbR86nG_split] at h
  exact h

/-- The source image of the partner vector. -/
theorem tbR86n_src_mem : sExtra⁻¹ (rhoLocal (identWordLocal wR8fR86nH)
      (generatedAxisGlobalTwelveRepresentative 9)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbR86n_eq

/-- The target image of Twelfth root `34` (sign from the phase of the prefix). -/
theorem twelfthRoot34_neg_R86n : sExtra⁻¹ (twelfthRootX 34) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_inverse 34 9
    (identWordLocal wR8fR86nH)
    tbR86nPrefix tbR86nPrefix_ok tbR86nPrefix_xi tbR86n_eq).2 tbR86nPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbR86n_partner : sExtra (rhoLocal (identWordLocal wR8fR86nH)
      (generatedAxisGlobalTwelveRepresentative 9)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra (twelfthRootX 34) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_inverse _ tbR86nPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 34) generatedTwelfthAxis
    tbR86nPrefix_ok tbR86nPrefix_xi tbR86n_eq).2 tbR86nPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
