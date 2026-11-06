/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Root8[11]- <-> Twelfth[29]- (record r8f:R83-, e = -1)

The identification `wR8fR83n_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word. -/
def tbR83nPrefix : List IdentLetter :=
  [.qel (qmElt (16715351, false)), .sign 933 0, .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false)]

/-- The target word is the prefix followed by the identification word of Twelfth root `29`. -/
theorem tbR83nG_split :
    wR8fR83nG = tbR83nPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 29 :=
  rfl

/-- The prefix consists of qualifying letters. -/
theorem tbR83nPrefix_ok : ∀ l ∈ tbR83nPrefix, SixthPhaseLetter l := by
  simp [tbR83nPrefix, SixthPhaseLetter]

/-- The prefix is Xi-free. -/
theorem tbR83nPrefix_xi : ∀ l ∈ tbR83nPrefix, l ≠ IdentLetter.xi := by
  simp [tbR83nPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (flips the Ω mask). -/
theorem tbR83nPrefix_phase :
    qmWord (tbR83nPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbR83n_eq : sExtra⁻¹ (rhoLocal (identWordLocal wR8fR83nH)
      (generatedAxisGlobalTwelveRepresentative 9)) =
    rhoLocal (identWordLocal (tbR83nPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 29))
      generatedTwelfthAxis := by
  have h := wR8fR83n_ident
  rw [tbR83nG_split] at h
  exact h

/-- The source image of the partner vector. -/
theorem tbR83n_src_mem : sExtra⁻¹ (rhoLocal (identWordLocal wR8fR83nH)
      (generatedAxisGlobalTwelveRepresentative 9)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbR83n_eq

/-- The target image of Twelfth root `29` (sign from the phase of the prefix). -/
theorem twelfthRoot29_neg_R83n : sExtra⁻¹ (twelfthRootX 29) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_inverse 29 9
    (identWordLocal wR8fR83nH)
    tbR83nPrefix tbR83nPrefix_ok tbR83nPrefix_xi tbR83n_eq).2 tbR83nPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbR83n_partner : sExtra (rhoLocal (identWordLocal wR8fR83nH)
      (generatedAxisGlobalTwelveRepresentative 9)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra (twelfthRootX 29) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_inverse _ tbR83nPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 29) generatedTwelfthAxis
    tbR83nPrefix_ok tbR83nPrefix_xi tbR83n_eq).2 tbR83nPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
