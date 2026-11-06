/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdC9p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Seventh[15]+ <-> Twelfth[33]- (record gforest:S7c9+, e = 1)

The identification `s7c9p_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word. -/
def tbS7c9pPrefix : List IdentLetter :=
  [.qel (qmElt (4036430, false)), .sign 1831 0, .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false),
  .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, true),
  .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (0, false)]

set_option maxRecDepth 100000 in
/-- The target word is the prefix followed by the identification word of Twelfth root `33`. -/
theorem tbS7c9pG_split :
    s7c9pG = tbS7c9pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 33 :=
  rfl

set_option maxRecDepth 100000 in
/-- The prefix consists of qualifying letters. -/
theorem tbS7c9pPrefix_ok : ∀ l ∈ tbS7c9pPrefix, SixthPhaseLetter l := by
  simp [tbS7c9pPrefix, SixthPhaseLetter]

set_option maxRecDepth 100000 in
/-- The prefix is Xi-free. -/
theorem tbS7c9pPrefix_xi : ∀ l ∈ tbS7c9pPrefix, l ≠ IdentLetter.xi := by
  simp [tbS7c9pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (fixes the Ω mask). -/
theorem tbS7c9pPrefix_phase :
    qmWord (tbS7c9pPrefix.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbS7c9p_eq : sExtra (rhoLocal (identWordLocal s7c9pH)
      (generatedAxisGlobalTwelveRepresentative 6)) =
    rhoLocal (identWordLocal (tbS7c9pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 33))
      generatedTwelfthAxis := by
  have h := s7c9p_ident
  rw [tbS7c9pG_split] at h
  exact h

/-- The source image of the partner vector. -/
theorem tbS7c9p_src_mem : sExtra (rhoLocal (identWordLocal s7c9pH)
      (generatedAxisGlobalTwelveRepresentative 6)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbS7c9p_eq

/-- The target image of Twelfth root `33` (sign from the phase of the prefix). -/
theorem twelfthRoot33_neg_S7c9p : sExtra⁻¹ (twelfthRootX 33) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_forward 33 6
    (identWordLocal s7c9pH)
    tbS7c9pPrefix tbS7c9pPrefix_ok tbS7c9pPrefix_xi tbS7c9p_eq).1 tbS7c9pPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbS7c9p_partner : sExtra⁻¹ (rhoLocal (identWordLocal s7c9pH)
      (generatedAxisGlobalTwelveRepresentative 6)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra (twelfthRootX 33) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_forward _ tbS7c9pPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 33) generatedTwelfthAxis
    tbS7c9pPrefix_ok tbS7c9pPrefix_xi tbS7c9p_eq).1 tbS7c9pPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
