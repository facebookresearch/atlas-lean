/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3pX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Ninth[5]+ <-> Twelfth[31]+ (record gninth:N3+, e = 1)

The identification `wGninthN3pX_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word. -/
def tbN3pPrefix : List IdentLetter :=
  [.qel (qmElt (10438696, true)), .sign 399 0, .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (1, false)]

/-- The target word is the prefix followed by the identification word of Twelfth root `31`. -/
theorem tbN3pG_split :
    wGninthN3pXG = tbN3pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 31 :=
  rfl

/-- The prefix consists of qualifying letters. -/
theorem tbN3pPrefix_ok : ∀ l ∈ tbN3pPrefix, SixthPhaseLetter l := by
  simp [tbN3pPrefix, SixthPhaseLetter]

/-- The prefix is Xi-free. -/
theorem tbN3pPrefix_xi : ∀ l ∈ tbN3pPrefix, l ≠ IdentLetter.xi := by
  simp [tbN3pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (flips the Ω mask). -/
theorem tbN3pPrefix_phase :
    qmWord (tbN3pPrefix.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbN3p_eq : sExtra (rhoLocal (identWordLocal wGninthN3pXH)
      (generatedAxisGlobalTwelveRepresentative 8)) =
    rhoLocal (identWordLocal (tbN3pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 31))
      generatedTwelfthAxis := by
  have h := wGninthN3pX_ident
  rw [tbN3pG_split] at h
  exact h

/-- The source image of the partner vector. -/
theorem tbN3p_src_mem : sExtra (rhoLocal (identWordLocal wGninthN3pXH)
      (generatedAxisGlobalTwelveRepresentative 8)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbN3p_eq

/-- The target image of Twelfth root `31` (sign from the phase of the prefix). -/
theorem twelfthRoot31_pos_N3p : sExtra (twelfthRootX 31) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_forward 31 8
    (identWordLocal wGninthN3pXH)
    tbN3pPrefix tbN3pPrefix_ok tbN3pPrefix_xi tbN3p_eq).2 tbN3pPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbN3p_partner : sExtra⁻¹ (rhoLocal (identWordLocal wGninthN3pXH)
      (generatedAxisGlobalTwelveRepresentative 8)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra⁻¹ (twelfthRootX 31) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_forward _ tbN3pPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 31) generatedTwelfthAxis
    tbN3pPrefix_ok tbN3pPrefix_xi tbN3p_eq).2 tbN3pPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
