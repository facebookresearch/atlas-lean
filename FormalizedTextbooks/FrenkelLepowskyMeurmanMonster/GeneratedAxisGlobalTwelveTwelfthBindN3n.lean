/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN3nX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Ninth[5]- <-> Twelfth[31]+ (record gninth:N3-, e = -1)

The identification `wGninthN3nX_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The Xi-free prefix of the target word. -/
def tbN3nPrefix : List IdentLetter :=
  [.qel (qmElt (2063253, false)), .sign 639 0, .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (1, false)]

/-- The target word is the prefix followed by the identification word of Twelfth root `31`. -/
theorem tbN3nG_split :
    wGninthN3nXG = tbN3nPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 31 :=
  rfl

/-- The prefix consists of qualifying letters. -/
theorem tbN3nPrefix_ok : ∀ l ∈ tbN3nPrefix, SixthPhaseLetter l := by
  simp [tbN3nPrefix, SixthPhaseLetter]

/-- The prefix is Xi-free. -/
theorem tbN3nPrefix_xi : ∀ l ∈ tbN3nPrefix, l ≠ IdentLetter.xi := by
  simp [tbN3nPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (fixes the Ω mask). -/
theorem tbN3nPrefix_phase :
    qmWord (tbN3nPrefix.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbN3n_eq : sExtra⁻¹ (rhoLocal (identWordLocal wGninthN3nXH)
      (generatedAxisGlobalTwelveRepresentative 8)) =
    rhoLocal (identWordLocal (tbN3nPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 31))
      generatedTwelfthAxis := by
  have h := wGninthN3nX_ident
  rw [tbN3nG_split] at h
  exact h

/-- The source image of the partner vector. -/
theorem tbN3n_src_mem : sExtra⁻¹ (rhoLocal (identWordLocal wGninthN3nXH)
      (generatedAxisGlobalTwelveRepresentative 8)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbN3n_eq

/-- The target image of Twelfth root `31` (sign from the phase of the prefix). -/
theorem twelfthRoot31_pos_N3n : sExtra (twelfthRootX 31) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_inverse 31 8
    (identWordLocal wGninthN3nXH)
    tbN3nPrefix tbN3nPrefix_ok tbN3nPrefix_xi tbN3n_eq).1 tbN3nPrefix_phase

/-- The remaining images of the two triangles are bound together. -/
theorem tbN3n_partner : sExtra (rhoLocal (identWordLocal wGninthN3nXH)
      (generatedAxisGlobalTwelveRepresentative 8)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ↔
      sExtra⁻¹ (twelfthRootX 31) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfth_partner_inverse _ tbN3nPrefix
    (generatedAxisGlobalTwelveTwelfthRootIdentWord 31) generatedTwelfthAxis
    tbN3nPrefix_ok tbN3nPrefix_xi tbN3n_eq).1 tbN3nPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
