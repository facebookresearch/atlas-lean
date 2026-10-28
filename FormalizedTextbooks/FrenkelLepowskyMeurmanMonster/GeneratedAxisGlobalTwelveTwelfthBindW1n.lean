/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW1n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Twelfth[1]- <-> Twelfth[1]+ (record gtwelfth:W1-, e = -1)

The factory identification `twGtwelfthW1n_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The source word is the identification word of Twelfth root `1`. -/
theorem tbW1nH_eq : twGtwelfthW1nH = generatedAxisGlobalTwelveTwelfthRootIdentWord 1 := rfl

/-- The Xi-free prefix of the target word. -/
def tbW1nPrefix : List IdentLetter :=
  [.qel (qmElt (4661015, true)), .sign 1889 0, .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
  .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
  .mono (0, true)]

/-- The target word is the prefix followed by the identification word of Twelfth root `1`. -/
theorem tbW1nG_split :
    twGtwelfthW1nG = tbW1nPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 1 :=
  rfl

/-- The prefix consists of qualifying letters. -/
theorem tbW1nPrefix_ok : ∀ l ∈ tbW1nPrefix, SixthPhaseLetter l := by
  simp [tbW1nPrefix, SixthPhaseLetter]

/-- The prefix is Xi-free. -/
theorem tbW1nPrefix_xi : ∀ l ∈ tbW1nPrefix, l ≠ IdentLetter.xi := by
  simp [tbW1nPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (fixes the Ω mask). -/
theorem tbW1nPrefix_phase :
    qmWord (tbW1nPrefix.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbW1n_eq : sExtra⁻¹ (twelfthRootX 1) =
    rhoLocal (identWordLocal (tbW1nPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 1))
      generatedTwelfthAxis := by
  have h := twGtwelfthW1n_ident
  rw [tbW1nH_eq, tbW1nG_split] at h
  exact h

/-- The source image of Twelfth root `1`. -/
theorem twelfthRoot1_neg_W1n : sExtra⁻¹ (twelfthRootX 1) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbW1n_eq

/-- The target image of Twelfth root `1` (sign from the phase of the prefix). -/
theorem twelfthRoot1_pos_W1n : sExtra (twelfthRootX 1) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_inverse 1 10
    (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord 1))
    tbW1nPrefix tbW1nPrefix_ok tbW1nPrefix_xi tbW1n_eq).1 tbW1nPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
