/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindPartner

/-! # Twelfth root vectors from the identification
Twelfth[13]- <-> Twelfth[13]+ (record gtwelfth:W13+, e = 1)

The factory identification `twGtwelfthW13p_ident` is put in root-vector form: the source word is a
Twelfth root identification word and/or the target word is an Xi-free prefix followed by one; the
Q-phase of the prefix is computed in the kernel.  The memberships follow from the binding lemmas
of `GeneratedAxisGlobalTwelveTwelfthBind` and `GeneratedAxisGlobalTwelveTwelfthBindPartner`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The source word is the identification word of Twelfth root `13`. -/
theorem tbW13pH_eq : twGtwelfthW13pH = generatedAxisGlobalTwelveTwelfthRootIdentWord 13 := rfl

/-- The Xi-free prefix of the target word. -/
def tbW13pPrefix : List IdentLetter :=
  [.qel (qmElt (7541136, true)), .sign 1862 0, .mono (0, true), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false),
  .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
  .mono (0, true), .mono (0, true), .mono (1, false)]

/-- The target word is the prefix followed by the identification word of Twelfth root `13`. -/
theorem tbW13pG_split :
    twGtwelfthW13pG = tbW13pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 13 :=
  rfl

/-- The prefix consists of qualifying letters. -/
theorem tbW13pPrefix_ok : ∀ l ∈ tbW13pPrefix, SixthPhaseLetter l := by
  simp [tbW13pPrefix, SixthPhaseLetter]

/-- The prefix is Xi-free. -/
theorem tbW13pPrefix_xi : ∀ l ∈ tbW13pPrefix, l ≠ IdentLetter.xi := by
  simp [tbW13pPrefix]

set_option maxRecDepth 100000 in
/-- The Q-phase of the prefix (fixes the Ω mask). -/
theorem tbW13pPrefix_phase :
    qmWord (tbW13pPrefix.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- The identification in root-vector form. -/
theorem tbW13p_eq : sExtra (twelfthRootX 13) =
    rhoLocal (identWordLocal (tbW13pPrefix ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 13))
      generatedTwelfthAxis := by
  have h := twGtwelfthW13p_ident
  rw [tbW13pH_eq, tbW13pG_split] at h
  exact h

/-- The source image of Twelfth root `13`. -/
theorem twelfthRoot13_pos_W13p : sExtra (twelfthRootX 13) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport 10 _ tbW13p_eq

/-- The target image of Twelfth root `13` (sign from the phase of the prefix). -/
theorem twelfthRoot13_neg_W13p : sExtra⁻¹ (twelfthRootX 13) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (twelfthRoot_of_target_forward 13 10
    (identWordLocal (generatedAxisGlobalTwelveTwelfthRootIdentWord 13))
    tbW13pPrefix tbW13pPrefix_ok tbW13pPrefix_xi tbW13p_eq).1 tbW13pPrefix_phase

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
