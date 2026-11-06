/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW2nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW2nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW2nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentPrefix

/-! # The Tenth-Twelfth identification gtwelfth:W2- (Twelfth root 2 to Tenth root 8, e = -1)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_inverse_GMZ`). The
identification binds one triality image at the Tenth root vector `8` and one at the Twelfth root
vector `2` (gated wrappers of workers gtenth, gtwelfth and gforest). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem fbW2n_pair : pairTriGMZ 32 64 false fbW2nL fbW2nW fbW2nHX fbW2nGX ((tensorWordDenAll
    fbW2nH : ℚ) * 32 / 2 ^ 12) ((tensorWordDenAll fbW2nG : ℚ) * 32 / 2 ^ 9) = 128 := by
  rw [pairTriGMZ_parts fbW2n_hok fbW2n_hm fbW2n_hp fbW2n_hn fbW2n_ha fbW2n_hb fbW2n_hc,
      fbW2nH_den, fbW2nG_den]
  norm_num [fbW2nL, fbW2nW]

/-- The identification gtwelfth:W2-: the triality image of the source image is the target image. -/
theorem fbW2n_ident :
    sExtra.symm (rhoLocal (identWordLocal fbW2nH) (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal fbW2nG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_GMZ 10 11 _ _ fbW2nL fbW2nW (ofList_ok fbW2nHT fbW2nHT_labels) (ofList_ok fbW2nGT
      fbW2nGT_labels) rfl rfl
    fbW2nH_tensor.1 fbW2nG_tensor.1 (by norm_num) (by norm_num) fbW2nL_actual fbW2nW_actual
        fbW2n_pair

/-- The Xi-free prefix of the target word (record prefix `Q * Sign * pi`). -/
def fbW2nM : List IdentLetter :=
  [.qel (qmElt (10747241, false)), .sign 376 0, .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, false)]

set_option maxRecDepth 100000 in
/-- The prefix consists of admissible letters (no Xi, source signs with `ε = 0`). -/
theorem fbW2nM_letters : fbW2nM.all generatedAxisGlobalTwelveTenthPrefixLetter = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the prefix on the Ω mask. -/
theorem fbW2nM_phase : qmWord (fbW2nM.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- Twelfth side of gtwelfth:W2-: the inverse triality image of Twelfth root vector `2` lies in
the union of the local orbits. -/
theorem fbW2n_twelfth : sExtra⁻¹ (twelfthRootX 2) ∈ generatedLocalOrbitUnion
    generatedAxisGlobalTwelveRepresentative := by
  have h1 : generatedAxisGlobalTwelveTwelfthRootIdentWord 2 = fbW2nH := rfl
  apply twelfthRoot_neg_of_src 2 11 (identWordLocal fbW2nG)
  rw [twelfthRootX, h1, ← twelfthRep_eq]
  exact fbW2n_ident

/-- Tenth side of gtwelfth:W2-: one triality image of Tenth root vector `8` (target behind the
    prefix,
sign from its Q-phase) lies in the union of the local orbits. -/
theorem fbW2n_tenth : sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector 8) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hl := fbIdentPrefix_letters fbW2nM_letters
  have h2 : fbW2nM ++ generatedAxisGlobalTwelveTenthRootIdent 8 = fbW2nG := rfl
  have he : sExtra.symm (rhoLocal (identWordLocal fbW2nH) (generatedAxisGlobalTwelveRepresentative
      10)) =
      rhoLocal (identWordLocal (fbW2nM ++ generatedAxisGlobalTwelveTenthRootIdent 8))
        (generatedAxisGlobalTwelveRepresentative 11) := by
    rw [h2]
    exact fbW2n_ident
  have hb := (sixthPhase_of_inverse_identity 10 (identWordLocal fbW2nH) fbW2nM _ hl.1 hl.2 _ he).2
    fbW2nM_phase
  rw [← generatedAxisGlobalTwelveTenthRootWord_ident] at hb
  exact hb

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
