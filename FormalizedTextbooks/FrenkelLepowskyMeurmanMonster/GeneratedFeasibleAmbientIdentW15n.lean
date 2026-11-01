/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentPrefix

/-! # The Tenth-Twelfth identification gtwelfth:W15- (Twelfth root 15 to Tenth root 38, e = -1)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_inverse_GMZ`). The
identification binds one triality image at the Tenth root vector `38` and one at the Twelfth root
vector `15` (gated wrappers of workers gtenth, gtwelfth and gforest). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem fbW15n_pair : pairTriGMZ 32 64 false fbW15nL fbW15nW fbW15nHX fbW15nGX ((tensorWordDenAll
    fbW15nH : ℚ) * 32 / 2 ^ 8) ((tensorWordDenAll fbW15nG : ℚ) * 32 / 2 ^ 13) = 128 := by
  rw [pairTriGMZ_parts fbW15n_hok fbW15n_hm fbW15n_hp fbW15n_hn fbW15n_ha fbW15n_hb fbW15n_hc,
      fbW15nH_den, fbW15nG_den]
  norm_num [fbW15nL, fbW15nW]

/-- The identification gtwelfth:W15-: the triality image of the source image is the target image. -/
theorem fbW15n_ident :
    sExtra.symm (rhoLocal (identWordLocal fbW15nH) (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal fbW15nG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_GMZ 10 11 _ _ fbW15nL fbW15nW (ofList_ok fbW15nHT fbW15nHT_labels) (ofList_ok
      fbW15nGT fbW15nGT_labels) rfl rfl
    fbW15nH_tensor.1 fbW15nG_tensor.1 (by norm_num) (by norm_num) fbW15nL_actual fbW15nW_actual
        fbW15n_pair

/-- The Xi-free prefix of the target word (record prefix `Q * Sign * pi`). -/
def fbW15nM : List IdentLetter :=
  [.qel (qmElt (15034916, false)), .sign 769 0, .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, true)]

set_option maxRecDepth 100000 in
/-- The prefix consists of admissible letters (no Xi, source signs with `ε = 0`). -/
theorem fbW15nM_letters : fbW15nM.all generatedAxisGlobalTwelveTenthPrefixLetter = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the prefix on the Ω mask. -/
theorem fbW15nM_phase : qmWord (fbW15nM.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- Twelfth side of gtwelfth:W15-: the inverse triality image of Twelfth root vector `15` lies in
the union of the local orbits. -/
theorem fbW15n_twelfth : sExtra⁻¹ (twelfthRootX 15) ∈ generatedLocalOrbitUnion
    generatedAxisGlobalTwelveRepresentative := by
  have h1 : generatedAxisGlobalTwelveTwelfthRootIdentWord 15 = fbW15nH := rfl
  apply twelfthRoot_neg_of_src 15 11 (identWordLocal fbW15nG)
  rw [twelfthRootX, h1, ← twelfthRep_eq]
  exact fbW15n_ident

/-- Tenth side of gtwelfth:W15-: one triality image of Tenth root vector `38` (target behind the
    prefix,
sign from its Q-phase) lies in the union of the local orbits. -/
theorem fbW15n_tenth : sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector 38) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hl := fbIdentPrefix_letters fbW15nM_letters
  have h2 : fbW15nM ++ generatedAxisGlobalTwelveTenthRootIdent 38 = fbW15nG := rfl
  have he : sExtra.symm (rhoLocal (identWordLocal fbW15nH)
      (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal (fbW15nM ++ generatedAxisGlobalTwelveTenthRootIdent 38))
        (generatedAxisGlobalTwelveRepresentative 11) := by
    rw [h2]
    exact fbW15n_ident
  have hb := (sixthPhase_of_inverse_identity 10 (identWordLocal fbW15nH) fbW15nM _ hl.1 hl.2 _ he).2
    fbW15nM_phase
  rw [← generatedAxisGlobalTwelveTenthRootWord_ident] at hb
  exact hb

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
