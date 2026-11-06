/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentPrefix

/-! # The Tenth-Twelfth identification gtwelfth:W15+ (Twelfth root 15 to Tenth root 38, e = 1)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_forward_GMZ`). The
identification binds one triality image at the Tenth root vector `38` and one at the Twelfth root
vector `15` (gated wrappers of workers gtenth, gtwelfth and gforest). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem fbW15p_pair : pairTriGMZ 32 64 true fbW15pL fbW15pW fbW15pHX fbW15pGX ((tensorWordDenAll
    fbW15pH : ℚ) * 32 / 2 ^ 8) ((tensorWordDenAll fbW15pG : ℚ) * 32 / 2 ^ 13) = 128 := by
  rw [pairTriGMZ_parts fbW15p_hok fbW15p_hm fbW15p_hp fbW15p_hn fbW15p_ha fbW15p_hb fbW15p_hc,
      fbW15pH_den, fbW15pG_den]
  norm_num [fbW15pL, fbW15pW]

/-- The identification gtwelfth:W15+: the triality image of the source image is the target image. -/
theorem fbW15p_ident :
    sExtra (rhoLocal (identWordLocal fbW15pH) (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal fbW15pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GMZ 10 11 _ _ fbW15pL fbW15pW (ofList_ok fbW15pHT fbW15pHT_labels) (ofList_ok
      fbW15pGT fbW15pGT_labels) rfl rfl
    fbW15pH_tensor.1 fbW15pG_tensor.1 (by norm_num) (by norm_num) fbW15pL_actual fbW15pW_actual
        fbW15p_pair

/-- The Xi-free prefix of the target word (record prefix `Q * Sign * pi`). -/
def fbW15pM : List IdentLetter :=
  [.qel (qmElt (4205436, true)), .sign 432 0, .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, false)]

set_option maxRecDepth 100000 in
/-- The prefix consists of admissible letters (no Xi, source signs with `ε = 0`). -/
theorem fbW15pM_letters : fbW15pM.all generatedAxisGlobalTwelveTenthPrefixLetter = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the prefix on the Ω mask. -/
theorem fbW15pM_phase : qmWord (fbW15pM.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- Twelfth side of gtwelfth:W15+: the positive triality image of Twelfth root vector `15` lies in
the union of the local orbits. -/
theorem fbW15p_twelfth : sExtra (twelfthRootX 15) ∈ generatedLocalOrbitUnion
    generatedAxisGlobalTwelveRepresentative := by
  have h1 : generatedAxisGlobalTwelveTwelfthRootIdentWord 15 = fbW15pH := rfl
  apply twelfthRoot_pos_of_src 15 11 (identWordLocal fbW15pG)
  rw [twelfthRootX, h1, ← twelfthRep_eq]
  exact fbW15p_ident

/-- Tenth side of gtwelfth:W15+: one triality image of Tenth root vector `38` (target behind the
    prefix,
sign from its Q-phase) lies in the union of the local orbits. -/
theorem fbW15p_tenth : sExtra⁻¹ (generatedAxisGlobalTwelveTenthRootVector 38) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hl := fbIdentPrefix_letters fbW15pM_letters
  have h2 : fbW15pM ++ generatedAxisGlobalTwelveTenthRootIdent 38 = fbW15pG := rfl
  have he : sExtra (rhoLocal (identWordLocal fbW15pH) (generatedAxisGlobalTwelveRepresentative
      10)) =
      rhoLocal (identWordLocal (fbW15pM ++ generatedAxisGlobalTwelveTenthRootIdent 38))
        (generatedAxisGlobalTwelveRepresentative 11) := by
    rw [h2]
    exact fbW15p_ident
  have hb := (sixthPhase_of_forward_identity 10 (identWordLocal fbW15pH) fbW15pM _ hl.1 hl.2 _ he).1
    fbW15pM_phase
  rw [← generatedAxisGlobalTwelveTenthRootWord_ident] at hb
  exact hb

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
