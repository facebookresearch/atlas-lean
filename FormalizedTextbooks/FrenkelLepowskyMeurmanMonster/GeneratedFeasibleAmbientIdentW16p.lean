/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentPrefix

/-! # The Tenth-Twelfth identification gtwelfth:W16+ (Twelfth root 16 to Tenth root 28, e = 1)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_forward_GMZ`). The
identification binds one triality image at the Tenth root vector `28` and one at the Twelfth root
vector `16` (gated wrappers of workers gtenth, gtwelfth and gforest). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem fbW16p_pair : pairTriGMZ 32 64 true fbW16pL fbW16pW fbW16pHX fbW16pGX ((tensorWordDenAll
    fbW16pH : ℚ) * 32 / 2 ^ 8) ((tensorWordDenAll fbW16pG : ℚ) * 32 / 2 ^ 9) = 128 := by
  rw [pairTriGMZ_parts fbW16p_hok fbW16p_hm fbW16p_hp fbW16p_hn fbW16p_ha fbW16p_hb fbW16p_hc,
      fbW16pH_den, fbW16pG_den]
  norm_num [fbW16pL, fbW16pW]

/-- The identification gtwelfth:W16+: the triality image of the source image is the target image. -/
theorem fbW16p_ident :
    sExtra (rhoLocal (identWordLocal fbW16pH) (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal fbW16pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GMZ 10 11 _ _ fbW16pL fbW16pW (ofList_ok fbW16pHT fbW16pHT_labels) (ofList_ok
      fbW16pGT fbW16pGT_labels) rfl rfl
    fbW16pH_tensor.1 fbW16pG_tensor.1 (by norm_num) (by norm_num) fbW16pL_actual fbW16pW_actual
        fbW16p_pair

/-- The Xi-free prefix of the target word (record prefix `Q * Sign * pi`). -/
def fbW16pM : List IdentLetter :=
  [.qel (qmElt (14183719, false)), .sign 1199 0, .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (1, false)]

set_option maxRecDepth 100000 in
/-- The prefix consists of admissible letters (no Xi, source signs with `ε = 0`). -/
theorem fbW16pM_letters : fbW16pM.all generatedAxisGlobalTwelveTenthPrefixLetter = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the prefix on the Ω mask. -/
theorem fbW16pM_phase : qmWord (fbW16pM.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- Twelfth side of gtwelfth:W16+: the positive triality image of Twelfth root vector `16` lies in
the union of the local orbits. -/
theorem fbW16p_twelfth : sExtra (twelfthRootX 16) ∈ generatedLocalOrbitUnion
    generatedAxisGlobalTwelveRepresentative := by
  have h1 : generatedAxisGlobalTwelveTwelfthRootIdentWord 16 = fbW16pH := rfl
  apply twelfthRoot_pos_of_src 16 11 (identWordLocal fbW16pG)
  rw [twelfthRootX, h1, ← twelfthRep_eq]
  exact fbW16p_ident

/-- Tenth side of gtwelfth:W16+: one triality image of Tenth root vector `28` (target behind the
    prefix,
sign from its Q-phase) lies in the union of the local orbits. -/
theorem fbW16p_tenth : sExtra (generatedAxisGlobalTwelveTenthRootVector 28) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hl := fbIdentPrefix_letters fbW16pM_letters
  have h2 : fbW16pM ++ generatedAxisGlobalTwelveTenthRootIdent 28 = fbW16pG := rfl
  have he : sExtra (rhoLocal (identWordLocal fbW16pH) (generatedAxisGlobalTwelveRepresentative
      10)) =
      rhoLocal (identWordLocal (fbW16pM ++ generatedAxisGlobalTwelveTenthRootIdent 28))
        (generatedAxisGlobalTwelveRepresentative 11) := by
    rw [h2]
    exact fbW16p_ident
  have hb := (sixthPhase_of_forward_identity 10 (identWordLocal fbW16pH) fbW16pM _ hl.1 hl.2 _ he).2
    fbW16pM_phase
  rw [← generatedAxisGlobalTwelveTenthRootWord_ident] at hb
  exact hb

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
