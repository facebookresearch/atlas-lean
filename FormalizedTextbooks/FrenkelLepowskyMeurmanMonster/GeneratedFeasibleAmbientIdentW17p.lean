/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW17pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW17pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW17pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentPrefix

/-! # The Tenth-Twelfth identification gtwelfth:W17+ (Twelfth root 17 to Tenth root 44, e = 1)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_forward_GMZ`). The
identification binds one triality image at the Tenth root vector `44` and one at the Twelfth root
vector `17` (gated wrappers of workers gtenth, gtwelfth and gforest). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem fbW17p_pair : pairTriGMZ 32 64 true fbW17pL fbW17pW fbW17pHX fbW17pGX ((tensorWordDenAll
    fbW17pH : ℚ) * 32 / 2 ^ 8) ((tensorWordDenAll fbW17pG : ℚ) * 32 / 2 ^ 9) = 128 := by
  rw [pairTriGMZ_parts fbW17p_hok fbW17p_hm fbW17p_hp fbW17p_hn fbW17p_ha fbW17p_hb fbW17p_hc,
      fbW17pH_den, fbW17pG_den]
  norm_num [fbW17pL, fbW17pW]

/-- The identification gtwelfth:W17+: the triality image of the source image is the target image. -/
theorem fbW17p_ident :
    sExtra (rhoLocal (identWordLocal fbW17pH) (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal fbW17pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GMZ 10 11 _ _ fbW17pL fbW17pW (ofList_ok fbW17pHT fbW17pHT_labels) (ofList_ok
      fbW17pGT fbW17pGT_labels) rfl rfl
    fbW17pH_tensor.1 fbW17pG_tensor.1 (by norm_num) (by norm_num) fbW17pL_actual fbW17pW_actual
        fbW17p_pair

/-- The Xi-free prefix of the target word (record prefix `Q * Sign * pi`). -/
def fbW17pM : List IdentLetter :=
  [.qel (qmElt (14417179, true)), .sign 1896 0, .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false)]

set_option maxRecDepth 100000 in
/-- The prefix consists of admissible letters (no Xi, source signs with `ε = 0`). -/
theorem fbW17pM_letters : fbW17pM.all generatedAxisGlobalTwelveTenthPrefixLetter = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the prefix on the Ω mask. -/
theorem fbW17pM_phase : qmWord (fbW17pM.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- Twelfth side of gtwelfth:W17+: the positive triality image of Twelfth root vector `17` lies in
the union of the local orbits. -/
theorem fbW17p_twelfth : sExtra (twelfthRootX 17) ∈ generatedLocalOrbitUnion
    generatedAxisGlobalTwelveRepresentative := by
  have h1 : generatedAxisGlobalTwelveTwelfthRootIdentWord 17 = fbW17pH := rfl
  apply twelfthRoot_pos_of_src 17 11 (identWordLocal fbW17pG)
  rw [twelfthRootX, h1, ← twelfthRep_eq]
  exact fbW17p_ident

/-- Tenth side of gtwelfth:W17+: one triality image of Tenth root vector `44` (target behind the
    prefix,
sign from its Q-phase) lies in the union of the local orbits. -/
theorem fbW17p_tenth : sExtra (generatedAxisGlobalTwelveTenthRootVector 44) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hl := fbIdentPrefix_letters fbW17pM_letters
  have h2 : fbW17pM ++ generatedAxisGlobalTwelveTenthRootIdent 44 = fbW17pG := rfl
  have he : sExtra (rhoLocal (identWordLocal fbW17pH) (generatedAxisGlobalTwelveRepresentative
      10)) =
      rhoLocal (identWordLocal (fbW17pM ++ generatedAxisGlobalTwelveTenthRootIdent 44))
        (generatedAxisGlobalTwelveRepresentative 11) := by
    rw [h2]
    exact fbW17p_ident
  have hb := (sixthPhase_of_forward_identity 10 (identWordLocal fbW17pH) fbW17pM _ hl.1 hl.2 _ he).2
    fbW17pM_phase
  rw [← generatedAxisGlobalTwelveTenthRootWord_ident] at hb
  exact hb

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
