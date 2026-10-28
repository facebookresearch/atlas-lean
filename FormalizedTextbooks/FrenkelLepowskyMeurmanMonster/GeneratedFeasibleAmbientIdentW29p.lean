/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentPrefix

/-! # The Tenth-Twelfth identification gtwelfth:W29+ (Twelfth root 29 to Tenth root 48, e = 1)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_forward_GMZ`). The
identification binds one triality image at the Tenth root vector `48` and one at the Twelfth root
vector `29` (gated wrappers of workers gtenth, gtwelfth and gforest). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem fbW29p_pair : pairTriGMZ 32 64 true fbW29pL fbW29pW fbW29pHX fbW29pGX ((tensorWordDenAll
    fbW29pH : ℚ) * 32 / 2 ^ 9) ((tensorWordDenAll fbW29pG : ℚ) * 32 / 2 ^ 9) = 128 := by
  rw [pairTriGMZ_parts fbW29p_hok fbW29p_hm fbW29p_hp fbW29p_hn fbW29p_ha fbW29p_hb fbW29p_hc,
      fbW29pH_den, fbW29pG_den]
  norm_num [fbW29pL, fbW29pW]

/-- The identification gtwelfth:W29+: the triality image of the source image is the target image. -/
theorem fbW29p_ident :
    sExtra (rhoLocal (identWordLocal fbW29pH) (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal fbW29pG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_forward_GMZ 10 11 _ _ fbW29pL fbW29pW (ofList_ok fbW29pHT fbW29pHT_labels) (ofList_ok
      fbW29pGT fbW29pGT_labels) rfl rfl
    fbW29pH_tensor.1 fbW29pG_tensor.1 (by norm_num) (by norm_num) fbW29pL_actual fbW29pW_actual
        fbW29p_pair

/-- The Xi-free prefix of the target word (record prefix `Q * Sign * pi`). -/
def fbW29pM : List IdentLetter :=
  [.qel (qmElt (13796080, true)), .sign 92 0, .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, false)]

set_option maxRecDepth 100000 in
/-- The prefix consists of admissible letters (no Xi, source signs with `ε = 0`). -/
theorem fbW29pM_letters : fbW29pM.all generatedAxisGlobalTwelveTenthPrefixLetter = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the prefix on the Ω mask. -/
theorem fbW29pM_phase : qmWord (fbW29pM.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- Twelfth side of gtwelfth:W29+: the positive triality image of Twelfth root vector `29` lies in
the union of the local orbits. -/
theorem fbW29p_twelfth : sExtra (twelfthRootX 29) ∈ generatedLocalOrbitUnion
    generatedAxisGlobalTwelveRepresentative := by
  have h1 : generatedAxisGlobalTwelveTwelfthRootIdentWord 29 = fbW29pH := rfl
  apply twelfthRoot_pos_of_src 29 11 (identWordLocal fbW29pG)
  rw [twelfthRootX, h1, ← twelfthRep_eq]
  exact fbW29p_ident

/-- Tenth side of gtwelfth:W29+: one triality image of Tenth root vector `48` (target behind the
    prefix,
sign from its Q-phase) lies in the union of the local orbits. -/
theorem fbW29p_tenth : sExtra (generatedAxisGlobalTwelveTenthRootVector 48) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hl := fbIdentPrefix_letters fbW29pM_letters
  have h2 : fbW29pM ++ generatedAxisGlobalTwelveTenthRootIdent 48 = fbW29pG := rfl
  have he : sExtra (rhoLocal (identWordLocal fbW29pH) (generatedAxisGlobalTwelveRepresentative
      10)) =
      rhoLocal (identWordLocal (fbW29pM ++ generatedAxisGlobalTwelveTenthRootIdent 48))
        (generatedAxisGlobalTwelveRepresentative 11) := by
    rw [h2]
    exact fbW29p_ident
  have hb := (sixthPhase_of_forward_identity 10 (identWordLocal fbW29pH) fbW29pM _ hl.1 hl.2 _ he).2
    fbW29pM_phase
  rw [← generatedAxisGlobalTwelveTenthRootWord_ident] at hb
  exact hb

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
