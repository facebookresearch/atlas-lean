/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentPrefix

/-! # The Tenth-Twelfth identification gtenth:T14+ (Tenth root 14 to Twelfth root 7, e = 1)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_forward_GMZ`). The
identification binds one triality image at the Tenth root vector `14` and one at the Twelfth root
vector `7` (gated wrappers of workers gtenth, gtwelfth and gforest). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem fbT14p_pair : pairTriGMZ 32 64 true fbT14pL fbT14pW fbT14pHX fbT14pGX ((tensorWordDenAll
    fbT14pH : ℚ) * 32 / 2 ^ 16) ((tensorWordDenAll fbT14pG : ℚ) * 32 / 2 ^ 9) = 128 := by
  rw [pairTriGMZ_parts fbT14p_hok fbT14p_hm fbT14p_hp fbT14p_hn fbT14p_ha fbT14p_hb fbT14p_hc,
      fbT14pH_den, fbT14pG_den]
  norm_num [fbT14pL, fbT14pW]

/-- The identification gtenth:T14+: the triality image of the source image is the target image. -/
theorem fbT14p_ident :
    sExtra (rhoLocal (identWordLocal fbT14pH) (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal (identWordLocal fbT14pG) (generatedAxisGlobalTwelveRepresentative 10) :=
  ident_forward_GMZ 11 10 _ _ fbT14pL fbT14pW (ofList_ok fbT14pHT fbT14pHT_labels) (ofList_ok
      fbT14pGT fbT14pGT_labels) rfl rfl
    fbT14pH_tensor.1 fbT14pG_tensor.1 (by norm_num) (by norm_num) fbT14pL_actual fbT14pW_actual
        fbT14p_pair

/-- The Xi-free prefix of the target word (record prefix `Q * Sign * pi`). -/
def fbT14pM : List IdentLetter :=
  [.qel (qmElt (9090190, true)), .sign 771 0, .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, true),
    .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, true),
    .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, true), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true),
    .mono (0, true)]

set_option maxRecDepth 100000 in
/-- The prefix consists of admissible letters (no Xi, source signs with `ε = 0`). -/
theorem fbT14pM_letters : fbT14pM.all generatedAxisGlobalTwelveTenthPrefixLetter = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the prefix on the Ω mask. -/
theorem fbT14pM_phase : qmWord (fbT14pM.map sixthPhaseData) (2048, false) = (2048, true) := by
  decide +kernel

/-- Tenth side of gtenth:T14+: the positive triality image of Tenth root vector `14` lies in the
union of the local orbits. -/
theorem fbT14p_tenth : sExtra (generatedAxisGlobalTwelveTenthRootVector 14) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have h1 : generatedAxisGlobalTwelveTenthRootIdent 14 = fbT14pH := rfl
  rw [generatedAxisGlobalTwelveTenthRootVector, generatedAxisGlobalTwelveTenthRootWord_ident, h1]
  exact generatedAxisGlobalTwelve_mem_of_transport 10 _ fbT14p_ident

/-- Twelfth side of gtenth:T14+: one triality image of Twelfth root vector `7` (target behind the
prefix, sign from its Q-phase) lies in the union of the local orbits. -/
theorem fbT14p_twelfth : sExtra (twelfthRootX 7) ∈ generatedLocalOrbitUnion
    generatedAxisGlobalTwelveRepresentative := by
  have hl := fbIdentPrefix_letters fbT14pM_letters
  have h2 : fbT14pM ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 7 = fbT14pG := rfl
  have he : sExtra (rhoLocal (identWordLocal fbT14pH) (generatedAxisGlobalTwelveRepresentative
      11)) =
      rhoLocal (identWordLocal (fbT14pM ++ generatedAxisGlobalTwelveTwelfthRootIdentWord 7))
        generatedTwelfthAxis := by
    rw [h2]
    exact fbT14p_ident
  exact (twelfthRoot_of_target_forward 7 11 (identWordLocal fbT14pH) fbT14pM hl.1 hl.2 he).2
      fbT14pM_phase

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
