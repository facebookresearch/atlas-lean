/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentPrefix

/-! # The Tenth-Twelfth identification gtwelfth:W10- (Twelfth root 10 to Tenth root 51, e = -1)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_inverse_GMZ`). The
identification binds one triality image at the Tenth root vector `51` and one at the Twelfth root
vector `10` (gated wrappers of workers gtenth, gtwelfth and gforest). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem fbW10n_pair : pairTriGMZ 32 64 false fbW10nL fbW10nW fbW10nHX fbW10nGX ((tensorWordDenAll
    fbW10nH : ℚ) * 32 / 2 ^ 8) ((tensorWordDenAll fbW10nG : ℚ) * 32 / 2 ^ 9) = 128 := by
  rw [pairTriGMZ_parts fbW10n_hok fbW10n_hm fbW10n_hp fbW10n_hn fbW10n_ha fbW10n_hb fbW10n_hc,
      fbW10nH_den, fbW10nG_den]
  norm_num [fbW10nL, fbW10nW]

/-- The identification gtwelfth:W10-: the triality image of the source image is the target image. -/
theorem fbW10n_ident :
    sExtra.symm (rhoLocal (identWordLocal fbW10nH) (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal fbW10nG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_GMZ 10 11 _ _ fbW10nL fbW10nW (ofList_ok fbW10nHT fbW10nHT_labels) (ofList_ok
      fbW10nGT fbW10nGT_labels) rfl rfl
    fbW10nH_tensor.1 fbW10nG_tensor.1 (by norm_num) (by norm_num) fbW10nL_actual fbW10nW_actual
        fbW10n_pair

/-- The Xi-free prefix of the target word (record prefix `Q * Sign * pi`). -/
def fbW10nM : List IdentLetter :=
  [.qel (qmElt (3076188, false)), .sign 1764 0, .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true)]

set_option maxRecDepth 100000 in
/-- The prefix consists of admissible letters (no Xi, source signs with `ε = 0`). -/
theorem fbW10nM_letters : fbW10nM.all generatedAxisGlobalTwelveTenthPrefixLetter = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the prefix on the Ω mask. -/
theorem fbW10nM_phase : qmWord (fbW10nM.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- Twelfth side of gtwelfth:W10-: the inverse triality image of Twelfth root vector `10` lies in
the union of the local orbits. -/
theorem fbW10n_twelfth : sExtra⁻¹ (twelfthRootX 10) ∈ generatedLocalOrbitUnion
    generatedAxisGlobalTwelveRepresentative := by
  have h1 : generatedAxisGlobalTwelveTwelfthRootIdentWord 10 = fbW10nH := rfl
  apply twelfthRoot_neg_of_src 10 11 (identWordLocal fbW10nG)
  rw [twelfthRootX, h1, ← twelfthRep_eq]
  exact fbW10n_ident

/-- Tenth side of gtwelfth:W10-: one triality image of Tenth root vector `51` (target behind the
    prefix,
sign from its Q-phase) lies in the union of the local orbits. -/
theorem fbW10n_tenth : sExtra (generatedAxisGlobalTwelveTenthRootVector 51) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hl := fbIdentPrefix_letters fbW10nM_letters
  have h2 : fbW10nM ++ generatedAxisGlobalTwelveTenthRootIdent 51 = fbW10nG := rfl
  have he : sExtra.symm (rhoLocal (identWordLocal fbW10nH)
      (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal (fbW10nM ++ generatedAxisGlobalTwelveTenthRootIdent 51))
        (generatedAxisGlobalTwelveRepresentative 11) := by
    rw [h2]
    exact fbW10n_ident
  have hb := (sixthPhase_of_inverse_identity 10 (identWordLocal fbW10nH) fbW10nM _ hl.1 hl.2 _ he).1
    fbW10nM_phase
  rw [← generatedAxisGlobalTwelveTenthRootWord_ident] at hb
  exact hb

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
