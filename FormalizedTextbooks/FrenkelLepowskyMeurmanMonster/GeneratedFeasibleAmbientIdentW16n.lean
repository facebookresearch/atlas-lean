/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16nPC
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentPrefix

/-! # The Tenth-Twelfth identification gtwelfth:W16- (Twelfth root 16 to Tenth root 28, e = -1)

All parts of the exact pairing (`pairTriGMZ_parts`, values checked in the kernel) sum to the Griess
norm `128`, so the triality image of the source image is the target image (`ident_inverse_GMZ`). The
identification binds one triality image at the Tenth root vector `28` and one at the Twelfth root
vector `16` (gated wrappers of workers gtenth, gtwelfth and gforest). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

/-- The exact pairing of the triality image of the source image with the target image. -/
theorem fbW16n_pair : pairTriGMZ 32 64 false fbW16nL fbW16nW fbW16nHX fbW16nGX ((tensorWordDenAll
    fbW16nH : ℚ) * 32 / 2 ^ 8) ((tensorWordDenAll fbW16nG : ℚ) * 32 / 2 ^ 9) = 128 := by
  rw [pairTriGMZ_parts fbW16n_hok fbW16n_hm fbW16n_hp fbW16n_hn fbW16n_ha fbW16n_hb fbW16n_hc,
      fbW16nH_den, fbW16nG_den]
  norm_num [fbW16nL, fbW16nW]

/-- The identification gtwelfth:W16-: the triality image of the source image is the target image. -/
theorem fbW16n_ident :
    sExtra.symm (rhoLocal (identWordLocal fbW16nH) (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal fbW16nG) (generatedAxisGlobalTwelveRepresentative 11) :=
  ident_inverse_GMZ 10 11 _ _ fbW16nL fbW16nW (ofList_ok fbW16nHT fbW16nHT_labels) (ofList_ok
      fbW16nGT fbW16nGT_labels) rfl rfl
    fbW16nH_tensor.1 fbW16nG_tensor.1 (by norm_num) (by norm_num) fbW16nL_actual fbW16nW_actual
        fbW16n_pair

/-- The Xi-free prefix of the target word (record prefix `Q * Sign * pi`). -/
def fbW16nM : List IdentLetter :=
  [.qel (qmElt (7159077, true)), .sign 622 0, .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true),
    .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true)]

set_option maxRecDepth 100000 in
/-- The prefix consists of admissible letters (no Xi, source signs with `ε = 0`). -/
theorem fbW16nM_letters : fbW16nM.all generatedAxisGlobalTwelveTenthPrefixLetter = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the prefix on the Ω mask. -/
theorem fbW16nM_phase : qmWord (fbW16nM.map sixthPhaseData) (2048, false) = (2048, false) := by
  decide +kernel

/-- Twelfth side of gtwelfth:W16-: the inverse triality image of Twelfth root vector `16` lies in
the union of the local orbits. -/
theorem fbW16n_twelfth : sExtra⁻¹ (twelfthRootX 16) ∈ generatedLocalOrbitUnion
    generatedAxisGlobalTwelveRepresentative := by
  have h1 : generatedAxisGlobalTwelveTwelfthRootIdentWord 16 = fbW16nH := rfl
  apply twelfthRoot_neg_of_src 16 11 (identWordLocal fbW16nG)
  rw [twelfthRootX, h1, ← twelfthRep_eq]
  exact fbW16n_ident

/-- Tenth side of gtwelfth:W16-: one triality image of Tenth root vector `28` (target behind the
    prefix,
sign from its Q-phase) lies in the union of the local orbits. -/
theorem fbW16n_tenth : sExtra (generatedAxisGlobalTwelveTenthRootVector 28) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hl := fbIdentPrefix_letters fbW16nM_letters
  have h2 : fbW16nM ++ generatedAxisGlobalTwelveTenthRootIdent 28 = fbW16nG := rfl
  have he : sExtra.symm (rhoLocal (identWordLocal fbW16nH)
      (generatedAxisGlobalTwelveRepresentative 10)) =
      rhoLocal (identWordLocal (fbW16nM ++ generatedAxisGlobalTwelveTenthRootIdent 28))
        (generatedAxisGlobalTwelveRepresentative 11) := by
    rw [h2]
    exact fbW16n_ident
  have hb := (sixthPhase_of_inverse_identity 10 (identWordLocal fbW16nH) fbW16nM _ hl.1 hl.2 _ he).1
    fbW16nM_phase
  rw [← generatedAxisGlobalTwelveTenthRootWord_ident] at hb
  exact hb

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
