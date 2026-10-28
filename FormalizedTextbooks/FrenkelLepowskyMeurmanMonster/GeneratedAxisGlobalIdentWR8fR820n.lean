/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPA
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820nPC

/-! # Factory identification Root8[25]- <-> Root8[25]- (record r8f:R820-, e = -1)

All parts of the exact pairing agree with the self parts of the target representation, whose sum
is the Griess norm `128` of the target axis; hence the triality image of the source image is the
target image (`ident_inverse_selfM`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The identification Root8[25]- <-> Root8[25]-. -/
theorem wR8fR820n_ident : sExtra.symm (rhoLocal (identWordLocal wR8fR820nH)
    (generatedAxisGlobalTwelveRepresentative 9)) =
      rhoLocal (identWordLocal wR8fR820nG) (generatedAxisGlobalTwelveRepresentative 9) := by
  have hX := (tensorWordAll_actual wR8fR820nH (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wR8fR820nH_growth]; norm_num) 32).1
  have hY := (tensorWordAll_actual wR8fR820nG (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [wR8fR820nG_growth]; norm_num) 32).1
  rw [wR8fR820nH_growth] at hX
  rw [wR8fR820nG_growth] at hY
  exact ident_inverse_selfM 9 9 _ _ wR8fR820nL wR8fR820nW (ofList_ok wR8fR820nHT
      wR8fR820nT_labels.1)
    (ofList_ok wR8fR820nGT wR8fR820nT_labels.2) rfl rfl (hX) (hY) (by norm_num) (by norm_num)
    (by norm_num) wR8fR820nL_actual wR8fR820nW_actual wR8fR820n_hok wR8fR820n_hm wR8fR820n_hp
        wR8fR820n_hn wR8fR820n_ha wR8fR820n_ht

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
