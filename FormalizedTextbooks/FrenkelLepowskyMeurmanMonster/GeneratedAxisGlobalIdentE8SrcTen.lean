/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcData

/-! # Materialized Eighth source: the packed triality tensor and its tight bound

The packed triality tensor of the source (`twTriTen`) is the literal `e8SrcTenLit`, and its fields
are bounded by `10496` (one packed check per column) instead of the coarse `2^29`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The literal tensor is the packed triality tensor. -/
theorem e8SrcTen_eq : twTriTen 64 2048 e8YLit (srcEighthYL 64).sh.odd = e8SrcTenLit := by
  decide +kernel

/-- The coarse bound of the literal tensor. -/
theorem e8SrcTen_coarse : TBnd 64 (4 * (16777216 * 8) + 288 * 6144) e8SrcTenLit := by
  have h := eighthSrcVecW_bnd (w := 64) (by norm_num)
  rw [e8YLit_eq, e8SrcTen_eq] at h
  exact h

set_option maxRecDepth 100000 in
/-- The packed tight-bound check of the literal tensor. -/
theorem e8SrcTen_check :
    (List.range 24).all (fun i => colLeB 64 10496 (tcol e8SrcTenLit i)) = true := by
  decide +kernel

/-- The tight bound of the literal tensor. -/
theorem e8SrcTen_tight : TBnd 64 10496 e8SrcTenLit :=
  tbnd_of_check (by norm_num) e8SrcTen_coarse (by norm_num) (by norm_num) e8SrcTen_check

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
