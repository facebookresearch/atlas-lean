/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentCheapY

/-! # The Twelfth axis as an identification vector with a cheap tensor

`twelfthSrcVecC w : IdentVec` represents the Twelfth axis (family representative `10`) with the
tensor block given by the widened compact literal `twelfthX12Lit` (numerators over `32`, field
bound `15` at every width `w ≥ 4`) and short scale `1 / 128`, so that identifications can
evaluate it cheaply in the kernel. It is the triality image `twTriVec` of the cheap incoming
vector `twelfthYC` (the literal matrix block, the octad label list and the matrix check are those
of `GeneratedAxisGlobalTwelveTwelfthIdentSource`; the pair terms are rechecked at the new scale),
with the computed tensor replaced by the literal after one packed comparison
(`twelfthX12_check`). `twelfthSrcC_rep` binds it to the genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The matrix check reads only the matrix block, the short block and the short scale. -/
theorem twMatCheck_congr (M' : MatRep) (L L' : IdentVec) (hm : L.mat = L'.mat) (hs : L.sh = L'.sh)
    (hd : L.sden = L'.sden) : twMatCheck M' L = twMatCheck M' L' := by
  unfold twMatCheck twTriMatEntry
  rw [hm, hs, hd]

/-- The octad label check reads only the short block. -/
theorem twOctCheck_congr (os : List ℕ) (L L' : IdentVec) (hs : L.sh = L'.sh) :
    twOctCheck os L = twOctCheck os L' := by
  unfold twOctCheck
  rw [hs]

/-- The triality image of the cheap incoming vector (short scale `1 / 128`). -/
def twelfthSrcVecC0 : IdentVec :=
  twTriVec 24 twelfthYC twelfthYXC 64 twelfthSrcMat twelfthSrcPairs128 twelfthSrcOcts 1 8

/-- The literal matrix block agrees with the triality formula. -/
theorem twelfthSrcC_mat : twMatCheck twelfthSrcMat twelfthYC = true := by
  rw [twMatCheck_congr _ twelfthYC twelfthYLit rfl rfl rfl]
  exact twelfthSrc_mat

/-- The octad list covers the incoming octad blocks. -/
theorem twelfthSrcC_octs : twOctCheck twelfthSrcOcts twelfthYC = true := by
  rw [twOctCheck_congr _ twelfthYC twelfthYLit rfl]
  exact twelfthSrc_octs

set_option maxRecDepth 100000 in
/-- The literal pair terms agree with the triality formulas at short scale `1 / 128`. -/
theorem twelfthSrcC_pairs : twPairCheck twelfthSrcPairs128 twelfthYC 64 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd incoming numerators are bounded. -/
theorem twelfthSrcC_oddBound :
    twelfthYC.sh.odd.all (fun q => decide ((8 * q.2).natAbs ≤ 32)) = true ∧
      4 * 56 + twelfthYC.sh.odd.length * 32 + 60 < 2 ^ 24 := by
  decide +kernel

/-- The short scale of the incoming vector. -/
theorem twelfthYC_sden : twelfthYC.sden = 1 / 16 := rfl

/-- The triality image of the cheap incoming vector represents the Twelfth axis. -/
theorem twelfthSrcC0_actual : griessConwayEncode generatedTwelfthAxis = twelfthSrcVecC0.real := by
  rw [generatedTwelfthAxis_local_expression]
  exact twTriVec_actual 24 56 32 twelfthYC twelfthYXC 64 twelfthSrcMat twelfthSrcPairs128
    twelfthSrcOcts 1 8 twelfthYC_ok rfl (by norm_num) twelfthYXC_bnd twelfthSrcC_oddBound.1
    (by have := twelfthSrcC_oddBound.2; omega)
    (by rw [twelfthYC_sden]; norm_num) (by rw [twelfthYC_sden]; norm_num)
    twelfthSrcC_mat twelfthSrcC_pairs twelfthSrcC_octs _ twelfthYC_actual

/-- The computed packed tensor of the triality image (numerators over `128`). -/
def twelfthX12C : List SVec := twTriTen 24 8 twelfthYXC twelfthYC.sh.odd

/-- Bounds of the computed packed tensor. -/
theorem twelfthX12C_bnd : TBnd 24 (4 * 56 + twelfthYC.sh.odd.length * 32) twelfthX12C :=
  twTriTen_bnd 24 56 32 8 twelfthYXC twelfthYC.sh.odd twelfthYXC_bnd
    (fun q hq => by
      have h := twelfthSrcC_oddBound.1
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h q hq)
    (by have := twelfthSrcC_oddBound.2; omega)

set_option maxRecDepth 100000 in
/-- The computed tensor is four times the compact literal. -/
theorem twelfthX12_check : twColCheck 24 4 4 twelfthX12C twelfthX12Lit = true := by
  decide +kernel

/-- The Twelfth axis with the compact literal tensor block. -/
def twelfthSrcVecC (w : ℕ) : IdentVec :=
  ⟨twelfthSrcMat, twelfthSrcVecC0.sh, twelfthSrcVecC0.sden,
    tensorRat w (twWidenT 4 w twelfthX12Lit) 32⟩

/-- The compact tensor block is the computed tensor block. -/
theorem twelfthSrcVecC_ten_eq (w : ℕ) (hw : 4 ≤ w) :
    (twelfthSrcVecC w).ten = twelfthSrcVecC0.ten := by
  change tensorRat w (twWidenT 4 w twelfthX12Lit) 32 = tensorRat 24 twelfthX12C (2 * 64)
  rw [twWidenT_rat 4 w hw]
  exact (twColCheck_rat 24 4 4 _ twelfthX12C twelfthX12Lit (by norm_num) twelfthX12C_bnd
    (by have := twelfthSrcC_oddBound.2; omega) twelfthX12_check (2 * 64) 32 (by norm_num)
    (by norm_num)).symm

/-- The compact representation has the coordinates of the computed one. -/
theorem twelfthSrcVecC_real (w : ℕ) (hw : 4 ≤ w) :
    (twelfthSrcVecC w).real = twelfthSrcVecC0.real := by
  have ht := twelfthSrcVecC_ten_eq w hw
  unfold IdentVec.real IdentVec.packet
  rw [ht]
  rfl

/-- The representation of family representative `10` with the compact tensor. -/
theorem twelfthSrcC_rep (w : ℕ) (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 10) = (twelfthSrcVecC w).real := by
  rw [twelfthSrcVecC_real w hw]
  exact twelfthSrcC0_actual

/-- The short block of the compact representation satisfies the range conditions. -/
theorem twelfthSrcVecC_ok (w : ℕ) : (twelfthSrcVecC w).sh.ok = true := by
  change twelfthSrcVecC0.sh.ok = true
  exact twTriVec_ok 24 twelfthYC twelfthYXC 64 twelfthSrcMat twelfthSrcPairs128 twelfthSrcOcts 1 8
    twelfthSrcC_pairs twelfthSrcC_octs

/-- The tensor block of the compact representation. -/
theorem twelfthSrcVecC_ten (w : ℕ) :
    (twelfthSrcVecC w).ten = tensorRat w (twWidenT 4 w twelfthX12Lit) 32 := rfl

/-- The short scale of the compact representation. -/
theorem twelfthSrcVecC_sden (w : ℕ) : (twelfthSrcVecC w).sden = 1 / 128 := by
  change 1 / (2 * (64 : ℚ)) = 1 / 128
  norm_num

/-- Bounds of the compact packed tensor. -/
theorem twelfthSrcXC_bnd (w : ℕ) (hw : 4 ≤ w) : TBnd w 15 (twWidenT 4 w twelfthX12Lit) :=
  twWidenT_bnd 4 w hw twelfthX12Lit

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
