/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcOdd

/-! # The Odd axis with packed tensor columns of any field width

`oddSrcVecW w` is `oddSrcVec` with the packed tensor column at field width `w` (any `w ≥ 4`),
mirroring `fifthSrcVecW`: smaller widths reduce kernel time and memory of packed word actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false

/-- The packed Odd tensor at field width `w`. -/
@[irreducible] def oddSrcXW (w : ℕ) : List SVec :=
  (List.range 24).map (fun j => if j = 0 then unitVec w 0 (-8) else szero)

/-- The columns of the packed Odd tensor at width `w`. -/
theorem oddSrcXW_col (w j : ℕ) (hj : j < 24) :
    tcol (oddSrcXW w) j = if j = 0 then unitVec w 0 (-8) else szero := by
  rw [oddSrcXW, tcol_range_map _ 24 j hj]

/-- Bounds of the packed Odd tensor at width `w`. -/
theorem oddSrcXW_bnd {w : ℕ} (hw : 4 ≤ w) : TBnd w 8 (oddSrcXW w) := by
  have h8 : (-8 : ℤ).natAbs < 2 ^ w := by
    calc (-8 : ℤ).natAbs < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  intro j hj
  rw [oddSrcXW_col w j hj]
  split_ifs
  · exact (unitVec_spec w 0 (-8) (by norm_num) h8).1
  · exact SBnd_zero _ _ _

/-- Values of the packed Odd tensor at width `w`. -/
theorem oddSrcXW_val {w : ℕ} (hw : 4 ≤ w) (k : Fin 4096) (j : Fin 24) :
    sval w (tcol (oddSrcXW w) j.val) k.val =
      if j.val = 0 then (if k.val = 0 then -8 else if k.val = 2048 then 8 else 0) else 0 := by
  have h8 : (-8 : ℤ).natAbs < 2 ^ w := by
    calc (-8 : ℤ).natAbs < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  rw [oddSrcXW_col w j.val j.isLt]
  have hs := (unitVec_spec w 0 (-8) (by norm_num) h8).2 k.val
  by_cases h0 : j.val = 0
  · simp only [h0, ↓reduceIte, hs, zero_add, neg_neg]
  · simp only [h0, ↓reduceIte, sval_zero]

/-- The Odd axis as an identification vector with tensor columns of width `w`. -/
def oddSrcVecW (w : ℕ) : IdentVec := ⟨oddSrcMat, oddSrcShort, 1 / 4, tensorRat w (oddSrcXW w) 1⟩

/-- The tensor block at width `w`. -/
theorem oddSrcVecW_ten (w : ℕ) : (oddSrcVecW w).ten = tensorRat w (oddSrcXW w) 1 := rfl

/-- The short block at width `w`. -/
theorem oddSrcVecW_sh (w : ℕ) : (oddSrcVecW w).sh = oddSrcShort := rfl

/-- The matrix block at width `w` is that of `oddSrcVec`. -/
theorem oddSrcVecW_mat (w : ℕ) : (oddSrcVecW w).mat = oddSrcVec.mat := rfl

/-- The short block at width `w` is that of `oddSrcVec`. -/
theorem oddSrcVecW_sh' (w : ℕ) : (oddSrcVecW w).sh = oddSrcVec.sh := rfl

/-- The short scale at width `w` is that of `oddSrcVec`. -/
theorem oddSrcVecW_sden (w : ℕ) : (oddSrcVecW w).sden = oddSrcVec.sden := rfl

/-- The width-`w` representation has the same packet as `oddSrcVec`. -/
theorem oddSrcVecW_packet {w : ℕ} (hw : 4 ≤ w) : (oddSrcVecW w).packet = oddSrcVec.packet := by
  unfold IdentVec.packet
  rw [oddSrcVecW_mat, oddSrcVecW_sh', oddSrcVecW_sden]
  congr 1
  congr 1
  funext t i
  change tensorRat w (oddSrcXW w) 1 (generatedAxisGlobalSpinLabel t) i =
    tensorRat 128 oddSrcX 1 (generatedAxisGlobalSpinLabel t) i
  change (sval w (tcol (oddSrcXW w) i.val) (generatedAxisGlobalSpinLabel t).val : ℚ) / 1 =
    (sval 128 (tcol oddSrcX i.val) (generatedAxisGlobalSpinLabel t).val : ℚ) / 1
  rw [oddSrcXW_val hw, oddSrcX_val]

/-- The width-`w` representation of family representative `2`. -/
theorem oddSrcW_rep {w : ℕ} (hw : 4 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 2) = (oddSrcVecW w).real := by
  rw [oddSrc_rep, IdentVec.real, IdentVec.real, oddSrcVecW_packet hw]

/-- The short block of the width-`w` representation satisfies the range conditions. -/
theorem oddSrcVecW_ok (w : ℕ) : (oddSrcVecW w).sh.ok = true := oddSrcVec_ok

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
