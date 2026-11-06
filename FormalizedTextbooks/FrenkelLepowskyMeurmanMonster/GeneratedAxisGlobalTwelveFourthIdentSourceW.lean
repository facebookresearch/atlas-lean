/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentSource

/-! # The Fourth axis with packed tensor columns of any field width

`fourthSrcVecW w` is `fourthSrcVec` with the packed tensor columns at field width `w` (any
`w ≥ 7`), following `fifthSrcVecW`.  Smaller widths reduce kernel time and memory of the packed
tensor evaluation; the width only has to accommodate the numerator bounds of the words used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The contribution of record `r` to column `i`, at field width `w`. -/
def fourthTermW (w i : ℕ) (r : Fin 56) : SVec :=
  if (generatedFourthOddRootOutputData r).2.val = i then
    unitVec w (generatedFourthOddRootOutputData r).1.val (fourthRootVal r) else szero

/-- Column `i` of the Fourth tensor at field width `w`. -/
def fourthColW (w i : ℕ) : SVec := ssum ((List.finRange 56).map (fourthTermW w i))

/-- The packed Fourth tensor at field width `w`. -/
@[irreducible] def fourthSrcXW (w : ℕ) : List SVec := (List.range 24).map (fourthColW w)

/-- Bounds and values of one record contribution. -/
theorem fourthTermW_spec {w : ℕ} (hw : 7 ≤ w) (i : ℕ) (r : Fin 56) :
    SBnd w (2 ^ 12) 1 (fourthTermW w i r) ∧ ∀ k, sval w (fourthTermW w i r) k =
      if (generatedFourthOddRootOutputData r).2.val = i then
        (if k = (generatedFourthOddRootOutputData r).1.val then fourthRootVal r
          else if k = (generatedFourthOddRootOutputData r).1.val + 2048 then -fourthRootVal r
          else 0) else 0 := by
  unfold fourthTermW
  split_ifs with h
  · have h1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have hu := unitVec_spec w (generatedFourthOddRootOutputData r).1.val (fourthRootVal r)
      (generatedFourthOddRootOutputData r).1.isLt (by rw [fourthRootVal_natAbs]; exact h1)
    rw [fourthRootVal_natAbs] at hu
    exact hu
  · exact ⟨SBnd_zero _ _ _, fun k => sval_zero _ _⟩

/-- Bounds and values of a column. -/
theorem fourthColW_spec {w : ℕ} (hw : 7 ≤ w) (i : ℕ) :
    SBnd w (2 ^ 12) 56 (fourthColW w i) ∧ ∀ k < 4096, sval w (fourthColW w i) k =
      ∑ r : Fin 56, sval w (fourthTermW w i r) k := by
  have h56 : 56 * 1 < 2 ^ w := by
    calc 56 * 1 < 2 ^ 7 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have h := ssum_spec (w := w) (n := 2 ^ 12) (B := 1) ((List.finRange 56).map (fourthTermW w i))
    (fun x hx => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact (fourthTermW_spec hw i r).1) (by simpa using h56)
  simp only [List.length_map, List.length_finRange, mul_one] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rw [fourthColW, h.2 k (by norm_num; exact hk), List.map_map, Fin.sum_univ_def]
  rfl

/-- Bounds of the packed Fourth tensor at width `w`. -/
theorem fourthSrcXW_bnd {w : ℕ} (hw : 7 ≤ w) : TBnd w 56 (fourthSrcXW w) := by
  intro i hi
  rw [fourthSrcXW, tcol_range_map _ 24 i hi]
  exact (fourthColW_spec hw i).1

/-- The packed Fourth tensor at width `w` is the canonical integer tensor. -/
theorem fourthSrcXW_val {w : ℕ} (hw : 7 ≤ w) (k : Fin 4096) (i : Fin 24) :
    sval w (tcol (fourthSrcXW w) i.val) k.val =
      generatedAxisGlobalCanonicalFourthTensorInteger k i := by
  rw [fourthSrcXW, tcol_range_map _ 24 i.val i.isLt, (fourthColW_spec hw i.val).2 k.val k.isLt,
    generatedAxisGlobalCanonicalFourthTensorInteger]
  apply Finset.sum_congr rfl
  intro r _
  rw [(fourthTermW_spec hw i.val r).2 k.val, fourthRootVal]
  exact fifth_record_term k i _ _ _

/-- The Fourth axis as an identification vector with tensor columns of width `w`. -/
def fourthSrcVecW (w : ℕ) : IdentVec :=
  ⟨fourthSrcMat, fourthSrcShort, 1 / 8, tensorRat w (fourthSrcXW w) 1⟩

/-- The tensor block at width `w`. -/
theorem fourthSrcVecW_ten (w : ℕ) : (fourthSrcVecW w).ten = tensorRat w (fourthSrcXW w) 1 := rfl

/-- The short block at width `w` is the Fourth short block. -/
theorem fourthSrcVecW_sh (w : ℕ) : (fourthSrcVecW w).sh = fourthSrcShort := rfl

set_option maxRecDepth 20000 in
/-- The representation at width `w` is the representation at width `128`. -/
theorem fourthSrcVecW_real {w : ℕ} (hw : 7 ≤ w) : (fourthSrcVecW w).real = fourthSrcVec.real := by
  have hten : (fourthSrcVecW w).ten = fourthSrcVec.ten := by
    funext k i
    rw [fourthSrcVecW_ten, fourthSrcVec_ten]
    change (sval w (tcol (fourthSrcXW w) i.val) k.val : ℚ) / 1 =
      (sval 128 (tcol fourthSrcX i.val) k.val : ℚ) / 1
    rw [fourthSrcXW_val hw, fourthSrcX_val]
  change generatedAxisGlobalRationalPacketReal (fourthSrcVecW w).packet =
    generatedAxisGlobalRationalPacketReal fourthSrcVec.packet
  congr 1
  unfold IdentVec.packet
  rw [hten]
  rfl

/-- The representation at width `w` gives the genuine coordinates of representative `3`. -/
theorem fourthSrcW_rep {w : ℕ} (hw : 7 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 3) = (fourthSrcVecW w).real := by
  rw [fourthSrcVecW_real hw]
  exact fourthSrc_rep

/-- The short block at width `w` satisfies the range conditions. -/
theorem fourthSrcVecW_ok (w : ℕ) : (fourthSrcVecW w).sh.ok = true := fourthSrcVec_ok

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
