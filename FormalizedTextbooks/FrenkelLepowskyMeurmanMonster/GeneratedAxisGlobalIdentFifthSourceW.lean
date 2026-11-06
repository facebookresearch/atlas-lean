/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSource

/-! # The Fifth axis with packed tensor columns of any field width

`fifthSrcVecW w` is `fifthSrcVec` with the packed tensor columns at field width `w` (any
`w ≥ 7`).  Smaller widths halve kernel time and memory of the packed tensor evaluation; the
width only has to accommodate the numerator bounds of the words used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false

/-- The contribution of record `r` to column `i`, at field width `w`. -/
def fifthTermW (w i : ℕ) (r : Fin 64) : SVec :=
  if (generatedFifthOddRootOutputData r).2.val = i then
    unitVec w (generatedFifthOddRootOutputData r).1.val (fifthRootVal r) else szero

/-- Column `i` of the Fifth tensor at field width `w`. -/
def fifthColW (w i : ℕ) : SVec := ssum ((List.finRange 64).map (fifthTermW w i))

/-- The packed Fifth tensor at field width `w`. -/
@[irreducible] def fifthSrcXW (w : ℕ) : List SVec := (List.range 24).map (fifthColW w)

/-- Bounds and values of one record contribution. -/
theorem fifthTermW_spec {w : ℕ} (hw : 7 ≤ w) (i : ℕ) (r : Fin 64) :
    SBnd w (2 ^ 12) 1 (fifthTermW w i r) ∧ ∀ k, sval w (fifthTermW w i r) k =
      if (generatedFifthOddRootOutputData r).2.val = i then
        (if k = (generatedFifthOddRootOutputData r).1.val then fifthRootVal r
          else if k = (generatedFifthOddRootOutputData r).1.val + 2048 then -fifthRootVal r
          else 0) else 0 := by
  unfold fifthTermW
  split_ifs with h
  · have h1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have hu := unitVec_spec w (generatedFifthOddRootOutputData r).1.val (fifthRootVal r)
      (generatedFifthOddRootOutputData r).1.isLt (by rw [fifthRootVal_natAbs]; exact h1)
    rw [fifthRootVal_natAbs] at hu
    exact hu
  · exact ⟨SBnd_zero _ _ _, fun k => sval_zero _ _⟩

/-- Bounds and values of a column. -/
theorem fifthColW_spec {w : ℕ} (hw : 7 ≤ w) (i : ℕ) :
    SBnd w (2 ^ 12) 64 (fifthColW w i) ∧ ∀ k < 4096, sval w (fifthColW w i) k =
      ∑ r : Fin 64, sval w (fifthTermW w i r) k := by
  have h64 : 64 * 1 < 2 ^ w := by
    calc 64 * 1 < 2 ^ 7 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have h := ssum_spec (w := w) (n := 2 ^ 12) (B := 1) ((List.finRange 64).map (fifthTermW w i))
    (fun x hx => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact (fifthTermW_spec hw i r).1) (by simpa using h64)
  simp only [List.length_map, List.length_finRange, mul_one] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rw [fifthColW, h.2 k (by norm_num; exact hk), List.map_map, Fin.sum_univ_def]
  rfl

/-- Bounds of the packed Fifth tensor at width `w`. -/
theorem fifthSrcXW_bnd {w : ℕ} (hw : 7 ≤ w) : TBnd w 64 (fifthSrcXW w) := by
  intro i hi
  rw [fifthSrcXW, tcol_range_map _ 24 i hi]
  exact (fifthColW_spec hw i).1

/-- The packed Fifth tensor at width `w` is the canonical integer tensor. -/
theorem fifthSrcXW_val {w : ℕ} (hw : 7 ≤ w) (k : Fin 4096) (i : Fin 24) :
    sval w (tcol (fifthSrcXW w) i.val) k.val = generatedAxisGlobalFifthTensorInteger k i := by
  rw [fifthSrcXW, tcol_range_map _ 24 i.val i.isLt, (fifthColW_spec hw i.val).2 k.val k.isLt,
    generatedAxisGlobalFifthTensorInteger]
  apply Finset.sum_congr rfl
  intro r _
  rw [(fifthTermW_spec hw i.val r).2 k.val, fifthRootVal]
  exact fifth_record_term k i _ _ _

/-- The Fifth axis as an identification vector with tensor columns of width `w`. -/
def fifthSrcVecW (w : ℕ) : IdentVec := ⟨fifthSrcMat, fifthSrcShort, 1 / 16, tensorRat w (fifthSrcXW w) 1⟩

/-- The tensor block at width `w`. -/
theorem fifthSrcVecW_ten (w : ℕ) : (fifthSrcVecW w).ten = tensorRat w (fifthSrcXW w) 1 := rfl

/-- The short block at width `w` is the Fifth short block. -/
theorem fifthSrcVecW_sh (w : ℕ) : (fifthSrcVecW w).sh = fifthSrcShort := rfl

set_option maxRecDepth 20000 in
/-- The representation at width `w` is the representation at width `128`. -/
theorem fifthSrcVecW_real {w : ℕ} (hw : 7 ≤ w) : (fifthSrcVecW w).real = fifthSrcVec.real := by
  have hten : (fifthSrcVecW w).ten = fifthSrcVec.ten := by
    funext k i
    rw [fifthSrcVecW_ten, fifthSrcVec_ten]
    change (sval w (tcol (fifthSrcXW w) i.val) k.val : ℚ) / 1 =
      (sval 128 (tcol fifthSrcX i.val) k.val : ℚ) / 1
    rw [fifthSrcXW_val hw, fifthSrcX_val]
  change generatedAxisGlobalRationalPacketReal (fifthSrcVecW w).packet =
    generatedAxisGlobalRationalPacketReal fifthSrcVec.packet
  congr 1
  unfold IdentVec.packet
  rw [hten]
  rfl

/-- The representation at width `w` gives the genuine coordinates of representative `4`. -/
theorem fifthSrcW_rep {w : ℕ} (hw : 7 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 4) = (fifthSrcVecW w).real := by
  rw [fifthSrcVecW_real hw]
  exact fifthSrc_rep

set_option maxRecDepth 100000 in
/-- The short block at width `w` satisfies the range conditions. -/
theorem fifthSrcVecW_ok (w : ℕ) : (fifthSrcVecW w).sh.ok = true := fifthSrcVec_ok

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
