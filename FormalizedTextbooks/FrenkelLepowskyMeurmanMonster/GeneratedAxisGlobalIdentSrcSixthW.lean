/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthSource

/-! # The Sixth axis with packed tensor columns of any field width

`sixthSrcVecW w` is `sixthSrcVec` with the packed tensor columns at field width `w` (any
`w ≥ 19`), mirroring `fifthSrcVecW`: smaller widths reduce kernel time and memory of packed word
actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative
set_option autoImplicit false

/-- Column `i` of the packed Sixth tensor at field width `w`. -/
def sixthColFW (w i : ℕ) : SVec :=
  ssum ((List.finRange 4096).map (fun n =>
    sixthSingle w n.val (sixthTNum n.val ⟨i % 24, Nat.mod_lt _ (by decide)⟩)))

/-- Bounds and values of a column at width `w`. -/
theorem sixthColFW_spec {w : ℕ} (hw : 19 ≤ w) (i : ℕ) :
    SBnd w (2 ^ 12) (4096 * 64) (sixthColFW w i) ∧ ∀ k < 4096,
      sval w (sixthColFW w i) k = sixthTNum k ⟨i % 24, Nat.mod_lt _ (by decide)⟩ := by
  have h19 : (2 : ℕ) ^ 19 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hv (n : ℕ) : (sixthTNum n ⟨i % 24, Nat.mod_lt _ (by decide)⟩).natAbs < 2 ^ w :=
    lt_of_le_of_lt (sixthTNum_natAbs _ _) (lt_of_lt_of_le (by norm_num) h19)
  have h := ssum_spec (w := w) (n := 2 ^ 12) (B := 64)
    ((List.finRange 4096).map (fun n =>
      sixthSingle w n.val (sixthTNum n.val ⟨i % 24, Nat.mod_lt _ (by decide)⟩)))
    (fun x hx => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx
      exact (sixthSingle_spec w n.val _ n.isLt (hv n.val)).1.mono (sixthTNum_natAbs _ _))
    (by simp only [List.length_map, List.length_finRange]; exact lt_of_lt_of_le (by norm_num) h19)
  simp only [List.length_map, List.length_finRange] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rw [sixthColFW, h.2 k (by norm_num; exact hk), List.map_map, ← Fin.sum_univ_def]
  simp only [Function.comp_apply, (sixthSingle_spec w _ _ (Fin.isLt _) (hv _)).2]
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro b _ hb
    split_ifs with h
    · exact absurd (Fin.ext h.symm) hb
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The packed Sixth tensor at width `w`. -/
@[irreducible] def sixthSrcXW (w : ℕ) : List SVec := (List.range 24).map (sixthColFW w)

/-- Bounds of the packed Sixth tensor at width `w`. -/
theorem sixthSrcXW_bnd {w : ℕ} (hw : 19 ≤ w) : TBnd w (4096 * 64) (sixthSrcXW w) := by
  intro i hi
  rw [sixthSrcXW, tcol_range_map _ 24 i hi]
  exact (sixthColFW_spec hw i).1

/-- The packed Sixth tensor at width `w` carries the executable numerators. -/
theorem sixthSrcXW_val {w : ℕ} (hw : 19 ≤ w) (k : Fin 4096) (i : Fin 24) :
    sval w (tcol (sixthSrcXW w) i.val) k.val = sixthTNum k.val i := by
  rw [sixthSrcXW, tcol_range_map _ 24 i.val i.isLt, (sixthColFW_spec hw i.val).2 k.val k.isLt]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-- The Sixth axis as an identification vector with tensor columns of width `w`. -/
def sixthSrcVecW (w : ℕ) : IdentVec :=
  ⟨sixthSrcMat, sixthSrcShort, 1 / 32, tensorRat w (sixthSrcXW w) 32⟩

/-- The tensor block at width `w`. -/
theorem sixthSrcVecW_ten (w : ℕ) : (sixthSrcVecW w).ten = tensorRat w (sixthSrcXW w) 32 := rfl

/-- The matrix block at width `w` is that of `sixthSrcVec`. -/
theorem sixthSrcVecW_mat (w : ℕ) : (sixthSrcVecW w).mat = sixthSrcVec.mat := rfl

/-- The short block at width `w` is that of `sixthSrcVec`. -/
theorem sixthSrcVecW_sh (w : ℕ) : (sixthSrcVecW w).sh = sixthSrcVec.sh := rfl

/-- The short scale at width `w` is that of `sixthSrcVec`. -/
theorem sixthSrcVecW_sden (w : ℕ) : (sixthSrcVecW w).sden = sixthSrcVec.sden := rfl

/-- The width-`w` representation has the same packet as `sixthSrcVec`. -/
theorem sixthSrcVecW_packet {w : ℕ} (hw : 19 ≤ w) :
    (sixthSrcVecW w).packet = sixthSrcVec.packet := by
  unfold IdentVec.packet
  rw [sixthSrcVecW_mat, sixthSrcVecW_sh, sixthSrcVecW_sden]
  congr 1
  congr 1
  funext t i
  change tensorRat w (sixthSrcXW w) 32 (generatedAxisGlobalSpinLabel t) i =
    tensorRat 128 sixthSrcX 32 (generatedAxisGlobalSpinLabel t) i
  change (sval w (tcol (sixthSrcXW w) i.val) (generatedAxisGlobalSpinLabel t).val : ℚ) / 32 =
    (sval 128 (tcol sixthSrcX i.val) (generatedAxisGlobalSpinLabel t).val : ℚ) / 32
  rw [sixthSrcXW_val hw, sixthSrcX_val]

/-- The width-`w` representation of family representative `5`. -/
theorem sixthSrcW_rep {w : ℕ} (hw : 19 ≤ w) :
    griessConwayEncode (generatedAxisGlobalTwelveRepresentative 5) = (sixthSrcVecW w).real := by
  rw [sixthSrc_rep, IdentVec.real, IdentVec.real, sixthSrcVecW_packet hw]

/-- The short block of the width-`w` representation satisfies the range conditions. -/
theorem sixthSrcVecW_ok (w : ℕ) : (sixthSrcVecW w).sh.ok = true := sixthSrcVec_ok

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
