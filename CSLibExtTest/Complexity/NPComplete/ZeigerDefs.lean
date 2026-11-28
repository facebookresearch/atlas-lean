/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ZeigerDefs

namespace MetaMathlibExt.Complexity.NPComplete.Zeiger

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ZeigerInstance) :
    zeigerDec (bitEncode i) = true ↔ WellFormed i ∧ ZeigerFeasible i := by
  simp [zeigerDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : zeigerDec [true] = false := by
  have h : bitDecode (α := ZeigerInstance) [true] = none := rfl
  simp [zeigerDec, h]

/-- Two cells pointing at each other, the left one numbered `a`. -/
private abbrev facing (a : ℕ) : ZeigerInstance := [[(1, a), (3, 0)]]

/-- The left cell. -/
private abbrev lft (a : ℕ) : Fin (rows (facing a)) × Fin (cols (facing a)) :=
  (⟨0, Nat.one_pos⟩, ⟨0, Nat.two_pos⟩)

/-- The right cell. -/
private abbrev rgt (a : ℕ) : Fin (rows (facing a)) × Fin (cols (facing a)) :=
  (⟨0, Nat.one_pos⟩, ⟨1, Nat.one_lt_two⟩)

private theorem cells (a : ℕ) (x : Fin (rows (facing a)) × Fin (cols (facing a))) :
    x = lft a ∨ x = rgt a := by
  obtain ⟨⟨r, hr⟩, ⟨c, hc⟩⟩ := x
  simp only [rows, cols, facing, List.length_cons, List.length_nil, List.headD_cons] at hr hc
  obtain rfl : r = 0 := by omega
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simp

/-- Each cell sees exactly the other cell. -/
private theorem ray_iff (a : ℕ) (x y : Fin (rows (facing a)) × Fin (cols (facing a))) :
    Ray (facing a) x y ↔ x ≠ y := by
  rcases cells a x with rfl | rfl <;> rcases cells a y with rfl | rfl <;>
    simp [Ray, cell, Fin.ext_iff, Fin.lt_def]

open Classical in
/-- The cells seen from `x` are exactly the other cell. -/
private theorem seen (a : ℕ) (x : Fin (rows (facing a)) × Fin (cols (facing a))) :
    (Finset.univ.filter fun y => Ray (facing a) x y) =
      {if x = lft a then rgt a else lft a} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, ray_iff]
  rcases cells a x with rfl | rfl <;> rcases cells a y with rfl | rfl <;> simp [Fin.ext_iff]

/-- Two facing arrows with value `1` each: each sees one cell, holding one distinct value. -/
example : zeigerDec (bitEncode (facing 1)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, fun _ => 1, fun _ => Nat.one_pos, ?_, ?_⟩
  · intro x hx
    rcases cells 1 x with rfl | rfl <;> simp_all [cell]
  · intro x
    rw [seen]
    simp

/-- Number `2` on the left cell is rejected: it sees one cell, so at most one value. -/
example : zeigerDec (bitEncode (facing 2)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, v, -, hgiven, hcount⟩
  have h := hcount (lft 2)
  rw [hgiven (lft 2) (by simp [cell]), seen] at h
  simp [cell] at h

/-- The rejected instance is well formed, so the rejection comes from the number. -/
example : WellFormed (facing 2) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.Zeiger
