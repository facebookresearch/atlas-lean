/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.YosenabeDefs

namespace MetaMathlibExt.Complexity.NPComplete.Yosenabe

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : YosenabeInstance) :
    yosenabeDec (bitEncode i) = true ↔ WellFormed i ∧ YosenabeFeasible i := by
  simp [yosenabeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : yosenabeDec [true] = false := by
  have h : bitDecode (α := YosenabeInstance) [true] = none := rfl
  simp [yosenabeDec, h]

/-- A circle numbered `1` next to a gray cell labelled `a`. -/
private abbrev pair (a : ℕ) : YosenabeInstance := [[(1, 1), (2, a)]]

/-- The circle cell. -/
private abbrev circ (a : ℕ) : Cell (pair a) := (⟨0, Nat.one_pos⟩, ⟨0, Nat.two_pos⟩)

/-- The gray cell. -/
private abbrev gray (a : ℕ) : Cell (pair a) := (⟨0, Nat.one_pos⟩, ⟨1, Nat.one_lt_two⟩)

private theorem cells (a : ℕ) (x : Cell (pair a)) : x = circ a ∨ x = gray a := by
  obtain ⟨⟨r, hr⟩, ⟨c, hc⟩⟩ := x
  simp only [rows, cols, pair, List.length_cons, List.length_nil, List.headD_cons] at hr hc
  obtain rfl : r = 0 := by omega
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simp

private theorem circle_iff (a : ℕ) (x : Cell (pair a)) : Circle (pair a) x ↔ x = circ a := by
  rcases cells a x with rfl | rfl <;> simp [Circle, cell, Fin.ext_iff]

private theorem gray_iff (a : ℕ) (x : Cell (pair a)) : Gray (pair a) x ↔ x = gray a := by
  rcases cells a x with rfl | rfl <;> simp [Gray, cell, Fin.ext_iff]

private theorem sameArea_iff (a : ℕ) (x y : Cell (pair a)) :
    SameArea (pair a) x y ↔ x = gray a ∧ y = gray a := by
  constructor
  · rintro ⟨hx, hy, -⟩
    exact ⟨(gray_iff a x).1 hx, (gray_iff a y).1 hy⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(gray_iff a _).2 rfl, (gray_iff a _).2 rfl, .refl _⟩

/-- Every instance of this shape with a positive label is well formed: there is one gray
area, holding one labelled cell. -/
private theorem pair_wellFormed (a : ℕ) : WellFormed (pair a) := by
  refine ⟨Nat.one_pos, Nat.two_pos, ?_, ?_, ?_⟩
  · intro row h
    simp only [List.mem_singleton] at h
    subst h
    rfl
  · intro row h e he
    simp only [List.mem_singleton] at h
    subst h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp
  intro g g' h _ _
  obtain ⟨rfl, rfl⟩ := (sameArea_iff a g g').1 h
  rfl

open Classical in
/-- The circles reaching the gray area are at most the one circle. -/
private theorem filter_sub (a : ℕ) (tip : Cell (pair a) → Cell (pair a)) :
    (Finset.univ.filter fun x => Circle (pair a) x ∧ SameArea (pair a) (tip x) (gray a)) ⊆
      {circ a} := by
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simpa using (circle_iff a x).1 hx.1

open Classical in
/-- The circle `1` moves onto the gray cell labelled `1`. -/
example : yosenabeDec (bitEncode (pair 1)) = true := by
  apply (accepts_encoding _).2
  refine ⟨pair_wellFormed 1, fun _ => gray 1, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain rfl := (circle_iff 1 x).1 hx
    refine ⟨(gray_iff 1 _).2 rfl, Or.inl rfl, ?_⟩
    rintro z ⟨hzx, hz⟩ hzc
    exact hzx ((circle_iff 1 z).1 hzc)
  · intro x x' hx hx' hne
    exact absurd (((circle_iff 1 x).1 hx).trans ((circle_iff 1 x').1 hx').symm) hne
  · intro g hg _
    obtain rfl := (gray_iff 1 g).1 hg
    have hfilter : (Finset.univ.filter fun x => Circle (pair 1) x ∧
        SameArea (pair 1) ((fun _ => gray 1) x) (gray 1)) = {circ 1} := by
      refine Finset.Subset.antisymm (filter_sub 1 _) ?_
      simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(circle_iff 1 _).2 rfl, (sameArea_iff 1 _ _).2 ⟨rfl, rfl⟩⟩
    rw [hfilter]
    simp [cell]
  · intro g hg
    obtain rfl := (gray_iff 1 g).1 hg
    exact ⟨circ 1, (circle_iff 1 _).2 rfl, (sameArea_iff 1 _ _).2 ⟨rfl, rfl⟩⟩

/-- Label `2` is rejected: the only circle carries `1`, so the area receives a sum of `0` or
`1`. -/
example : yosenabeDec (bitEncode (pair 2)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, tip, -, -, hsum, -⟩
  have h := hsum (gray 2) ((gray_iff 2 _).2 rfl) (by simp [cell])
  rcases Finset.subset_singleton_iff.1 (filter_sub 2 tip) with hf | hf <;>
    rw [hf] at h <;> simp [cell] at h

/-- The rejected instance is well formed, so the rejection comes from the label. -/
example : WellFormed (pair 2) := pair_wellFormed 2

end MetaMathlibExt.Complexity.NPComplete.Yosenabe
