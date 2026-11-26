/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.EvenOddCompositions

namespace MetaMathlibExt

-- A single block of size three contributes the odd sign.
example : compositionOddMinusEven 3 (· = Composition.single 3 (by decide)) = 1 := by
  classical
  rw [compositionOddMinusEven, Fintype.sum_eq_single (Composition.single 3 (by decide))
    (fun c hc => by simp [hc])]
  simp

-- The part after a small part may equal the threshold precisely when it is last.
example : IsHuangSmallPartPlacement 2 [2, 1, 2] := by
  intro i a hi ha
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  change i < 3 at hi'
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact (Nat.lt_irrefl 2 ha).elim
  · exact ⟨by decide, ⟨2, rfl, le_rfl⟩, 2, rfl, Or.inl rfl⟩
  · exact (Nat.lt_irrefl 2 ha).elim

example : ¬ IsHuangSmallPartPlacement 2 [2, 1, 2, 2] := by
  intro h
  simpa using (h 1 1 rfl (by decide)).2.2

-- The only source composition of four with one exceptional part is [4].
example : Nat.card {c : Composition 5 //
    (c.blocks.filter fun a => a < 2).length = 1 ∧ IsHuangSmallPartPlacement 2 c.blocks} = 1 := by
  rw [← card_composition_huang_franklin 2 1 4 (by decide) (by decide), Nat.card_eq_one_iff_exists]
  refine ⟨⟨Composition.single 4 (by decide), by decide, by simp⟩, ?_⟩
  rintro ⟨c, hcount, hadm⟩
  apply Subtype.ext
  by_contra h
  change c ≠ Composition.single 4 (by decide) at h
  have hlt : ∀ i, c.blocksFun i < 4 := (Composition.ne_single_iff (by decide : 0 < 4)).mp h
  have hall (x : ℕ) (hx : x ∈ c.blocks) : x % 2 = 1 % 2 := by
    by_contra hmod
    have := hadm x hx hmod
    rw [← c.ofFn_blocksFun, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have := hlt i
    omega
  have he : (c.blocks.filter fun x => decide (x % 2 ≠ 1 % 2)) = [] := by
    simpa [List.filter_eq_nil_iff] using hall
  rw [he] at hcount
  contradiction

-- With no allowed small values, the terms for a positive mark count cancel (k = 1).
example : compositionOddMinusEven 3 (fun c =>
    (c.blocks.filter fun a => a < 1).length = 1 ∧ IsHuangSmallPartPlacement 1 c.blocks) = 0 := by
  rw [show 3 = 3 + 1 - 1 by decide,
    compositionOddMinusEven_huang_eq_sum 1 1 3 (by decide) (by decide)]
  decide

-- No marks: the generalized binomial convention gives one empty coloring.
example : compositionOddMinusEven 1 (fun c =>
    (c.blocks.filter fun a => a < 1).length = 0 ∧ IsHuangSmallPartPlacement 1 c.blocks) = 1 := by
  rw [show 1 = 1 + 1 - 1 by decide,
    compositionOddMinusEven_huang_eq_sum 1 0 1 (by decide) (by decide)]
  decide

-- This instance includes both an odd shift count and a nonzero exclusion term.
example : compositionOddMinusEven 10 (fun c =>
    (c.blocks.filter fun a => a < 3).length = 1 ∧ IsHuangSmallPartPlacement 3 c.blocks) = 6 := by
  rw [show 10 = 8 + 3 - 1 by decide,
    compositionOddMinusEven_huang_eq_sum 3 1 8 (by decide) (by decide)]
  decide

end MetaMathlibExt
