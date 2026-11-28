/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShakashakaDefs

namespace MetaMathlibExt.Complexity.NPComplete.Shakashaka

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ShakashakaInstance) :
    shakashakaDec (bitEncode i) = true ↔ WellFormed i ∧ ShakashakaFeasible i := by
  simp [shakashakaDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : shakashakaDec [true] = false := by
  have h : bitDecode (α := ShakashakaInstance) [true] = none := rfl
  simp [shakashakaDec, h]

/-- With every white square left white, the white area of the board `[0 | white]` (a black `0`
next to a white square) is the closed unit square `[0, 1] × [1, 2]`. -/
private theorem whiteSet_20 :
    whiteSet [[2, 0]] (fun _ _ => 0) = Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (1 : ℝ) 2 := by
  ext ⟨x, y⟩
  simp only [whiteSet, whitePart, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]
  constructor
  · rintro ⟨r, hr, c, hc, hcell, h1, h2, h3, h4, -⟩
    simp only [List.length_cons, List.length_nil, List.getD_cons_zero] at hr hc
    obtain rfl : r = 0 := by omega
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · simp [cell] at hcell
    · norm_num at h1 h2 h3 h4
      exact ⟨⟨h1, h2⟩, h3, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨0, by simp, 1, by simp, rfl, by simpa using h1, by simpa using h2, by simpa using h3,
      by norm_num; linarith, trivial⟩

/-- The board `[0 | white]` is solved by leaving the white square white: the black `0` has no
neighboring half-black square, and the white area is one open square. -/
example : shakashakaDec (bitEncode ([[2, 0]] : ShakashakaInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, fun _ _ => 0, by decide, ?_⟩
  intro p hp
  rw [whiteSet_20, interior_prod_eq, interior_Icc, interior_Icc] at hp ⊢
  refine ⟨0, 1, 1, 2, Or.inl ?_⟩
  rw [(isPreconnected_Ioo.prod isPreconnected_Ioo).connectedComponentIn hp]
  ext q
  simp only [Set.mem_prod, Set.mem_Ioo, Set.mem_ofPred_eq]
  tauto

/-- The board `[1 | black]` has no solution: the black `1` needs one neighboring white square
with a black half, but its only neighbor is black. -/
example : shakashakaDec (bitEncode ([[3, 1]] : ShakashakaInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, sol, hnum, -⟩ := (accepts_encoding _).1 h
  have h0 := hnum 0 (by simp) 0 (by simp) (by decide)
  rw [Finset.card_eq_zero.mpr] at h0
  · simp [cell] at h0
  · refine Finset.filter_eq_empty_iff.2 fun q hq hf => ?_
    simp only [Finset.mem_product, Finset.mem_range, List.length_cons, List.length_nil,
      List.getD_cons_zero] at hq
    obtain ⟨q1, q2⟩ := q
    obtain rfl : q1 = 0 := by simp at hq; omega
    rcases (by simp at hq; omega : q2 = 0 ∨ q2 = 1) with rfl | rfl <;> simp [cell] at hf

/-- An entry above `6` makes the board malformed. -/
example : shakashakaDec (bitEncode ([[7]] : ShakashakaInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.2 [7] (by simp) 7 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.Shakashaka
