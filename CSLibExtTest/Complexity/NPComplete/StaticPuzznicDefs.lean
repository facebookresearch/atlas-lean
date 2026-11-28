/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.StaticPuzznicDefs

namespace MetaMathlibExt.Complexity.NPComplete.StaticPuzznic

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : StaticPuzznicInstance) :
    staticPuzznicDec (bitEncode i) = true ↔ WellFormed i ∧ StaticPuzznicFeasible i := by
  simp [staticPuzznicDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : staticPuzznicDec [true] = false := by
  have h : bitDecode (α := StaticPuzznicInstance) [true] = none := rfl
  simp [staticPuzznicDec, h]

/-- The cells of a one-row grid `[a, b]`: `a` and `b` in row `0`, walls everywhere else. -/
private theorem cell_pair (a b r c : ℕ) :
    cell [[a, b]] r c = if r = 0 then (if c = 0 then a else if c = 1 then b else 1) else 1 := by
  rcases r with _ | r <;> rcases c with _ | _ | c <;> simp [cell]

/-- Nothing falls in a one-row grid: the row below it is outside, which reads as wall. -/
private theorem not_falling_pair (a b : ℕ) : ¬ Falling [[a, b]] := by
  rintro ⟨r, c, -, h⟩
  rw [cell_pair] at h
  simp at h

/-- Two blocks of the same pattern side by side match and vanish together. -/
example : staticPuzznicDec (bitEncode ([[2, 2]] : StaticPuzznicInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, [[0, 0]],
    Relation.ReflTransGen.single
    (Or.inr (Or.inl ⟨not_falling_pair 2 2, ⟨0, 0, by decide⟩, by decide⟩)), fun r c h => ?_⟩
  unfold IsBlock at h
  rw [cell_pair] at h
  split_ifs at h <;> omega

/-- Two blocks of different patterns side by side neither fall, match, nor have an empty cell to
slide into, so play is stuck with both blocks on the grid. -/
example : staticPuzznicDec (bitEncode ([[2, 3]] : StaticPuzznicInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, B, hB, hclear⟩ := (accepts_encoding _).1 h
  have nonzero : ∀ r c, cell [[2, 3]] r c ≠ 0 := by
    intro r c
    rw [cell_pair]
    split_ifs <;> omega
  have stuck : ∀ B', ¬ Step [[2, 3]] B' := by
    rintro B' (⟨r, c, -, h0, -⟩ | ⟨-, ⟨r, c, htwin⟩, -⟩ | ⟨-, -, r, c, c', -, -, h0, -⟩)
    · exact nonzero _ _ h0
    · have hb := htwin.1
      unfold IsBlock at hb
      rw [cell_pair] at hb
      split_ifs at hb with hr hc0 hc1 <;> try omega
      · subst hr hc0
        revert htwin
        decide
      · subst hr hc1
        revert htwin
        decide
    · exact nonzero _ _ h0
  rcases Relation.ReflTransGen.cases_head hB with rfl | ⟨B', hs, -⟩
  · exact hclear 0 0 (by unfold IsBlock; decide)
  · exact stuck B' hs

/-- Rows of different lengths make the grid malformed. -/
example : staticPuzznicDec (bitEncode ([[2], [0, 0]] : StaticPuzznicInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1 [0, 0] (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.StaticPuzznic
