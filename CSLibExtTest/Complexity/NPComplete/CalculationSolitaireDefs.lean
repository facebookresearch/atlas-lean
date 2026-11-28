/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CalculationSolitaireDefs

namespace MetaMathlibExt.Complexity.NPComplete.CalculationSolitaire

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : CalculationSolitaireInstance) :
    calculationSolitaireDec (bitEncode i) = true ↔
      WellFormed i ∧ CalculationSolitaireFeasible i := by
  simp [calculationSolitaireDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : calculationSolitaireDec [true] = false := by
  have h : bitDecode (α := CalculationSolitaireInstance) [true] = none := rfl
  simp [calculationSolitaireDec, h]

/-- Every rank in `1, 2, 3` occurs exactly twice when the two foundations hold one card each,
`1` on the `1`-foundation and `2` on the `2`-foundation, and the cards `1, 2, 3, 3` are dealt
elsewhere. -/
private theorem wellFormed_of (i : CalculationSolitaireInstance) (hk : i.1 = 3)
    (hs : i.2.1 = [1, 1]) (ht : i.2.2.1.length = 2)
    (hcards : ∀ x ∈ i.2.2.1.flatten ++ i.2.2.2, 1 ≤ x ∧ x ≤ 3)
    (hcount : ∀ r ∈ [1, 2, 3], onFoundations i r + (i.2.2.1.flatten ++ i.2.2.2).count r = 2) :
    WellFormed i := by
  refine ⟨hk ▸ Nat.prime_three, by simp [hs], by simp [hs, hk], by simp [hs, hk], by simp [hs, ht],
    hk ▸ hcards, ?_⟩
  intro r h₁ h₂
  rw [hs]
  obtain rfl | rfl | rfl : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  all_goals exact hcount _ (by simp)

/-- With `k = 3`, the stock `3, 2, 1, 3` is cleared by parking `3` on a tableau pile, playing `2`
and then the parked `3` on the `1`-foundation, and `1` then `3` on the `2`-foundation. -/
example : calculationSolitaireDec (bitEncode
    ((3, [1, 1], [[], []], [3, 2, 1, 3]) : CalculationSolitaireInstance)) = true := by
  refine (accepts_encoding _).2 ⟨wellFormed_of _ rfl rfl rfl (by decide) (by decide), [3, 3], ?_⟩
  refine .head (b := ([1, 1], [[3], []], [2, 1, 3]))
    (Or.inr (Or.inl ⟨3, [2, 1, 3], 0, [], rfl, rfl, rfl⟩)) ?_
  refine .head (b := ([2, 1], [[3], []], [1, 3]))
    (Or.inl ⟨2, [1, 3], 0, 1, rfl, rfl, by decide, by decide, rfl⟩) ?_
  refine .head (b := ([3, 1], [[], []], [1, 3]))
    (Or.inr (Or.inr ⟨3, [], 0, 0, 2, rfl, rfl, by decide, by decide, rfl⟩)) ?_
  refine .head (b := ([3, 2], [[], []], [3]))
    (Or.inl ⟨1, [3], 1, 1, rfl, rfl, by decide, by decide, rfl⟩) ?_
  exact .single (Or.inl ⟨3, [], 1, 2, rfl, rfl, by decide, by decide, rfl⟩)

/-- With the stock empty and both tableau piles topped by `3`, while the foundations need `2`
and `1`, no move is possible, so the tableau can never be cleared. -/
example : calculationSolitaireDec (bitEncode
    ((3, [1, 1], [[3, 2], [3, 1]], []) : CalculationSolitaireInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, f, h⟩
  rcases h.cases_head with h | ⟨c, hstep, -⟩
  · simp at h
  rcases hstep with ⟨x, rest, -, -, hx, -⟩ | ⟨x, rest, -, -, hx, -⟩ |
    ⟨x, p, j, idx, n, hj, hidx, -, hcard, -⟩
  · simp at hx
  · simp at hx
  · clear h
    rcases j with _ | _ | j <;> rcases idx with _ | _ | idx <;> simp at hj hidx <;>
      obtain ⟨rfl, -⟩ := hj <;> subst hidx <;> simp [card] at hcard

end MetaMathlibExt.Complexity.NPComplete.CalculationSolitaire
