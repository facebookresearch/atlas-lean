/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ExistentialPresburgerArithmeticDefs

namespace MetaMathlibExt.Complexity.NPComplete.ExistentialPresburgerArithmetic

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Logic.LegacyPL
open NonTautology (parse valuation)

private theorem accepts_encoding (i : ExistentialPresburgerArithmeticInstance) :
    existentialPresburgerArithmeticDec (bitEncode i) = true ↔
      WellFormed i ∧ ExistentialPresburgerArithmeticFeasible i := by
  simp [existentialPresburgerArithmeticDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : existentialPresburgerArithmeticDec [true] = false := by
  have h : bitDecode (α := ExistentialPresburgerArithmeticInstance) [true] = none := rfl
  simp [existentialPresburgerArithmeticDec, h]

/-- `∃ y, lo ≤ y ∧ y ≤ hi` in one variable: atom `0` is `0·y + lo ≤ 1·y + 0`, atom `1` is
`1·y + 0 ≤ 0·y + hi`, and the postfix tokens `atom 0, atom 1, ∧` conjoin them. -/
private abbrev between (lo hi : ℕ) : ExistentialPresburgerArithmeticInstance :=
  (1, [([0], lo, [1], 0), ([1], 0, [0], hi)], [(0, 0), (0, 1), (2, 0)])

private theorem parse_between (lo hi : ℕ) :
    parse (between lo hi).2.2 =
      some (Proposition.and (Proposition.atom ((0 : ℕ) : WithBot ℕ))
        (Proposition.atom ((1 : ℕ) : WithBot ℕ))) := rfl

/-- `∃ y, 2 ≤ y ∧ y ≤ 3` holds with `y = 2`. -/
example : existentialPresburgerArithmeticDec (bitEncode (between 2 3)) = true := by
  refine (accepts_encoding _).2 ⟨⟨by rw [parse_between]; rfl, by decide, by decide⟩, _,
    parse_between 2 3, [2], rfl, ?_⟩
  simp only [Proposition.evalBool, valuation]
  decide

/-- `∃ y, 3 ≤ y ∧ y ≤ 2` is well formed but false in `ℕ`. -/
example : existentialPresburgerArithmeticDec (bitEncode (between 3 2)) = false := by
  cases h : existentialPresburgerArithmeticDec (bitEncode (between 3 2)) with
  | false => rfl
  | true =>
    obtain ⟨-, E, hE, ys, hlen, hev⟩ := (accepts_encoding _).1 h
    rw [parse_between] at hE
    obtain rfl := (Option.some.inj hE).symm
    match ys, hlen with
    | [y], _ =>
      simp only [Proposition.evalBool, valuation] at hev
      have h' : (decide (0 * y + 0 + 3 ≤ 1 * y + 0 + 0) &&
          decide (1 * y + 0 + 0 ≤ 0 * y + 0 + 2)) = true := hev
      simp at h'
      omega

end MetaMathlibExt.Complexity.NPComplete.ExistentialPresburgerArithmetic
