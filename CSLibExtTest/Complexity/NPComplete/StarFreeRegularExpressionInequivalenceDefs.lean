/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.StarFreeRegularExpressionInequivalenceDefs

namespace MetaMathlibExt.Complexity.NPComplete.StarFreeRegularExpressionInequivalence

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : StarFreeRegularExpressionInequivalenceInstance) :
    starFreeRegularExpressionInequivalenceDec (bitEncode i) = true ↔
      WellFormed i ∧ StarFreeRegularExpressionInequivalenceFeasible i := by
  simp [starFreeRegularExpressionInequivalenceDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : starFreeRegularExpressionInequivalenceDec [true] = false := by
  have h : bitDecode (α := StarFreeRegularExpressionInequivalenceInstance) [true] = none := rfl
  simp [starFreeRegularExpressionInequivalenceDec, h]

/-- The single letter `0` (token `(2, 0)`) and `ε` (token `(1, 0)`) differ on the word `0`. -/
example : starFreeRegularExpressionInequivalenceDec
    (bitEncode ((1, [(2, 0)], [(1, 0)]) : StarFreeRegularExpressionInequivalenceInstance)) =
      true := by
  refine (accepts_encoding _).2 ⟨⟨.char 0, 1, ⟨rfl, by decide⟩, ⟨rfl, by decide⟩, rfl, rfl⟩,
    .char 0, 1, rfl, rfl, fun e => ?_⟩
  have hmem : [0] ∈ (RegularExpression.char 0 : RegularExpression ℕ).matches' := by
    simp
  rw [e] at hmem
  simp at hmem

/-- `0 + 0` (tokens `(2, 0) (2, 0) (3, 0)`) and `0` denote the same language, so the pair is a
no-instance. -/
example : starFreeRegularExpressionInequivalenceDec
    (bitEncode ((1, [(2, 0), (2, 0), (3, 0)], [(2, 0)]) :
      StarFreeRegularExpressionInequivalenceInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, E₁, E₂, h₁, h₂, hne⟩ := (accepts_encoding _).1 h
  have e₁ : E₁ = .char 0 + .char 0 := (Option.some.inj h₁).symm
  have e₂ : E₂ = .char 0 := (Option.some.inj h₂).symm
  subst e₁ e₂
  exact hne (by simp)

/-- `0*` (tokens `(2, 0) (5, 0)`) and `0` denote different languages, but `0*` has star height
`1`, so the instance is malformed and rejected. -/
example : starFreeRegularExpressionInequivalenceDec
    (bitEncode ((1, [(2, 0), (5, 0)], [(2, 0)]) :
      StarFreeRegularExpressionInequivalenceInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨⟨E₁, E₂, ⟨h₁, -⟩, -, hs, -⟩, -⟩ := (accepts_encoding _).1 h
  have e₁ : E₁ = (RegularExpression.char 0).star := (Option.some.inj h₁).symm
  subst e₁
  exact absurd hs (by decide)

/-- A token list that leaves two expressions on the stack spells no expression. -/
example : starFreeRegularExpressionInequivalenceDec
    (bitEncode ((1, [(2, 0), (2, 0)], [(2, 0)]) :
      StarFreeRegularExpressionInequivalenceInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, E₁, E₂, h₁, -, -⟩ := (accepts_encoding _).1 h
  exact absurd h₁ (by simp [parse, readToken])

end MetaMathlibExt.Complexity.NPComplete.StarFreeRegularExpressionInequivalence
