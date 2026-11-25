/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ArithmeticProgressionAuxiliaryFloor
import MathlibExt.Algebra.Polynomial.ArithmeticProgressionAuxiliaryRoot
import Mathlib.Tactic.NormNum

/-!
# Floors at powers of the auxiliary root

The first three examples fail the strict cutoff `(m + 1) * d < 2 * a` from Proposition 4.
The last example has a strict cutoff and probes the endpoint exponent.
-/

open MetaMathlibExt

example : ∃ x : ℝ, 0 < x ∧ x ^ 4 - 4 * x - 3 = 0 ∧ ⌊x⌋ = 1 := by
  obtain ⟨⟨x, ⟨hx, hG⟩, _⟩, _⟩ :=
    arithProgPoly_eq3_existsUnique_pos (m := 2) (a := 1) (d := 1) (by decide) (by decide)
      (by decide)
  have hf := arithProgPoly_floor_lam_pow_eq_of_eight (m := 2) (a := 1) (d := 1)
    (hm := by decide) (ha := by decide) (hd := by decide) (had := by decide)
    (lam := x) (hlam := hx) (hG := hG) (p := 1) (hp1 := by decide) (hpm := by decide)
  norm_num at hG hf
  exact ⟨x, hx, hG, hf⟩

example : ∃ x : ℝ, 0 < x ∧ 3 * x ^ 4 + x ^ 3 - 9 * x - 7 = 0 ∧ ⌊3 * x⌋ = 4 := by
  obtain ⟨⟨x, ⟨hx, hG⟩, _⟩, _⟩ :=
    arithProgPoly_eq3_existsUnique_pos (m := 2) (a := 3) (d := 2) (by decide) (by decide)
      (by decide)
  have hf := arithProgPoly_floor_lam_pow_eq_of_eight (m := 2) (a := 3) (d := 2)
    (by decide) (by decide) (by decide) (by decide) x hx hG 1 (by decide) (by decide)
  norm_num at hG hf
  exact ⟨x, hx, hG, hf⟩

example : ∃ x : ℝ, 0 < x ∧ 2 * x ^ 5 + x ^ 4 - 6 * x - 5 = 0 ∧
    ⌊2 * x⌋ = 2 ∧ ⌊2 * x ^ 2⌋ = 3 := by
  obtain ⟨⟨x, ⟨hx, hG⟩, _⟩, _⟩ :=
    arithProgPoly_eq3_existsUnique_pos (m := 3) (a := 2) (d := 1) (by decide) (by decide)
      (by decide)
  have hf := arithProgPoly_floor_lam_pow_eq_of_eight (m := 3) (a := 2) (d := 1)
    (by decide) (by decide) (by decide) (by decide) x hx hG
  have hf₁ := hf 1 (by decide) (by decide)
  have hf₂ := hf 2 (by decide) (by decide)
  norm_num at hG hf₁ hf₂
  exact ⟨x, hx, hG, hf₁, hf₂⟩

example : ∃ x : ℝ, 0 < x ∧ 3 * x ^ 6 + 2 * x ^ 5 - 8 * x - 7 = 0 ∧ ⌊3 * x ^ 3⌋ = 5 := by
  obtain ⟨⟨x, ⟨hx, hG⟩, _⟩, _⟩ :=
    arithProgPoly_eq3_existsUnique_pos (m := 4) (a := 3) (d := 1) (by decide) (by decide)
      (by decide)
  have hf := arithProgPoly_floor_lam_pow_eq_of_eight (m := 4) (a := 3) (d := 1)
    (by decide) (by decide) (by decide) (by decide) x hx hG 3 (by decide) (by decide)
  norm_num at hG hf
  exact ⟨x, hx, hG, hf⟩
