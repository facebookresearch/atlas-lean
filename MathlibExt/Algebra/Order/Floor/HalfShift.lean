/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Floor and ceiling of a quotient plus one half

When dividing by a positive natural number, the floor or ceiling of the quotient is
unchanged by taking the corresponding integer rounding of the numerator first.
Applying this to `q + m / 2` in `ℝ` gives the half-shift formulas.
-/

namespace MetaMathlibExt

/-- **Floor and ceiling of a quotient plus one half.** For every integer $q$ and every positive
integer $m$, $\lfloor q/m + 1/2 \rfloor = \lfloor (q + \lfloor m/2 \rfloor)/m \rfloor$ and
$\lceil q/m + 1/2 \rceil = \lceil (q + \lceil m/2 \rceil)/m \rceil$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 8. -/
public theorem floor_ceil_div_add_half (q : ℤ) (m : ℕ) (hm : 0 < m) :
    ⌊(q : ℝ) / m + 1 / 2⌋ = ⌊((q + (m / 2 : ℕ) : ℤ) : ℝ) / m⌋ ∧
      ⌈(q : ℝ) / m + 1 / 2⌉ = ⌈((q + ((m + 1) / 2 : ℕ) : ℤ) : ℝ) / m⌉ := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hshift : (q : ℝ) / m + 1 / 2 = ((q : ℝ) + (m : ℝ) / 2) / m := by
    rw [add_div, div_right_comm (m : ℝ), div_self hmR]
  have floor_div (x : ℝ) : ⌊x / m⌋ = ⌊(⌊x⌋ : ℝ) / m⌋ := by
    simp only [Int.floor_div_natCast, Int.floor_intCast]
  have ceil_div (x : ℝ) : ⌈x / m⌉ = ⌈(⌈x⌉ : ℝ) / m⌉ := by
    rw [← neg_inj, ← Int.floor_neg, ← Int.floor_neg]
    simp only [← neg_div]
    rw [floor_div (-x), Int.floor_neg, Int.cast_neg]
  have floor_half (n : ℤ) : ⌊(n : ℝ) / 2⌋ = n / 2 := by
    simpa only [Nat.cast_ofNat, Int.floor_intCast] using Int.floor_div_natCast (n : ℝ) 2
  have hf : ⌊(m : ℝ) / 2⌋ = (m / 2 : ℕ) := by
    simpa only [Int.cast_natCast, Int.natCast_ediv, Nat.cast_ofNat] using floor_half (m : ℤ)
  have hc : ⌈(m : ℝ) / 2⌉ = ((m + 1) / 2 : ℕ) := by
    rw [← neg_inj, ← Int.floor_neg, ← neg_div, ← Int.cast_natCast, ← Int.cast_neg, floor_half]
    omega
  rw [hshift]
  constructor
  · rw [floor_div, Int.floor_intCast_add, hf]
  · rw [ceil_div, Int.ceil_intCast_add, hc]

end MetaMathlibExt
