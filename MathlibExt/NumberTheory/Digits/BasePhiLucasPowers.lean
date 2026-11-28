/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution
import MathlibExt.NumberTheory.Digits.BasePhiConjugate
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Lucas numbers and powers of the golden ratio

Binet's formula bounds the golden-ratio power at an odd index between the corresponding Lucas
number and that number plus one. At a positive even index, the power lies between the Lucas number
minus one and the Lucas number itself. At every even index, including zero, the Lucas number is the
sum of the golden-ratio powers at that index and its negative.

## References

* Michel Dekking and Ad van Loon, *Counting Base Phi Representations*, The Fibonacci Quarterly
  62 (2024), no. 2, 112–124, Section 4, Example 3, for the even-index identity.
* The bounds use `cb_lucas_binet` from `MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution`.
-/

open scoped goldenRatio

namespace MetaMathlibExt.BasePhiLucasPowers

open BasePhiConjugate

private theorem psi_even_pow_pos (k : ℕ) : (0 : ℝ) < ψ ^ (2 * k) := by
  have hψ2 : (0 : ℝ) < ψ ^ 2 := by
    rw [pow_two]
    exact mul_pos_of_neg_of_neg Real.goldenConj_neg Real.goldenConj_neg
  calc (0 : ℝ) < (ψ ^ 2) ^ k := pow_pos hψ2 k
    _ = ψ ^ (2 * k) := by rw [← pow_mul]

/-- The Lucas number at any even index is strictly greater than the golden ratio raised to
that index. -/
public lemma lucas_even_gt (k : ℕ) :
    φ ^ ((2 * k : ℕ) : ℤ) < (lucasNumber (2 * k) : ℝ) := by
  rw [← cb_lucas_binet]
  simp only [zpow_natCast]
  have hψ := psi_even_pow_pos k
  linarith

/-- The Lucas number at any odd index is strictly smaller than the golden ratio raised to
that index. -/
public lemma lucas_odd_lt (k : ℕ) :
    (lucasNumber (2 * k + 1) : ℝ) < φ ^ ((2 * k + 1 : ℕ) : ℤ) := by
  rw [← cb_lucas_binet]
  simp only [zpow_natCast]
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hψr : ψ = -(-ψ) := by ring
  have hpos : (0 : ℝ) < -ψ := by linarith [Real.goldenConj_neg]
  have h2 : ψ ^ (2 * k + 1) = -((-ψ) ^ (2 * k + 1)) := by
    conv_lhs => rw [hψr]
    exact hodd.neg_pow (-ψ)
  have h1 : (0 : ℝ) < (-ψ) ^ (2 * k + 1) := pow_pos hpos _
  linarith

/-- The golden ratio raised to any odd index is strictly less than one plus the Lucas number
at that index. -/
public lemma lucas_odd_add_one_gt (k : ℕ) :
    φ ^ ((2 * k + 1 : ℕ) : ℤ) < (lucasNumber (2 * k + 1) : ℝ) + 1 := by
  rw [← cb_lucas_binet]
  simp only [zpow_natCast]
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hψr : ψ = -(-ψ) := by ring
  have hr0 : (0 : ℝ) ≤ -ψ := le_of_lt (by linarith [Real.goldenConj_neg])
  have hr1 : -ψ < 1 := by linarith [Real.neg_one_lt_goldenConj]
  have h1 : (-ψ) ^ (2 * k + 1) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
  have h2 : ψ ^ (2 * k + 1) = -((-ψ) ^ (2 * k + 1)) := by
    conv_lhs => rw [hψr]
    exact hodd.neg_pow (-ψ)
  linarith

/-- At a positive even index, the Lucas number minus one is strictly less than the golden ratio
raised to that index. -/
public lemma lucas_even_sub_one_lt (k : ℕ) :
    (lucasNumber (2 * k + 2) : ℝ) - 1 < φ ^ ((2 * k + 2 : ℕ) : ℤ) := by
  rw [← cb_lucas_binet]
  simp only [zpow_natCast]
  have hev : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  have hψr : ψ = -(-ψ) := by ring
  have hr0 : (0 : ℝ) ≤ -ψ := le_of_lt (by linarith [Real.goldenConj_neg])
  have hr1 : -ψ < 1 := by linarith [Real.neg_one_lt_goldenConj]
  have h1 : (-ψ) ^ (2 * k + 2) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
  have h2 : ψ ^ (2 * k + 2) = (-ψ) ^ (2 * k + 2) := by
    conv_lhs => rw [hψr]
    exact hev.neg_pow (-ψ)
  linarith

/-- The golden-ratio powers at positions $2n$ and $-2n$ sum to the Lucas number $L_{2n}$,
including $n = 0$. -/
public lemma pair_value (n : ℕ) :
    φ ^ (2 * (n : ℤ)) + φ ^ (-(2 * (n : ℤ))) = (lucasNumber (2 * n) : ℝ) := by
  have hcast : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  have hev : Even (2 * (n : ℤ)) := by
    use (n : ℤ)
    ring
  rw [← cb_lucas_binet, ← zpow_natCast φ, ← zpow_natCast ψ, hcast]
  congr 1
  exact (even_pow_eq hev).symm

end MetaMathlibExt.BasePhiLucasPowers
