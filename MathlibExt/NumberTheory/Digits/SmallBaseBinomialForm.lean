/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import MathlibExt.NumberTheory.Digits.BinomialDigits
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith

/-!
# Small bases for binomial forms of powers of two

Take `x = ⌈√(2n)⌉` and `k = n / x`. If the remainder is too large for the scaled
binomial coefficients to fit in base `2^x - 1`, increase `x` by one and subtract
`k` from the remainder, keeping the same `k`.
-/

namespace MetaMathlibExt

/-- **Binomial form.** A natural number $N$ has a base-$b$ representation in binomial form if
there are natural numbers $\alpha \ge 1$ and $k \ge 1$ such that the base-$b$ digits of $N$, from
the most significant to the least significant, are
$\alpha\binom{k}{k}, \alpha\binom{k}{k-1}, \dots, \alpha\binom{k}{0}$.

The one-digit case $k = 0$ is excluded as degenerate.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Section 1
(definition of binomial form). -/
@[expose] public def HasBinomialForm (b N : ℕ) : Prop :=
  ∃ α k : ℕ, 1 ≤ α ∧ 1 ≤ k ∧ Nat.digits b N = (List.range (k + 1)).map fun i => α * k.choose i

private theorem two_le_two_pow_sub_one (x : ℕ) (hx : 2 ≤ x) : 2 ≤ 2 ^ x - 1 := by
  have h : (4 : ℕ) ≤ 2 ^ x := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hx
  omega

private theorem hasBinomialForm_of_remainder (n x k r : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k)
    (hn : n = x * k + r) (hr : r + k ≤ x) : HasBinomialForm (2 ^ x - 1) (2 ^ n) := by
  have hc : k.choose ((k + 1) / 2) ≤ 2 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    exact Nat.choose_succ_le_two_pow _ _
  have hscaled : 2 ^ r * k.choose ((k + 1) / 2) ≤ 2 ^ (x - 1) := calc
    _ ≤ 2 ^ r * 2 ^ (k - 1) := Nat.mul_le_mul_left _ hc
    _ = 2 ^ (r + (k - 1)) := (pow_add ..).symm
    _ ≤ 2 ^ (x - 1) := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega)
  have hlt : (2 : ℕ) ^ (x - 1) < 2 ^ x - 1 := by
    have hhalf : (2 : ℕ) ≤ 2 ^ (x - 1) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (show 1 ≤ x - 1 by omega)
    have hdouble : (2 : ℕ) ^ x = 2 ^ (x - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ x)]
    omega
  have hα : 1 ≤ (2 : ℕ) ^ r := pow_pos (by decide : 0 < (2 : ℕ)) r
  have hdigits := digits_mul_one_add_pow (2 ^ r) k (2 ^ x - 1) hα (hscaled.trans_lt hlt)
  have hbase : 1 + (2 ^ x - 1 : ℕ) = 2 ^ x := by
    have := two_le_two_pow_sub_one x hx
    omega
  rw [hbase, ← pow_mul, ← pow_add, Nat.add_comm r, ← hn] at hdigits
  exact ⟨2 ^ r, k, hα, hk, hdigits⟩

/-- **Powers of 2 have binomial forms in small bases.** For every natural number $n \ge 2$ there
are natural numbers $y$ and $b$ with $y \le \lceil \sqrt{2n} \rceil + 1$ and $2 \le b \le 2^y - 1$
such that $2^n$ has a base-$b$ representation in binomial form.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 5
(`integers-2024-A69-thm-5`). -/
public theorem exists_small_base_binomialForm_two_pow (n : ℕ) (hn : 2 ≤ n) :
    ∃ y b : ℕ, y ≤ ⌈Real.sqrt (2 * n)⌉₊ + 1 ∧ 2 ≤ b ∧ b ≤ 2 ^ y - 1 ∧
      HasBinomialForm b (2 ^ n) := by
  let x := ⌈Real.sqrt (2 * n)⌉₊
  have hx_sq : 2 * n ≤ x ^ 2 := by
    have hsqrt : Real.sqrt (2 * n) ≤ (x : ℝ) := Nat.le_ceil _
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
    rw [Real.sq_sqrt (by positivity)] at hsq
    exact_mod_cast hsq
  have hx : 2 ≤ x := by
    by_contra! h
    have hx1 : x ^ 2 ≤ 1 := by simpa using (Nat.pow_le_pow_left (show x ≤ 1 by omega) 2)
    omega
  have hxn : x ≤ n := by
    apply Nat.ceil_le.mpr
    apply (Real.sqrt_le_iff).2
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact ⟨by positivity, by nlinarith [mul_nonneg (sub_nonneg.mpr hn') (Nat.cast_nonneg n)]⟩
  let k := n / x
  let r := n % x
  have hx_pos : 0 < x := by omega
  have hk : 1 ≤ k := by
    simpa [k] using (Nat.le_div_iff_mul_le hx_pos).2 (show 1 * x ≤ n by simpa using hxn)
  have hrx : r < x := Nat.mod_lt _ hx_pos
  have hnr : n = x * k + r := by simpa [k, r, Nat.add_comm] using (Nat.mod_add_div n x).symm
  have htwok : 2 * k ≤ x := by
    apply (mul_le_mul_iff_right₀ hx_pos).mp
    calc
      x * (2 * k) = 2 * (x * k) := by ac_rfl
      _ ≤ 2 * n := Nat.mul_le_mul_left _ (by omega)
      _ ≤ x * x := by simpa [pow_two] using hx_sq
  by_cases h : r + k ≤ x
  · exact ⟨x, 2 ^ x - 1, by omega, two_le_two_pow_sub_one x hx, le_rfl,
      hasBinomialForm_of_remainder n x k r hx hk hnr h⟩
  · have hrk : k ≤ r := by omega
    have hn' : n = (x + 1) * k + (r - k) := by rw [Nat.add_mul]; omega
    have hy : 2 ≤ x + 1 := by omega
    exact ⟨x + 1, 2 ^ (x + 1) - 1, le_rfl, two_le_two_pow_sub_one _ hy, le_rfl,
      hasBinomialForm_of_remainder n (x + 1) k (r - k) hy hk hn' (by omega)⟩

end MetaMathlibExt
