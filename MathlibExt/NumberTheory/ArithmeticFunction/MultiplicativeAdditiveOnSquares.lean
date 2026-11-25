/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Multiplicative functions additive on pairs of squares

We determine the values on squares from the value at four and deduce the power law
for all even exponents.
-/

namespace MetaMathlibExt

namespace multiplicative_additive_on_squares

/-- The values on odd and even squares are quadratic polynomials in the half-index. -/
private theorem square_values (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ m n : ℕ, 0 < m → 0 < n → f (m ^ 2 + n ^ 2) = f (m ^ 2) + f (n ^ 2)) :
    (∀ n : ℕ, f ((2 * n + 1) ^ 2) = 1 + f 4 * n * (n + 1)) ∧
      (∀ n : ℕ, f ((2 * n) ^ 2) = f 4 * n ^ 2) := by
  let g (n : ℕ) := f (n ^ 2)
  have h1 : g 1 = 1 := by simpa [g] using hf.map_one
  have h2 : f 2 = 2 := by
    simpa [hf.map_one, one_add_one_eq_two] using hadd 1 1 (by decide) (by decide)
  -- The two sums of squares differ by a factor of two, coprime to the smaller sum.
  have shift (n b : ℕ) (hb : 0 < b) :
      g (2 * n + 1 + 2 * b) + g (2 * n + 1) = 2 * (g (2 * n + 1 + b) + g b) := by
    have hcop : Nat.Coprime 2 ((2 * n + 1 + b) ^ 2 + b ^ 2) := by
      apply Nat.coprime_two_left.mpr
      exact ⟨2 * n ^ 2 + 2 * n * b + 2 * n + b + b ^ 2, by ring⟩
    dsimp only [g]
    rw [← hadd _ _ (by omega) (by omega), ← hadd _ _ (by omega) hb,
      show (2 * n + 1 + 2 * b) ^ 2 + (2 * n + 1) ^ 2 =
        2 * ((2 * n + 1 + b) ^ 2 + b ^ 2) by ring, hf.2 hcop, h2]
  -- With step two the second difference on odd squares is constant.
  have odd (n : ℕ) : g (2 * n + 1) = 1 + f 4 * n * (n + 1) := by
    induction n using Nat.twoStepInduction with
    | zero => simpa using h1
    | one =>
      have h := shift 0 1 (by decide)
      change g 3 + g 1 = 2 * (f 4 + g 1) at h
      simp only [h1] at h
      norm_num
      linear_combination h
    | more n ih₀ ih₁ =>
      have h := shift n 2 (by decide)
      rw [show 2 * n + 1 + 2 * 2 = 2 * (n + 2) + 1 by omega,
        show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by omega, ih₀, ih₁] at h
      change g (2 * (n + 2) + 1) + _ = 2 * (_ + f 4) at h
      push_cast at h ⊢
      linear_combination h
  refine ⟨odd, ?_⟩
  intro n
  cases n with
  | zero => simp
  | succ n =>
    have h := shift n 1 (by decide)
    rw [show 2 * n + 1 + 2 * 1 = 2 * (n + 1) + 1 by omega,
      show 2 * n + 1 + 1 = 2 * (n + 1) by omega, odd, odd, h1] at h
    change g (2 * (n + 1)) = f 4 * ((n + 1 : ℕ) : ℂ) ^ 2
    push_cast at h ⊢
    linear_combination -h / 2

end multiplicative_additive_on_squares

/-- **Multiplicative functions additive on pairs of squares.** Let $f$ be a complex-valued
multiplicative arithmetic function (so $f(1) = 1$ and $f(ab) = f(a) f(b)$ for coprime $a$ and
$b$) such that $f(m^2 + n^2) = f(m^2) + f(n^2)$ for all positive integers $m$ and $n$. Then
$f(4)$ is $0$ or $4$; $f(q^{2k}) = f(q^2)^k$ for all positive integers $q$ and $k$; and if
$f(4) = 4$, then $f(m^2) = m^2$ for every positive integer $m$.

The source also assumes $f \ne 0$, which follows from $f(1) = 1$.

Source: Elchin Hasanalizade, *On the k-Additive Uniqueness of Sums of Consecutive Squares
for Multiplicative Functions*, INTEGERS 25 (2025), Article A40, Theorem 1
(`integers-2025-A40-thm-1`). -/
public theorem multiplicative_additive_on_squares (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hadd : ∀ m n : ℕ, 0 < m → 0 < n → f (m ^ 2 + n ^ 2) = f (m ^ 2) + f (n ^ 2)) :
    (f 4 = 0 ∨ f 4 = 4) ∧
      (∀ q k : ℕ, 0 < q → 0 < k → f (q ^ (2 * k)) = f (q ^ 2) ^ k) ∧
      (f 4 = 4 → ∀ m : ℕ, 0 < m → f (m ^ 2) = (m : ℂ) ^ 2) := by
  obtain ⟨odd, even⟩ := multiplicative_additive_on_squares.square_values f hf hadd
  -- At 36 the even-square formula must agree with the product of the values at 4 and 9.
  have h36 := hf.2 (by decide : Nat.Coprime 4 9)
  rw [show 4 * 9 = (2 * 3) ^ 2 by decide, even,
    show 9 = (2 * 1 + 1) ^ 2 by decide, odd] at h36
  push_cast at h36
  have hroots : f 4 * (f 4 - 4) = 0 := by linear_combination -h36 / 2
  have hcases : f 4 = 0 ∨ f 4 = 4 := (mul_eq_zero.mp hroots).imp_right sub_eq_zero.mp
  have squares (h4 : f 4 = 4) (n : ℕ) : f (n ^ 2) = (n : ℂ) ^ 2 := by
    obtain ⟨r, rfl | rfl⟩ := n.even_or_odd'
    · rw [even, h4]
      push_cast
      ring
    · rw [odd, h4]
      push_cast
      ring
  refine ⟨hcases, ?_, fun h4 m _ => squares h4 m⟩
  intro q k _ hk
  rw [Nat.mul_comm, pow_mul]
  rcases hcases with h0 | h4
  · have parity (n : ℕ) : f (n ^ 2) = (n % 2 : ℕ) := by
      obtain ⟨r, rfl | rfl⟩ := n.even_or_odd'
      · simp [even, h0]
      · simp [odd, h0, Nat.add_mod]
    rw [parity, parity, Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one q with hq | hq <;> simp [hq, hk.ne']
  · rw [squares h4, squares h4, Nat.cast_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]

end MetaMathlibExt
