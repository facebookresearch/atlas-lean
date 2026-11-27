/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.JacobsthalLucasNumber
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Cauchy convolutions with Oresme numbers

Cauchy convolutions `∑_{k=0}^n a_k O_{n-k}` of the Oresme numbers `O_n = n/2^n` with
second-order sequences, and congruences read off from them, following M. R. Bacon and
C. K. Cook. The Oresme numbers are written inline as `n / 2^n` over `ℚ`, the Lucas numbers
`L_0 = 2, L_1 = 1` are `lucasNumber`, and the Jacobsthal–Lucas numbers `j_0 = 2, j_1 = 1` are
`jacobsthalLucasNumber`.
-/

namespace MetaMathlibExt

/-- **Self-convolution of the Oresme numbers.** Let $O_m = m/2^m$ denote the Oresme numbers. For
every natural number $n$, $\sum_{k=0}^{n} O_k O_{n-k} = \frac{(n+1) n (n-1)}{6 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 2.1 (`fq-2024-cookbacon061124-prop-2.1`). -/
public theorem oresme_convolution_self (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℚ) / 2 ^ k) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      ((n : ℚ) + 1) * n * ((n : ℚ) - 1) / (6 * 2 ^ n) := by
  -- A discrete antiderivative of the numerator k(n-k).
  let F (k : ℕ) : ℚ := k * ((k : ℚ) - 1) * (3 * n + 1 - 2 * k) / 6
  calc
    _ = ∑ k ∈ Finset.range (n + 1), (F (k + 1) - F k) / 2 ^ n := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hkn, Nat.cast_sub hkn]
      congr 1
      simp only [F, Nat.cast_add, Nat.cast_one]
      ring
    _ = (F (n + 1) - F 0) / 2 ^ n := by rw [← Finset.sum_div, Finset.sum_range_sub]
    _ = _ := by
      simp [F]
      field_simp
      ring

/-- **Fibonacci–Oresme convolution.** Let $F_m$ denote the Fibonacci numbers, with $F_0 = 0$,
$F_1 = 1$ and $F_{m+2} = F_{m+1} + F_m$, and let $O_m = m/2^m$ denote the Oresme numbers. For
every natural number $n$,
$\sum_{k=0}^{n} F_k O_{n-k} = \frac{2}{5} F_{n+1} - \frac{2(n+1)}{5 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 4.1 (`fq-2024-cookbacon061124-prop-4.1`). -/
public theorem fib_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Nat.fib k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 5 * (Nat.fib (n + 1) : ℚ) - 2 * ((n : ℚ) + 1) / (5 * 2 ^ n) := by
  let O (m : ℕ) : ℚ := m / 2 ^ m
  let S (m : ℕ) := ∑ k ∈ Finset.range (m + 1), (Nat.fib k : ℚ) * O (m - k)
  have shift (m : ℕ) :
      S (m + 1) = ∑ k ∈ Finset.range (m + 1), (Nat.fib (k + 1) : ℚ) * O (m - k) := by
    dsimp only [S]
    rw [Finset.sum_range_succ']
    simp
  have step (m : ℕ) : S (m + 2) = S m + S (m + 1) + O (m + 1) := by
    rw [shift (m + 1), Finset.sum_range_succ', shift m]
    simp [S, Nat.fib_add_two, add_mul, Finset.sum_add_distrib]
  change S n = _
  induction n using Nat.twoStepInduction with
  | zero => norm_num [S, O]
  | one => norm_num [S, O, Finset.sum_range_succ]
  | more n ih₀ ih₁ =>
    rw [step, ih₀, ih₁, Nat.fib_add_two (n := n + 1)]
    simp only [O, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    field_simp
    ring

/-- **Oresme–Fibonacci congruence modulo 5.** Let $F_n$ denote the Fibonacci numbers, with
$F_0 = 0$ and $F_1 = 1$. For every natural number $n$, $2^{n-1} F_n \equiv n \pmod 5$, where at
$n = 0$ the exponent $n - 1$ is taken to be $0$ (both sides are then $0$).

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 4.2 (`fq-2024-cookbacon061124-cor-4.2`). -/
public theorem two_pow_pred_mul_fib_modEq_five (n : ℕ) :
    2 ^ (n - 1) * Nat.fib n ≡ n [MOD 5] := by
  obtain _ | n := n
  · decide
  change 2 ^ n * Nat.fib (n + 1) ≡ n + 1 [MOD 5]
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih₀ ih₁ =>
    calc
      2 ^ (n + 2) * Nat.fib (n + 3) =
          4 * (2 ^ n * Nat.fib (n + 1)) + 2 * (2 ^ (n + 1) * Nat.fib (n + 2)) := by
            rw [Nat.fib_add_two (n := n + 1)]
            simp only [pow_succ]
            ring
      _ ≡ 4 * (n + 1) + 2 * (n + 2) [MOD 5] := (ih₀.mul_left 4).add (ih₁.mul_left 2)
      _ ≡ n + 3 [MOD 5] := by unfold Nat.ModEq; omega

/-- **Lucas–Oresme convolution.** Let $L_m$ denote the Lucas numbers and let $O_m = m/2^m$
denote the Oresme numbers. For every natural number $n$,
$\sum_{k=0}^{n} L_k O_{n-k} = \frac{2}{5} L_{n+1} - \frac{2}{5 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 4.3 (`fq-2024-cookbacon061124-prop-4.3`). -/
public theorem lucasNumber_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (lucasNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 5 * (lucasNumber (n + 1) : ℚ) - 2 / (5 * 2 ^ n) := by
  let O (m : ℕ) : ℚ := m / 2 ^ m
  let S (m : ℕ) := ∑ k ∈ Finset.range (m + 1), (lucasNumber k : ℚ) * O (m - k)
  -- Peeling off the term `L₀ O_{m+1} = 2 O_{m+1}` shifts the Lucas index.
  have shift (m : ℕ) :
      S (m + 1) =
        ∑ k ∈ Finset.range (m + 1), (lucasNumber (k + 1) : ℚ) * O (m - k) + 2 * O (m + 1) := by
    dsimp only [S]
    rw [Finset.sum_range_succ']
    simp [lucasNumber]
  -- The convolution satisfies the Lucas recurrence up to the term `2 O_{m+2} - O_{m+1}`.
  have step (m : ℕ) : S (m + 2) = S (m + 1) + S m + (2 * O (m + 2) - O (m + 1)) := by
    rw [shift (m + 1), Finset.sum_range_succ', shift m]
    simp [S, lucasNumber, add_mul, Finset.sum_add_distrib]
    ring
  change S n = _
  induction n using Nat.twoStepInduction with
  | zero => norm_num [S, O, lucasNumber]
  | one => norm_num [S, O, Finset.sum_range_succ, lucasNumber]
  | more n ih₀ ih₁ =>
    rw [step, ih₀, ih₁]
    simp only [O, lucasNumber, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    field_simp
    ring

/-- **Pell–Oresme convolution.** Let $P_m$ denote the Pell numbers and let $O_m = m/2^m$ denote
the Oresme numbers. For every natural number $n$,
$\sum_{k=0}^{n} P_k O_{n-k} = \frac{2}{49}(5 P_{n+1} - 4 P_n) - \frac{2(7n + 5)}{49 \cdot 2^n}$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 5.2 (`fq-2024-cookbacon061124-prop-5.2`). -/
public theorem pellNumber_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (pellNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 49 * (5 * (pellNumber (n + 1) : ℚ) - 4 * pellNumber n) -
        2 / 49 * ((7 * (n : ℚ) + 5) / 2 ^ n) := by
  let O (m : ℕ) : ℚ := m / 2 ^ m
  let S (m : ℕ) := ∑ k ∈ Finset.range (m + 1), (pellNumber k : ℚ) * O (m - k)
  -- The initial term vanishes because `pellNumber 0 = 0`.
  have shift (m : ℕ) :
      S (m + 1) = ∑ k ∈ Finset.range (m + 1), (pellNumber (k + 1) : ℚ) * O (m - k) := by
    dsimp only [S]
    rw [Finset.sum_range_succ']
    simp [pellNumber]
  -- The convolution follows the Pell recurrence with an extra `O (m + 1)` from `pellNumber 1`.
  have step (m : ℕ) : S (m + 2) = 2 * S (m + 1) + S m + O (m + 1) := by
    rw [shift (m + 1), Finset.sum_range_succ', shift m]
    simp [S, pellNumber, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  change S n = _
  induction n using Nat.twoStepInduction with
  | zero => norm_num [S, O, pellNumber]
  | one => norm_num [S, O, pellNumber, Finset.sum_range_succ]
  | more n ih₀ ih₁ =>
    rw [step, ih₀, ih₁]
    simp only [O, pellNumber, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    field_simp
    ring

/-- **Jacobsthal–Lucas–Oresme convolution.** Let $j_m$ denote the Jacobsthal–Lucas numbers and
let $O_m = m/2^m$ denote the Oresme numbers. For every natural number $n$,
$\sum_{k=0}^{n} j_k O_{n-k} = \frac{2}{9} j_{n+1} - \frac{2}{9 \cdot 2^n}$.

The paper prints $+$ where the equality sign belongs, with no relation between the two sides;
this is the equality reading, which matches Propositions 4.3 and 6.2 and Corollary 6.5.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Proposition 6.4 (`fq-2024-cookbacon061124-prop-6.4`). -/
public theorem jacobsthalLucasNumber_oresme_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (jacobsthalLucasNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 / 9 * (jacobsthalLucasNumber (n + 1) : ℚ) - 2 / (9 * 2 ^ n) := by
  let O (m : ℕ) : ℚ := m / 2 ^ m
  let S (m : ℕ) := ∑ k ∈ Finset.range (m + 1), (jacobsthalLucasNumber k : ℚ) * O (m - k)
  have shift (m : ℕ) :
      S (m + 1) =
        ∑ k ∈ Finset.range (m + 1), (jacobsthalLucasNumber (k + 1) : ℚ) * O (m - k) +
          2 * O (m + 1) := by
    dsimp only [S]
    rw [Finset.sum_range_succ']
    simp [jacobsthalLucasNumber]
  have step (m : ℕ) : S (m + 2) = S (m + 1) + 2 * S m + (2 * O (m + 2) - O (m + 1)) := by
    rw [shift (m + 1), Finset.sum_range_succ', shift m]
    simp [S, jacobsthalLucasNumber, two_mul, add_mul, Finset.sum_add_distrib]
    ring
  change S n = _
  induction n using Nat.twoStepInduction with
  | zero => norm_num [S, O, jacobsthalLucasNumber]
  | one => norm_num [S, O, Finset.sum_range_succ, jacobsthalLucasNumber]
  | more n ih₀ ih₁ =>
    rw [step, ih₀, ih₁]
    simp only [O, jacobsthalLucasNumber, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one, pow_succ]
    field_simp
    ring

/-- **Oresme–Pell–Lucas congruence modulo 49.** Let $Q_n$ denote the Pell–Lucas numbers, with
$Q_0 = Q_1 = 1$. For every natural number $n$,
$2^{n+1} (5 Q_{n+1} - 4 Q_n) \equiv 2 - 7n \pmod{49}$ as integers.

The paper prints $2^{n+1}(5Q_{n+1} - 4Q_n) \equiv 2 - 7n \equiv 0$. Its proof (base values $2$ and
$44$ on both sides, inductive hypothesis $2^{n+1}(5Q_{n+1} - 4Q_n) - (2 - 7n) \equiv 0$)
establishes the single congruence above, while the second link $2 - 7n \equiv 0 \pmod{49}$ fails
at $n = 0$.

Source: Michael R. Bacon and Charles K. Cook, *Some Properties of Oresme Numbers and
Convolutions with Various Second Order Sequences*, The Fibonacci Quarterly 62 (2024), no. 3,
Article cookbacon061124, Corollary 5.5 (`fq-2024-cookbacon061124-cor-5.5`). -/
public theorem two_pow_succ_mul_pellLucasSequence_combination_modEq (n : ℕ) :
    2 ^ (n + 1) * (5 * (pellLucasSequence (n + 1) : ℤ) - 4 * pellLucasSequence n) ≡
      2 - 7 * n [ZMOD 49] := by
  let A (k : ℕ) : ℤ :=
    2 ^ (k + 1) * (5 * (pellLucasSequence (k + 1) : ℤ) - 4 * pellLucasSequence k)
  have step (k : ℕ) : A (k + 2) = 4 * (A (k + 1) + A k) := by
    dsimp only [A]
    rw [pellLucasSequence_succ_succ (k + 1), pellLucasSequence_succ_succ k]
    push_cast
    simp only [pow_succ]
    ring
  change A n ≡ _ [ZMOD 49]
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih₀ ih₁ =>
    rw [step]
    refine ((ih₁.add ih₀).mul_left 4).trans ?_
    -- The linear residues satisfy the same recurrence up to a difference of `49 * n`.
    refine Int.modEq_iff_dvd.mpr ⟨(n : ℤ), ?_⟩
    push_cast
    ring

end MetaMathlibExt
