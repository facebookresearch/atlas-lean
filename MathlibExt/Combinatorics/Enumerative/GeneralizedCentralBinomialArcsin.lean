/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Zurita's polynomials for reciprocal central binomial series

The coefficient recurrences define Zurita's polynomials and constants.
`hasDerivAt_zurita_antiderivative_one` proves the first arcsine antiderivative and
`hasDerivAt_zurita_antiderivative_two` proves the second on $(0,1)$.

## References

- Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
  Coefficients*, INTEGERS 26 (2026), Article A2, pp. 1–21, Definitions 1–4 and Lemmas 1–2.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Coefficients of Zurita's polynomial $S_n$.** For a natural number $n$, the rational numbers
$s_0, s_1, s_2, \dots$ are defined by $s_0 = 1/(1/2 - n)$ and
$s_k = \frac{k - 1 - n}{k - n + 1/2}\, s_{k-1}$ for every $k \ge 1$. Their first $n + 1$ terms are
the coefficients of $S_n(x) = \sum_{k=0}^{n} s_k x^k$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 1. -/
def zuritaSCoeff (n : ℕ) : ℕ → ℚ
  | 0 => 1 / (1 / 2 - n)
  | k + 1 => ((k : ℚ) - n) / ((k : ℚ) + 1 - n + 1 / 2) * zuritaSCoeff n k

/-- **Zurita's constant $c_n$.** For a natural number $n$, let $s_n$ be the coefficient of $x^n$
in Zurita's polynomial $S_n(x) = \sum_{k=0}^n s_k x^k$. Then $c_n$ is the rational number
$s_n/2 - 1$. For $n = 1$ this gives $c_1 = 1$, the paper's convention.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
def zuritaC (n : ℕ) : ℚ :=
  zuritaSCoeff n n / 2 - 1

/-- **Reversed coefficients of Zurita's polynomial $T_{n-2}$.** Fix a natural number $n$, let
$s_0, s_1, \dots$ be the coefficients of $S_n$ and let $c_n = s_n/2 - 1$. The rational numbers
$u_0, u_1, \dots$ are defined by $u_0 = -s_{n-1}/2 - c_n$ and
$u_{i+1} = \frac{(k + 1 - n)\, u_i + s_k/2}{k - n}$ with $k = n - 2 - i$, where the index
subtractions $n - 1$ and $n - 2 - i$ are truncated at $0$. For $n \ge 2$ they list the
coefficients of $T_{n-2}$ backwards, $t_{n-2-i} = u_i$ for $0 \le i \le n - 2$; thus
$t_{n-2} = -s_{n-1}/2 - c_n$ and $t_{k-1} = ((k + 1 - n) t_k + s_k/2)/(k - n)$ for
$k = n - 2, \dots, 1$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
def zuritaTCoeffRev (n : ℕ) : ℕ → ℚ
  | 0 => -zuritaSCoeff n (n - 1) / 2 - zuritaC n
  | i + 1 => ((((n - 2 - i : ℕ) : ℚ) + 1 - n) * zuritaTCoeffRev n i +
      zuritaSCoeff n (n - 2 - i) / 2) / (((n - 2 - i : ℕ) : ℚ) - n)

/-- **Coefficients of Zurita's polynomial $T_{n-2}$.** For natural numbers $n$ and $k$,
$t_k = u_{n-2-k}$, where $n - 2 - k$ is truncated at $0$ and $u_0, u_1, \dots$ are the reversed
coefficients of $T_{n-2}$: with $s_j$ the coefficients of $S_n$ and $c_n = s_n/2 - 1$,
$u_0 = -s_{n-1}/2 - c_n$ and $u_{i+1} = ((m + 1 - n) u_i + s_m/2)/(m - n)$ for
$m = n - 2 - i$, the indices $n - 1$ and $n - 2 - i$ being truncated at $0$. For $k \le n - 2$
these are the coefficients of $T_{n-2}(x) = \sum_{k=0}^{n-2} t_k x^k$; for $k > n - 2$,
$t_k = u_0$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
def zuritaTCoeff (n k : ℕ) : ℚ :=
  zuritaTCoeffRev n (n - 2 - k)

/-- **Zurita's coefficients $m_k$.** For a natural number $n$, the rational numbers
$m_0, m_1, \dots$ are defined by $m_0 = 2/(2n - 1)$ and
$m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for $k \ge 1$. Zurita's polynomial $M_{n-1}$ is
$M_{n-1}(x) = \sum_{k=0}^{n-1} m_k x^k$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 3. -/
def zuritaMCoeff (n : ℕ) : ℕ → ℚ
  | 0 => 2 / (2 * n - 1)
  | k + 1 => 2 * ((k : ℚ) + 1 - n) / (2 * ((k : ℚ) + 1) - 2 * n + 1) * zuritaMCoeff n k

/-- **Zurita's constant $d_n$.** For a natural number $n$, let $m_0, m_1, \dots$ be Zurita's
coefficients, given by $m_0 = 2/(2n - 1)$ and $m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for
$k \ge 1$, so that $M_{n-1}(x) = \sum_{k=0}^{n-1} m_k x^k$ for $n \ge 1$. Then $d_n$ is the
rational number $m_{n-1}/2$ for $n \ge 1$, and $d_0 = m_0/2 = -1$. For $n = 1$ this gives
$d_1 = 1$, the paper's convention.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 4. -/
def zuritaD (n : ℕ) : ℚ :=
  zuritaMCoeff n (n - 1) / 2

/-- **Coefficients of Zurita's polynomial $N_{n-2}$.** For natural numbers $n$ and $k$, let $m_k$
be Zurita's coefficient, given by $m_0 = 2/(2n - 1)$ and
$m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for $k \ge 1$. This is the rational number
$m_k / (2(k - n + 1))$, taken to be $0$ when $k = n - 1$. For $k \le n - 2$ it is the
coefficient of $x^k$ in $N_{n-2}(x) = \frac12 \sum_{i=0}^{n-2} \frac{m_i x^i}{i - n + 1}$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 4. -/
def zuritaNCoeff (n k : ℕ) : ℚ :=
  zuritaMCoeff n k / 2 / ((k : ℚ) - n + 1)

/-- **Values from Zurita's Tables 1-4.** For $n = 2$ the coefficients $s_0, s_1, s_2$ of $S_2$ are
$-2/3$, $-8/3$ and $16/3$, and the constants $c_2$ and $c_4$ equal $5/3$ and $93/35$. For $n = 3$
the coefficients $t_0, t_1$ of $T_1$ are $-1/10$ and $-3/5$, the coefficients $m_0, m_1, m_2$ of
$M_2$ are $2/5$, $8/15$ and $16/15$, the constant $d_3$ equals $8/15$, and the coefficients of
$x^0$ and $x^1$ in $N_1$ are $-3/30$ and $-8/30$.

In polynomial form: $S_2(x) = -2/3 - (8/3)x + (16/3)x^2$, $T_1(x) = -1/10 - (3/5)x$,
$M_2(x) = 2/5 + (8/15)x + (16/15)x^2$ and $N_1(x) = -(8x + 3)/30$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Tables 1-4. -/
theorem zurita_table_values :
    (List.range 3).map (zuritaSCoeff 2) = [-2 / 3, -8 / 3, 16 / 3] ∧ zuritaC 2 = 5 / 3 ∧
      zuritaC 4 = 93 / 35 ∧ (List.range 2).map (zuritaTCoeff 3) = [-1 / 10, -3 / 5] ∧
      (List.range 3).map (zuritaMCoeff 3) = [2 / 5, 8 / 15, 16 / 15] ∧ zuritaD 3 = 8 / 15 ∧
      (List.range 2).map (zuritaNCoeff 3) = [-3 / 30, -8 / 30] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, zuritaC, zuritaD, zuritaTCoeff, zuritaNCoeff]
  norm_num [zuritaSCoeff, zuritaTCoeffRev, zuritaMCoeff, zuritaC]

/-- **Zurita's polynomial $S_n$.** For a natural number $n$ and a real number $x$,
$S_n(x) = \sum_{k=0}^{n} s_k x^k$, where $s_0 = 1/(1/2 - n)$ and
$s_k = \frac{k - 1 - n}{k - n + 1/2}\, s_{k-1}$ for $k \ge 1$ are the coefficients of $S_n$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 1. -/
noncomputable def zuritaS (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (zuritaSCoeff n k : ℝ) * x ^ k

/-- **Zurita's polynomial $T_{n-2}$.** For a natural number $n$ and a real number $x$,
$T_{n-2}(x) = \sum_{k=0}^{n-2} t_k x^k$, where $t_0, t_1, \dots$ are the coefficients of
Zurita's polynomial $T_{n-2}$; for $n \le 1$ the sum is empty and $T_{n-2}(x) = 0$. For
$n \ge 2$ these coefficients are given by $t_{n-2} = -s_{n-1}/2 - c_n$ and
$t_{k-1} = ((k + 1 - n) t_k + s_k/2)/(k - n)$ for $k = n - 2, \dots, 1$, where
$s_0 = 1/(1/2 - n)$ and $s_k = \frac{k - 1 - n}{k - n + 1/2}\, s_{k-1}$ for $k \ge 1$ are the
coefficients of Zurita's polynomial $S_n$, and $c_n = s_n/2 - 1$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
noncomputable def zuritaT (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n - 1), (zuritaTCoeff n k : ℝ) * x ^ k

/-- **Zurita's polynomial $M_{n-1}$.** For a natural number $n$, let $m_0, m_1, \dots$ be Zurita's
coefficients, given by $m_0 = 2/(2n - 1)$ and $m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for
$k \ge 1$. Then $M_{n-1}$ is the real polynomial function
$M_{n-1}(x) = \sum_{k=0}^{n-1} m_k x^k$ (so $M_{-1} = 0$).

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 3. -/
noncomputable def zuritaM (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, (zuritaMCoeff n k : ℝ) * x ^ k

/-- Evaluation of $M_{n-1}$ as the finite sum of its first $n$ terms. -/
theorem zuritaM_eq_sum_range (n : ℕ) (x : ℝ) :
    zuritaM n x = ∑ k ∈ range n, (zuritaMCoeff n k : ℝ) * x ^ k := rfl

/-- **Zurita's polynomial $N_{n-2}$.** For a natural number $n$, let $m_0, m_1, \dots$ be Zurita's
coefficients, given by $m_0 = 2/(2n - 1)$ and $m_k = \frac{2(k - n)}{2k - 2n + 1}\, m_{k-1}$ for
$k \ge 1$. Then $N_{n-2}$ is the real polynomial function
$N_{n-2}(x) = \frac12 \sum_{k=0}^{n-2} \frac{m_k x^k}{k - n + 1}$, which is $0$ for $n \le 1$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 4. -/
noncomputable def zuritaN (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n - 1), (zuritaNCoeff n k : ℝ) * x ^ k

namespace ZuritaAntiderivative

-- The coefficients of x P'(x) - n P(x) are (k - n) times those of P.
private noncomputable def weightedSum (a : ℕ → ℚ) (l n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range l, ((k : ℝ) - n) * (a k : ℝ) * x ^ k

private theorem s_step (n k : ℕ) :
    ((k : ℝ) + 1 - n + 1 / 2) * (zuritaSCoeff n (k + 1) : ℝ) =
      ((k : ℝ) - n) * (zuritaSCoeff n k : ℝ) := by
  have h : (k : ℝ) + 1 - n + 1 / 2 ≠ 0 := by
    rcases le_or_gt n (k + 1) with hk | hk
    · have := (Nat.cast_le (α := ℝ)).mpr hk
      push_cast at this
      linarith
    · have := (Nat.cast_le (α := ℝ)).mpr (show k + 2 ≤ n by omega)
      push_cast at this
      linarith
  rw [zuritaSCoeff]
  push_cast
  rw [← mul_assoc, mul_div_cancel₀ _ h]

private theorem s_zero (n : ℕ) : (1 / 2 - (n : ℝ)) * (zuritaSCoeff n 0 : ℝ) = 1 := by
  have h : 1 / 2 - (n : ℝ) ≠ 0 := by
    cases n with
    | zero => norm_num
    | succ n => push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [zuritaSCoeff]
  push_cast
  exact mul_one_div_cancel h

-- Summing the coefficient recurrence leaves just the constant and the last term.
private theorem s_identity (n : ℕ) (x : ℝ) :
    zuritaS n x / 2 + (1 - x) * weightedSum (zuritaSCoeff n) (n + 1) n x = 1 := by
  have partial_sum (l : ℕ) :
      (∑ k ∈ range (l + 1), (zuritaSCoeff n k : ℝ) * x ^ k) / 2 +
        (1 - x) * weightedSum (zuritaSCoeff n) (l + 1) n x =
          1 - ((l : ℝ) - n) * (zuritaSCoeff n l : ℝ) * x ^ (l + 1) := by
    induction l with
    | zero =>
      simp [weightedSum]
      linarith only [s_zero n]
    | succ l ih =>
      unfold weightedSum at *
      rw [sum_range_succ, sum_range_succ (f := fun k =>
        ((k : ℝ) - n) * (zuritaSCoeff n k : ℝ) * x ^ k)]
      push_cast
      rw [pow_succ x (l + 1)]
      linear_combination ih + x ^ (l + 1) * s_step n l
  simpa [zuritaS] using partial_sum n

private theorem c_eq (m : ℕ) : (zuritaC (m + 1) : ℝ) =
    -(zuritaSCoeff (m + 1) m : ℝ) - 1 := by
  unfold zuritaC
  push_cast
  have h := s_step (m + 1) m
  push_cast at h
  linarith

-- Solve the recurrence for (k + 1 - n) tₖ, working down from k = n - 2.
private theorem t_weight (m i k : ℕ) (hk : k + i = m) :
    ((k : ℝ) - (m + 1)) * (zuritaTCoeffRev (m + 2) i : ℝ) =
      ((k : ℝ) - (m + 2)) * (zuritaSCoeff (m + 2) k : ℝ) - 1 := by
  induction i generalizing k with
  | zero =>
    simp only [Nat.add_zero] at hk
    subst k
    rw [zuritaTCoeffRev]
    push_cast
    have hc := c_eq (m + 1)
    have hs := s_step (m + 2) m
    push_cast at hs
    linear_combination hc + hs
  | succ i ih =>
    have h := ih (k + 1) (by omega)
    have hs := s_step (m + 2) k
    rw [zuritaTCoeffRev, show m + 2 - 2 - i = k + 1 by omega]
    push_cast at *
    have hkm : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
    rw [show (k : ℝ) - (m + 1) = (k : ℝ) + 1 - (m + 2) by ring,
      mul_div_cancel₀ _ (by linarith)]
    linear_combination h + hs

private theorem t_identity (m : ℕ) (x : ℝ) :
    (1 - x) * (weightedSum (zuritaTCoeff (m + 1)) m m x + (zuritaC (m + 1) : ℝ) * x ^ m) +
      zuritaS (m + 1) x / 2 = x ^ (m + 1) := by
  have hcoeff (k : ℕ) (hk : k ∈ range m) :
      ((k : ℝ) - m) * (zuritaTCoeff (m + 1) k : ℝ) =
        ((k : ℝ) - (m + 1)) * (zuritaSCoeff (m + 1) k : ℝ) - 1 := by
    obtain _ | m := m
    · simp at hk
    have hk' := mem_range.mp hk
    simpa [zuritaTCoeff, add_assoc, one_add_one_eq_two] using t_weight m (m - k) k (by omega)
  have hsum :
      weightedSum (zuritaTCoeff (m + 1)) m m x + (zuritaC (m + 1) : ℝ) * x ^ m =
        weightedSum (zuritaSCoeff (m + 1)) (m + 1 + 1) (m + 1) x -
          ∑ k ∈ range (m + 1), x ^ k := by
    unfold weightedSum
    rw [sum_range_succ (n := m + 1)]
    simp only [sub_self, zero_mul, add_zero]
    rw [sum_range_succ (n := m), sum_range_succ (f := fun k => x ^ k)]
    push_cast
    rw [c_eq]
    have h := sum_congr rfl fun k hk => congrArg (· * x ^ k) (hcoeff k hk)
    simp only [sub_mul, one_mul, sum_sub_distrib] at h ⊢
    linarith only [h]
  rw [hsum, mul_sub, mul_neg_geom_sum]
  linarith only [s_identity (m + 1) x]

private theorem quotient_deriv (a : ℕ → ℚ) (l n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => (∑ k ∈ range l, (a k : ℝ) * y ^ k) / y ^ n)
      (weightedSum a l n x / x ^ (n + 1)) x := by
  have hpow (k : ℕ) : HasDerivAt (fun y : ℝ => y ^ k) ((k : ℝ) * x ^ k / x) x := by
    apply (hasDerivAt_pow k x).congr_deriv
    cases k <;> simp [pow_succ, ← mul_assoc, hx]
  simp_rw [weightedSum, sum_div]
  apply HasDerivAt.fun_sum
  intro k _
  apply (((hpow k).const_mul (a k : ℝ)).fun_div (hpow n) (pow_ne_zero _ hx)).congr_deriv
  rw [pow_succ]
  field_simp
  ring

-- Differentiate the square-root factor separately from the Laurent polynomial.
private theorem ratio_deriv {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Real.sqrt y / Real.sqrt (1 - y))
      (1 / (2 * Real.sqrt x * (1 - x) * Real.sqrt (1 - x))) x := by
  have hpos := sub_pos.mpr hx1
  have hs := Real.sqrt_pos.2 hx0
  have ht := Real.sqrt_pos.2 hpos
  have h := ((hasDerivAt_id x).const_sub 1).sqrt hpos.ne'
  apply ((Real.hasDerivAt_sqrt hx0.ne').fun_div h ht.ne').congr_deriv
  dsimp
  field_simp
  rw [Real.sq_sqrt hpos.le, Real.sq_sqrt hx0.le]
  ring

private theorem factor_deriv (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => zuritaS n y / y ^ n * (Real.sqrt y / Real.sqrt (1 - y)))
      (1 / (x ^ n * Real.sqrt x * (1 - x) * Real.sqrt (1 - x))) x := by
  have hS : HasDerivAt (fun y => zuritaS n y / y ^ n)
      (weightedSum (zuritaSCoeff n) (n + 1) n x / x ^ (n + 1)) x :=
    quotient_deriv _ _ _ hx0.ne'
  apply (hS.fun_mul (ratio_deriv hx0 hx1)).congr_deriv
  rw [pow_succ]
  have hpos := sub_pos.mpr hx1
  have hs := Real.sqrt_pos.2 hx0
  have ht := Real.sqrt_pos.2 hpos
  field_simp
  rw [Real.sq_sqrt hx0.le]
  linear_combination 2 * x * s_identity n x

-- With n = m + 1, the recurrence cancels consecutive powers in the derivative.
private theorem m_step (m k : ℕ) (hk : k < m) :
    ((k : ℝ) + 1 - m - 1 / 2) * (zuritaMCoeff (m + 1) (k + 1) : ℝ) =
      ((k : ℝ) - m) * (zuritaMCoeff (m + 1) k : ℝ) := by
  have hkm : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
  rw [zuritaMCoeff]
  push_cast
  field_simp (disch := linarith)
  ring

private theorem m_identity (m : ℕ) (x : ℝ) :
    (1 - x) * weightedSum (zuritaMCoeff (m + 1)) (m + 1) m x -
      zuritaM (m + 1) x / 2 = -1 := by
  have partial_sum (l : ℕ) (hl : l ≤ m) :
      (1 - x) * weightedSum (zuritaMCoeff (m + 1)) (l + 1) m x -
        (∑ k ∈ range (l + 1), (zuritaMCoeff (m + 1) k : ℝ) * x ^ k) / 2 =
          -1 - ((l : ℝ) - m) * (zuritaMCoeff (m + 1) l : ℝ) * x ^ (l + 1) := by
    induction l with
    | zero =>
      simp [weightedSum, zuritaMCoeff]
      field_simp [show 2 * ((m : ℝ) + 1) - 1 ≠ 0 by linarith [Nat.cast_nonneg (α := ℝ) m]]
      ring
    | succ l ih =>
      unfold weightedSum at *
      rw [sum_range_succ, sum_range_succ (f := fun k => (zuritaMCoeff (m + 1) k : ℝ) * x ^ k)]
      push_cast
      rw [pow_succ x (l + 1)]
      linear_combination ih (by omega) + x ^ (l + 1) * m_step m l hl
  simpa [zuritaM] using partial_sum m le_rfl

/-- The coefficient recurrence for $M_{n-1}$ (cleared of denominators), including the
constant term. -/
public theorem zuritaMCoeff_weighted (n k : ℕ) (hk : k < n) :
    ((n : ℝ) - k - 1 / 2) * (zuritaMCoeff n k : ℝ) =
      if k = 0 then 1 else ((n : ℝ) - k) * (zuritaMCoeff n (k - 1) : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  cases k with
  | zero =>
    simp only [Nat.cast_zero, sub_zero, ite_true, zuritaMCoeff]
    push_cast
    have hm := Nat.cast_nonneg (α := ℝ) m
    field_simp (disch := linarith)
  | succ k =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
    have h := m_step m k (by omega)
    push_cast at h ⊢
    linear_combination -h

-- The final coefficient of M gives d, and all earlier coefficients come from N.
private theorem n_identity (m : ℕ) (x : ℝ) :
    weightedSum (zuritaNCoeff (m + 1)) m m x + (zuritaD (m + 1) : ℝ) * x ^ m =
      zuritaM (m + 1) x / 2 := by
  rw [zuritaM, sum_range_succ, add_div, zuritaD]
  simp only [Nat.add_sub_cancel, Rat.cast_div, Rat.cast_ofNat]
  rw [weightedSum, sum_div]
  congr 1
  · apply sum_congr rfl
    intro k hk
    have hkm : (k : ℝ) < m := by exact_mod_cast mem_range.mp hk
    rw [zuritaNCoeff]
    push_cast
    field_simp [show (k : ℝ) - (m + 1) + 1 ≠ 0 by linarith]
    ring
  · ring

private theorem m_factor_deriv (m : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => zuritaM (m + 1) y / y ^ m * (Real.sqrt (1 - y) / Real.sqrt y))
      (-1 / (x ^ (m + 1) * Real.sqrt x * Real.sqrt (1 - x))) x := by
  have hpos := sub_pos.mpr hx1
  have hs := Real.sqrt_pos.2 hx0
  have ht := Real.sqrt_pos.2 hpos
  have hr : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y) / Real.sqrt y)
      (-1 / (2 * x * Real.sqrt x * Real.sqrt (1 - x))) x := by
    apply ((((hasDerivAt_id x).const_sub 1).sqrt hpos.ne').fun_div
      (Real.hasDerivAt_sqrt hx0.ne') hs.ne').congr_deriv
    dsimp
    field_simp
    rw [Real.sq_sqrt hx0.le, Real.sq_sqrt hpos.le]
    ring
  have hM : HasDerivAt (fun y => zuritaM (m + 1) y / y ^ m)
      (weightedSum (zuritaMCoeff (m + 1)) (m + 1) m x / x ^ (m + 1)) x :=
    quotient_deriv _ _ _ hx0.ne'
  apply (hM.fun_mul hr).congr_deriv
  rw [pow_succ]
  field_simp
  rw [Real.sq_sqrt hpos.le]
  linear_combination 2 * m_identity m x

private theorem arcsin_sqrt_deriv {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Real.arcsin (Real.sqrt y))
      (1 / (2 * Real.sqrt x * Real.sqrt (1 - x))) x := by
  have hs := Real.sqrt_pos.2 hx0
  have hs1 : Real.sqrt x < 1 := by nlinarith only [Real.sq_sqrt hx0.le, hx1]
  apply ((Real.hasDerivAt_arcsin (by linarith : Real.sqrt x ≠ -1) hs1.ne).comp x
    (Real.hasDerivAt_sqrt hx0.ne')).congr_deriv
  rw [Real.sq_sqrt hx0.le]
  ring

end ZuritaAntiderivative

open ZuritaAntiderivative

/-- **Zurita's antiderivative of $x^{-n-1/2}\arcsin(\sqrt{x})/(1-x)^{3/2}$.** Let $n \ge 1$, let
$c_n$ be Zurita's constant and let $S_n$ and $T_{n-2}$ be Zurita's polynomials (with
$T_{-1} = 0$). For every real $x$ with $0 < x < 1$, the function
$$
F(y) = \log|y - 1| + c_n \log y + \frac{T_{n-2}(y)}{y^{n-1}} +
\frac{\arcsin(\sqrt{y})\, S_n(y)}{y^{n-1/2} \sqrt{1 - y}}
$$
has derivative $x^{-n-1/2} \arcsin(\sqrt{x}) / (1 - x)^{3/2}$ at $x$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Lemma 1 (`integers-2026-A2-lem-1`). -/
theorem hasDerivAt_zurita_antiderivative_one {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Real.log (y - 1) + (zuritaC n : ℝ) * Real.log y +
        zuritaT n y / y ^ (n - 1) +
        Real.arcsin (Real.sqrt y) * zuritaS n y / (y ^ ((n : ℝ) - 1 / 2) * Real.sqrt (1 - y)))
      (x ^ (-(n : ℝ) - 1 / 2) * Real.arcsin (Real.sqrt x) / (1 - x) ^ ((3 : ℝ) / 2)) x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hpos := sub_pos.mpr hx1
  have hs := Real.sqrt_pos.2 hx0
  have ht := Real.sqrt_pos.2 hpos
  have ha := arcsin_sqrt_deriv hx0 hx1
  have hT : HasDerivAt (fun y => zuritaT (m + 1) y / y ^ m)
      (weightedSum (zuritaTCoeff (m + 1)) m m x / x ^ (m + 1)) x :=
    quotient_deriv _ _ _ hx0.ne'
  have hcross : 1 / (2 * Real.sqrt x * Real.sqrt (1 - x)) *
      (zuritaS (m + 1) x / x ^ (m + 1) * (Real.sqrt x / Real.sqrt (1 - x))) =
        zuritaS (m + 1) x / (2 * x ^ (m + 1) * (1 - x)) := by
    field_simp
    rw [Real.sq_sqrt hpos.le]
  have hrest : 1 / (x - 1) + (zuritaC (m + 1) : ℝ) * x⁻¹ +
      weightedSum (zuritaTCoeff (m + 1)) m m x / x ^ (m + 1) +
      zuritaS (m + 1) x / (2 * x ^ (m + 1) * (1 - x)) = 0 := by
    rw [← neg_sub 1 x]
    field_simp
    linear_combination 2 * x * t_identity m x
  have hlog := ((hasDerivAt_id x).sub_const 1).log (sub_ne_zero.mpr hx1.ne)
  have h := ((hlog.add ((Real.hasDerivAt_log hx0.ne').const_mul (zuritaC (m + 1) : ℝ))).add
    hT).add (ha.fun_mul (factor_deriv (m + 1) hx0 hx1))
  apply (h.congr_of_eventuallyEq ?_).congr_deriv
  · dsimp
    rw [Real.rpow_sub hx0, Real.rpow_neg hx0.le, Real.rpow_natCast, ← Real.sqrt_eq_rpow,
      show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    rw [hcross, ← add_assoc, hrest, zero_add]
    field_simp
  · filter_upwards [lt_mem_nhds hx0] with y hy
    dsimp
    rw [Real.rpow_sub hy, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring

/-- **Zurita's antiderivative of $x^{-n-1/2}\arcsin(\sqrt{x})/\sqrt{1-x}$.** Let $n \ge 1$, let
$d_n$ be Zurita's constant and let $M_{n-1}$ and $N_{n-2}$ be Zurita's polynomials (with
$N_{-1} = 0$). For every real $x$ with $0 < x < 1$, the function
$$
G(y) = d_n \log y - \frac{\arcsin(\sqrt{y}) \sqrt{y(1 - y)}\, M_{n-1}(y)}{y^n} +
\frac{N_{n-2}(y)}{y^{n-1}}
$$
has derivative $x^{-n-1/2} \arcsin(\sqrt{x}) / \sqrt{1 - x}$ at $x$.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Lemma 2 (`integers-2026-A2-lem-2`). -/
theorem hasDerivAt_zurita_antiderivative_two {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => (zuritaD n : ℝ) * Real.log y -
        Real.arcsin (Real.sqrt y) * Real.sqrt (y * (1 - y)) * zuritaM n y / y ^ n +
        zuritaN n y / y ^ (n - 1))
      (x ^ (-(n : ℝ) - 1 / 2) * Real.arcsin (Real.sqrt x) / Real.sqrt (1 - x)) x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hpos := sub_pos.mpr hx1
  have hs := Real.sqrt_pos.2 hx0
  have ht := Real.sqrt_pos.2 hpos
  have hN : HasDerivAt (fun y => zuritaN (m + 1) y / y ^ m)
      (weightedSum (zuritaNCoeff (m + 1)) m m x / x ^ (m + 1)) x :=
    quotient_deriv _ _ _ hx0.ne'
  have hcross : 1 / (2 * Real.sqrt x * Real.sqrt (1 - x)) *
      (zuritaM (m + 1) x / x ^ m * (Real.sqrt (1 - x) / Real.sqrt x)) =
        zuritaM (m + 1) x / (2 * x ^ (m + 1)) := by
    rw [pow_succ]
    field_simp
    rw [Real.sq_sqrt hx0.le]
  have hrest : (zuritaD (m + 1) : ℝ) * x⁻¹ +
      weightedSum (zuritaNCoeff (m + 1)) m m x / x ^ (m + 1) -
      zuritaM (m + 1) x / (2 * x ^ (m + 1)) = 0 := by
    rw [pow_succ]
    field_simp
    linear_combination 2 * n_identity m x
  have h := (((Real.hasDerivAt_log hx0.ne').const_mul (zuritaD (m + 1) : ℝ)).sub
    ((arcsin_sqrt_deriv hx0 hx1).fun_mul (m_factor_deriv m hx0 hx1))).add hN
  apply (h.congr_of_eventuallyEq ?_).congr_deriv
  · dsimp
    rw [Real.rpow_sub hx0, Real.rpow_neg hx0.le, Real.rpow_natCast, ← Real.sqrt_eq_rpow, hcross]
    linear_combination hrest
  · filter_upwards [lt_mem_nhds hx0] with y hy
    dsimp
    rw [Real.sqrt_mul hy.le, pow_succ]
    field_simp
    linear_combination -Real.arcsin (Real.sqrt y) * Real.sqrt (1 - y) *
      zuritaM (m + 1) y * Real.sq_sqrt hy.le

end

end MetaMathlibExt
