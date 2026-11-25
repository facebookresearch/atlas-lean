/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Weighted sums of (a, b)-Fibonacci numbers

The generalized Catalan identity gives the recurrence for the product of consecutive
(a, b)-Fibonacci numbers, which yields the weighted even-index sum by induction.
For the even and odd sums weighted by powers of `-b`, multiplying by the discriminant
turns each summand into a difference of weighted Lucas numbers.
At Pell and Jacobsthal parameters, both the even and odd alternating sums telescope.
For the sum weighted by powers of `c`, adjoining the last term gives a first-order recurrence.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted

/-- **The (a, b)-Fibonacci numbers.** For complex numbers $a$ and $b$, the $(a,b)$-Fibonacci
numbers $F^{a,b}_n$, $n \in \mathbb{N}$, are the complex numbers given by $F^{a,b}_0 = 0$,
$F^{a,b}_1 = 1$ and $F^{a,b}_{n+2} = a F^{a,b}_{n+1} + b F^{a,b}_n$ for every $n$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
def fibAB (a b : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 => a * fibAB a b (n + 1) + b * fibAB a b n

/-- **Zeroth (a, b)-Fibonacci number.** For all complex numbers $a$ and $b$, the $(a,b)$-Fibonacci
number $F^{a,b}_0$ equals $0$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
@[simp]
theorem fibAB_zero (a b : ℂ) : fibAB a b 0 = 0 := rfl

/-- **First (a, b)-Fibonacci number.** For all complex numbers $a$ and $b$, the $(a,b)$-Fibonacci
number $F^{a,b}_1$ equals $1$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
@[simp]
theorem fibAB_one (a b : ℂ) : fibAB a b 1 = 1 := rfl

/-- **Recurrence for the (a, b)-Fibonacci numbers.** For all complex numbers $a$ and $b$ and every
natural number $n$, the $(a,b)$-Fibonacci numbers satisfy
$F^{a,b}_{n+2} = a F^{a,b}_{n+1} + b F^{a,b}_n$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
theorem fibAB_add_two (a b : ℂ) (n : ℕ) :
    fibAB a b (n + 2) = a * fibAB a b (n + 1) + b * fibAB a b n :=
  rfl

/-- **(a, b)-Lucas numbers.** For complex numbers $a$ and $b$, the $(a, b)$-Lucas numbers are the
sequence $(L_n)_{n \ge 0}$ of complex numbers defined by $L_0 = 2$, $L_1 = a$ and
$L_{n+2} = a L_{n+1} + b L_n$ for all $n \ge 0$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
def lucasAB (a b : ℂ) : ℕ → ℂ
  | 0 => 2
  | 1 => a
  | n + 2 => a * lucasAB a b (n + 1) + b * lucasAB a b n

/-- **Zeroth (a, b)-Lucas number.** For all complex numbers $a$ and $b$, the $(a,b)$-Lucas number
$L^{a,b}_0$ equals $2$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
@[simp]
theorem lucasAB_zero (a b : ℂ) : lucasAB a b 0 = 2 := rfl

/-- **First (a, b)-Lucas number.** For all complex numbers $a$ and $b$, the $(a,b)$-Lucas number
$L^{a,b}_1$ equals $a$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
@[simp]
theorem lucasAB_one (a b : ℂ) : lucasAB a b 1 = a := rfl

/-- **Recurrence for the (a, b)-Lucas numbers.** For all complex numbers $a$ and $b$ and every
natural number $n$, the $(a,b)$-Lucas numbers satisfy
$L^{a,b}_{n+2} = a L^{a,b}_{n+1} + b L^{a,b}_n$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Section 1 (sequence
definition). -/
theorem lucasAB_add_two (a b : ℂ) (n : ℕ) :
    lucasAB a b (n + 2) =
      a * lucasAB a b (n + 1) + b * lucasAB a b n :=
  rfl

/-- Horadam's sequence `H_m^{a,b}(r, s)`: `H_0 = r`,
`H_1 = s`, `H_{m+2} = a H_{m+1} + b H_m`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Journal of Integer Sequences 28
(2025), Article 25.1.7, Section 1.2. -/
def horadamAB (a b r s : ℂ) : ℕ → ℂ
  | 0 => r
  | 1 => s
  | n + 2 => a * horadamAB a b r s (n + 1) + b * horadamAB a b r s n

/-- The defining recurrence of `horadamAB`.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Journal of Integer Sequences 28
(2025), Article 25.1.7, Section 1.2. -/
theorem horadamAB_add_two (a b r s : ℂ) (n : ℕ) :
    horadamAB a b r s (n + 2) =
      a * horadamAB a b r s (n + 1) + b * horadamAB a b r s n :=
  rfl

/-- **Sum of even-indexed (a, b)-Fibonacci numbers weighted by powers of -b.** Let $a, b$ be
complex numbers and let $(F_n)$ be the $(a, b)$-Fibonacci numbers. Then for every integer
$n \ge 0$,
$$\sum_{i=0}^{n} (-b)^{n-i} F_{2i} = F_n F_{n+1}.$$

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 11. -/
theorem sum_neg_b_pow_fibAB_even_prod (a b : ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-b) ^ (n - i) * fibAB a b (2 * i) =
      fibAB a b n * fibAB a b (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec := fibAB_add_two a b
    -- At s = 1, the generalized Catalan identity relates consecutive products.
    have h := MetaMathlibExt.horadam_generalized_catalan_identity a b
      (fibAB a b) (fibAB a b) (fibAB a b) hrec hrec hrec
      (fibAB_zero a b) (fibAB_one a b) 1 n (n + 1)
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
    calc
      _ = -b * (∑ i ∈ Finset.range (n + 1), (-b) ^ (n - i) * fibAB a b (2 * i)) +
          fibAB a b (2 * (n + 1)) := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hi), pow_succ', mul_assoc]
      _ = _ := by
        rw [ih, two_mul]
        simpa [Nat.one_add, mul_assoc, mul_comm, mul_left_comm] using
          (sub_eq_iff_eq_add.mp h).symm

private theorem fibAB_succ_mul_discriminant (a b : ℂ) (k : ℕ) :
    fibAB a b (k + 1) * (a ^ 2 + 4 * b) = lucasAB a b (k + 2) + b * lucasAB a b k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [lucasAB, pow_two]; ring
  | one => simp [fibAB, lucasAB]; ring
  | more k ih₀ ih₁ =>
    calc
      _ = a * (fibAB a b (k + 2) * (a ^ 2 + 4 * b)) +
          b * (fibAB a b (k + 1) * (a ^ 2 + 4 * b)) := by
        rw [fibAB_add_two a b (k + 1)]
        ring
      _ = _ := by
        rw [ih₁, ih₀, lucasAB_add_two a b (k + 2)]
        rw [lucasAB_add_two a b k]
        ring

-- The terms telescope along indices of either parity, starting at k + 1.
private theorem sum_fibAB_stride_two (a b : ℂ) (k n : ℕ) :
    (∑ i ∈ Finset.range n, (-b) ^ (n - (i + 1)) * fibAB a b (2 * i + k + 1)) *
      (a ^ 2 + 4 * b) = lucasAB a b (2 * n + k) - (-b) ^ n * lucasAB a b k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    have shift (i : ℕ) : 2 * (i + 1) + k = 2 * i + (k + 2) := by omega
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, shift, Nat.mul_zero, Nat.zero_add, Nat.sub_zero]
    rw [add_mul, ih, mul_assoc, fibAB_succ_mul_discriminant, pow_succ]
    ring

/-- **Sums of (a, b)-Fibonacci numbers weighted by powers of -b, via Lucas numbers.** Let $a, b$
be complex numbers with $\Delta = a^2 + 4b \ne 0$, and let $(F_n)$ and $(L_n)$ be the
$(a, b)$-Fibonacci and $(a, b)$-Lucas numbers. Then for every integer $n \ge 0$,
$$\sum_{i=0}^{n} (-b)^{n-i} F_{2i} = \frac{L_{2n+1} + (-1)^{n+1} a b^n}{\Delta}$$
and
$$\sum_{i=0}^{n} (-b)^{n-i} F_{2i+1} = \frac{L_{2n+2} + 2 (-1)^n b^{n+1}}{\Delta}.$$

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 10(a). -/
theorem sum_neg_b_pow_fibAB_disc (a b : ℂ)
    (hΔ : a ^ 2 + 4 * b ≠ 0) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-b) ^ (n - i) * fibAB a b (2 * i) =
      (lucasAB a b (2 * n + 1) + (-1) ^ (n + 1) * a * b ^ n) /
        (a ^ 2 + 4 * b)) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-b) ^ (n - i) * fibAB a b (2 * i + 1) =
      (lucasAB a b (2 * n + 2) + (-1) ^ n * 2 * b ^ (n + 1)) /
        (a ^ 2 + 4 * b)) := by
  constructor <;> apply (eq_div_iff hΔ).2
  · rw [Finset.sum_range_succ']
    simp only [fibAB_zero, mul_zero, add_zero, Nat.mul_succ]
    rw [sum_fibAB_stride_two a b 1 n, lucasAB_one]
    rw [neg_pow, pow_succ]
    ring
  · calc
      _ = lucasAB a b (2 * n + 2) - (-b) ^ (n + 1) * lucasAB a b 0 := by
        simpa only [Nat.succ_sub_succ_eq_sub, Nat.add_zero, Nat.mul_succ] using
          sum_fibAB_stride_two a b 0 (n + 1)
      _ = _ := by
        rw [lucasAB_zero, neg_pow, pow_succ (-1 : ℂ)]
        ring

/-- **Alternating sums of Pell and Pell–Lucas numbers.** Let $(P_n)$ and $(Q_n)$ be the Pell
and Pell–Lucas numbers, that is, the $(2, 1)$-Fibonacci and $(2, 1)$-Lucas numbers, viewed as
complex numbers. Then for every integer $n \ge 0$,
$$\sum_{i=0}^{n} (-1)^i P_{2i} = \frac{(-1)^n Q_{2n+1} - 2}{8}, \qquad
\sum_{i=0}^{n} (-1)^i Q_{2i} = (-1)^n P_{2n+1} + 1,$$
$$\sum_{i=0}^{n} (-1)^i P_{2i+1} = \frac{(-1)^n Q_{2n+2} + 2}{8}, \qquad
\sum_{i=0}^{n} (-1)^i Q_{2i+1} = (-1)^n P_{2n+2}.$$

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 10(c). -/
theorem sum_neg_one_pow_pell (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * fibAB 2 1 (2 * i) =
      ((-1) ^ n * lucasAB 2 1 (2 * n + 1) - 2) / 8) ∧
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * lucasAB 2 1 (2 * i) =
      (-1) ^ n * fibAB 2 1 (2 * n + 1) + 1) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * fibAB 2 1 (2 * i + 1) =
      ((-1) ^ n * lucasAB 2 1 (2 * n + 2) + 2) / 8) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * lucasAB 2 1 (2 * i + 1) =
      (-1) ^ n * fibAB 2 1 (2 * n + 2)) := by
  -- Each new summand splits into the two boundary terms of the other sequence.
  have pell (k : ℕ) : fibAB 2 1 (k + 1) =
      (lucasAB 2 1 (k + 2) + lucasAB 2 1 k) / 8 := by
    apply (eq_div_iff (by norm_num)).2
    simpa only [show (2 : ℂ) ^ 2 + 4 * 1 = 8 by norm_num, one_mul] using
      fibAB_succ_mul_discriminant 2 1 k
  have pellLucas (k : ℕ) : lucasAB 2 1 (k + 1) =
      fibAB 2 1 (k + 2) + fibAB 2 1 k := by
    induction k using Nat.twoStepInduction with
    | zero => norm_num [fibAB, lucasAB]
    | one => norm_num [fibAB, lucasAB]
    | more k hk hk₁ =>
      rw [lucasAB_add_two 2 1 (k + 1), hk₁, hk, fibAB_add_two 2 1 (k + 2),
        fibAB_add_two 2 1 k]
      ring
  induction n with
  | zero => norm_num [fibAB, lucasAB]
  | succ n ih =>
    obtain ⟨hPe, hQe, hPo, hQo⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_range_succ, hPe, Nat.mul_succ, pell (2 * n + 1), pow_succ]
      ring
    · rw [Finset.sum_range_succ, hQe, Nat.mul_succ, pellLucas (2 * n + 1), pow_succ]
      ring
    · rw [Finset.sum_range_succ, hPo, Nat.mul_succ, pell (2 * n + 2), pow_succ]
      ring
    · rw [Finset.sum_range_succ, hQo, Nat.mul_succ, pellLucas (2 * n + 2), pow_succ]
      ring

/-- **Weighted alternating sums of Jacobsthal and Jacobsthal–Lucas numbers.** Let $(J_n)$ and
$(j_n)$ be the Jacobsthal and Jacobsthal–Lucas numbers, that is, the $(1, 2)$-Fibonacci and
$(1, 2)$-Lucas numbers, viewed as complex numbers. Then for every integer $n \ge 0$,
$$\sum_{i=0}^{n} (-1)^i 2^{n-i} J_{2i} = \frac{(-1)^n j_{2n+1} - 2^n}{9}, \qquad
\sum_{i=0}^{n} (-1)^i 2^{n-i} j_{2i} = (-1)^n J_{2n+1} + 2^n,$$
$$\sum_{i=0}^{n} (-1)^i 2^{n-i} J_{2i+1} = \frac{(-1)^n j_{2n+2} + 2^{n+2}}{9}, \qquad
\sum_{i=0}^{n} (-1)^i 2^{n-i} j_{2i+1} = (-1)^n J_{2n+2}.$$

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 10(d). -/
theorem sum_neg_one_pow_jacobsthal (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * 2 ^ (n - i) * fibAB 1 2 (2 * i) =
      ((-1) ^ n * lucasAB 1 2 (2 * n + 1) - 2 ^ n) / 9) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * 2 ^ (n - i) * lucasAB 1 2 (2 * i) =
      (-1) ^ n * fibAB 1 2 (2 * n + 1) + 2 ^ n) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * 2 ^ (n - i) * fibAB 1 2 (2 * i + 1) =
      ((-1) ^ n * lucasAB 1 2 (2 * n + 2) + 2 ^ (n + 2)) / 9) ∧
    (∑ i ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ i * 2 ^ (n - i) * lucasAB 1 2 (2 * i + 1) =
      (-1) ^ n * fibAB 1 2 (2 * n + 2)) := by
  -- A step of size two leaves only the two endpoints after weighting.
  have telescope (f g : ℕ → ℂ) (h : ∀ k, f (k + 2) = g (k + 2) + 2 * g k)
      (k : ℕ) (m : ℕ) :
      (∑ i ∈ Finset.range (m + 1), (-1 : ℂ) ^ i * 2 ^ (m - i) * f (2 * i + k)) =
        (-1) ^ m * g (2 * m + k) + 2 ^ m * (f k - g k) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
      calc
        _ = 2 * (∑ i ∈ Finset.range (m + 1), (-1 : ℂ) ^ i * 2 ^ (m - i) * f (2 * i + k)) +
            (-1 : ℂ) ^ (m + 1) * f (2 * (m + 1) + k) := by
          rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hi), pow_succ]
          ring
        _ = _ := by
          rw [ih, show 2 * (m + 1) + k = 2 * m + k + 2 by omega, h,
            pow_succ (-1 : ℂ) m, pow_succ (2 : ℂ) m]
          ring
  have jacobsthal (k : ℕ) : fibAB 1 2 (k + 2) =
      lucasAB 1 2 (k + 2 + 1) / 9 + 2 * (lucasAB 1 2 (k + 1) / 9) := by
    rw [← mul_div_assoc, ← add_div]
    apply (eq_div_iff (by norm_num)).2
    simpa only [show (1 : ℂ) ^ 2 + 4 * 2 = 9 by norm_num] using
      fibAB_succ_mul_discriminant 1 2 (k + 1)
  have jacobsthalLucas (k : ℕ) : lucasAB 1 2 (k + 2) =
      fibAB 1 2 (k + 2 + 1) + 2 * fibAB 1 2 (k + 1) := by
    induction k using Nat.twoStepInduction with
    | zero => norm_num [fibAB, lucasAB]
    | one => norm_num [fibAB, lucasAB]
    | more k hk hk₁ =>
      rw [lucasAB_add_two 1 2 (k + 2), hk₁, hk, fibAB_add_two 1 2 (k + 3),
        fibAB_add_two 1 2 (k + 1)]
      ring
  have evenJ := telescope _ (fun k => lucasAB 1 2 (k + 1) / 9) jacobsthal 0 n
  have oddJ := telescope _ (fun k => lucasAB 1 2 (k + 1) / 9) jacobsthal 1 n
  have evenL := telescope _ (fun k => fibAB 1 2 (k + 1)) jacobsthalLucas 0 n
  have oddL := telescope _ (fun k => fibAB 1 2 (k + 1)) jacobsthalLucas 1 n
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Nat.add_zero, Nat.zero_add, fibAB_zero, lucasAB_one] at evenJ
    rw [evenJ]
    ring
  · simpa only [Nat.add_zero, Nat.zero_add, lucasAB_zero, fibAB_one,
      show (2 : ℂ) - 1 = 1 by norm_num, mul_one] using evenL
  · rw [oddJ, pow_add]
    rw [fibAB_one, show lucasAB 1 2 (1 + 1) = 5 by norm_num [lucasAB]]
    ring
  · simpa only [lucasAB_one, show fibAB 1 2 (1 + 1) = 1 by norm_num [fibAB],
      sub_self, mul_zero, add_zero] using oddL

-- The stated identity assumes c ≠ 0, although the induction also works at zero.
set_option linter.unusedVariables false in
/-- **Sums of (a, b)-Fibonacci numbers weighted by powers of c.** Let $a, b, c$ be complex
numbers with $c \ne 0$ and $c^2 - ac - b \ne 0$, and let $(F_n)$ be the $(a, b)$-Fibonacci
numbers. Then for every integer $n \ge 1$,
$$\sum_{i=1}^{n} c^{n-i} F_i = \frac{c^{n+1} - c F_{n+1} - b F_n}{c^2 - ac - b}.$$

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Theorem 12. -/
theorem sum_c_pow_fibAB (a b c : ℂ) (hc : c ≠ 0)
    (hc2 : c ^ 2 - a * c - b ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, c ^ (n - i) * fibAB a b i =
      (c ^ (n + 1) - c * fibAB a b (n + 1) - b * fibAB a b n) /
        (c ^ 2 - a * c - b) := by
  apply (eq_div_iff hc2).2
  induction n, hn using Nat.le_induction with
  | base => simp [fibAB, mul_comm]
  | succ n hn ih =>
    have hsum : ∑ i ∈ Finset.Icc 1 (n + 1), c ^ (n + 1 - i) * fibAB a b i =
        c * (∑ i ∈ Finset.Icc 1 n, c ^ (n - i) * fibAB a b i) + fibAB a b (n + 1) := by
      rw [Finset.sum_Icc_succ_top (hn.trans (Nat.le_succ n)), Nat.sub_self, pow_zero, one_mul,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.succ_sub (Finset.mem_Icc.mp hi).2, pow_succ', mul_assoc]
    rw [hsum, add_mul, mul_assoc, ih, fibAB_add_two, pow_succ c (n + 1)]
    ring

end MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted
