/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Complex.Basic
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Weighted sums of even-indexed (a, b)-Fibonacci numbers

The generalized Catalan identity gives the recurrence for the product of consecutive
(a, b)-Fibonacci numbers, which yields the weighted sum by induction.
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

end MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted
