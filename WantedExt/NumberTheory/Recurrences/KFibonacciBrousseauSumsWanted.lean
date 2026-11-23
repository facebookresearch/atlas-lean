/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

/-!
# Brousseau sums of k-Fibonacci numbers

Statements from Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau
Sums*, Journal of Integer Sequences 27 (2024), Article 24.6.4.

The `k`-Fibonacci numbers `F_{k,n}` (`F_{k,0} = 0`, `F_{k,1} = 1`,
`F_{k,n} = k F_{k,n-1} + F_{k,n-2}`) are the Lucas sequence `U(k, -1)`,
`lucasU ⟨k, -1, _⟩`; the Fibonacci, Lucas and Pell numbers are `Nat.fib`, `lucasNumber` and
`pellNumber`, and the Pell–Lucas numbers `Q_n` (`Q_0 = Q_1 = 2`) are `lucasV ⟨2, -1, _⟩`.
The paper takes `k` a positive integer; the identities are stated for every nonzero integer
`k` (every integer `k` in Theorem 1).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The numbers $A_k^{(p)}$ for $k$-Fibonacci Brousseau sums.** For a rational number $k$, the
rational numbers $A_k^{(p)}$, $p \ge 0$, are defined by $A_k^{(0)} = 1$ and, for $p \ge 1$,
$$
A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)},
$$
where $2/k$ is read as $0$ when $k = 0$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
def brousseauA (k : ℚ) : ℕ → ℚ
  | 0 => 1
  | p + 1 => 2 / k * ∑ j ∈ Finset.range ((p + 2) / 2),
      ((p + 1).choose (2 * j + 1) : ℚ) * brousseauA k (p - 2 * j)
decreasing_by omega

/-- **The initial value $A_k^{(0)} = 1$.** For every rational number $k$, the number $A_k^{(0)}$
for $k$-Fibonacci Brousseau sums equals $1$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
theorem brousseauA_zero (k : ℚ) : brousseauA k 0 = 1 := by
  rw [brousseauA]

/-- **The value $A_k^{(1)} = 2/k$.** For every rational number $k$, the number $A_k^{(1)}$ for
$k$-Fibonacci Brousseau sums equals $2/k$, where $2/0$ is read as $0$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
theorem brousseauA_one (k : ℚ) : brousseauA k 1 = 2 / k := by
  rw [brousseauA]
  simp [brousseauA_zero]

/-- **The value $A_k^{(2)} = 8/k^2$.** For every rational number $k$, the number $A_k^{(2)}$ for
$k$-Fibonacci Brousseau sums equals $8/k^2$, where $8/0$ is read as $0$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
theorem brousseauA_two (k : ℚ) : brousseauA k 2 = 8 / k ^ 2 := by
  rw [brousseauA]
  simp [brousseauA_one]
  ring

/-- **The coefficient polynomials $C_k^{(p)}$ for $k$-Fibonacci Brousseau sums.** For a rational
number $k$, let $A_k^{(r)}$ be the numbers for $k$-Fibonacci Brousseau sums. For a natural number
$p$ and a rational number $n$,
$$
C_k^{(p)}(n) = \sum_{r=0}^{p} (-1)^r A_k^{(r)} \binom{p}{r} n^{p-r},
$$
where $0^0 = 1$; in particular $C_k^{(p)}(0) = (-1)^p A_k^{(p)}$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 5. -/
def brousseauCoeff (k : ℚ) (p : ℕ) (n : ℚ) : ℚ :=
  ∑ r ∈ Finset.range (p + 1), (-1) ^ r * brousseauA k r * (p.choose r : ℚ) * n ^ (p - r)

/-- **The polynomial $C_k^{(0)}$ is constant $1$.** For all rational numbers $k$ and $n$, the
coefficient polynomial $C_k^{(0)}$ for $k$-Fibonacci Brousseau sums satisfies $C_k^{(0)}(n) = 1$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 5. -/
theorem brousseauCoeff_zero (k n : ℚ) : brousseauCoeff k 0 n = 1 := by
  simp [brousseauCoeff, brousseauA_zero]

/-- **The polynomial $C_k^{(1)}(n) = n - 2/k$.** For all rational numbers $k$ and $n$, the
coefficient polynomial $C_k^{(1)}$ for $k$-Fibonacci Brousseau sums satisfies
$C_k^{(1)}(n) = n - 2/k$, where $2/0$ is read as $0$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 5. -/
theorem brousseauCoeff_one (k n : ℚ) : brousseauCoeff k 1 n = n - 2 / k := by
  simp [brousseauCoeff, Finset.sum_range_succ, brousseauA_zero, brousseauA_one]
  ring

/-- **$k$-Fibonacci numbers as a power-weighted convolution.** For an integer $k$, let $F_{k,n}$
be the $k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$: $F_{k,0} = 0$, $F_{k,1} = 1$ and
$F_{k,n+2} = k F_{k,n+1} + F_{k,n}$. For every integer $k$, every $n \ge 0$ and every $p \ge 1$,
$$
F_{k,n} = n^p + \sum_{i=1}^{n} \Bigl(k i^p -
2 \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} i^{p-2j+1}\Bigr) F_{k,n-i}.
$$

The paper assumes $k \ge 1$ and $n \ge 1$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 1 (`jis-2024-24.6.4-thm-1`). -/
public theorem_wanted kFibonacci_eq_pow_add_convolution (k : ℤ) (n p : ℕ) (hp : 1 ≤ p) :
    lucasU ⟨k, -1, by decide⟩ n = (n : ℤ) ^ p +
      ∑ i ∈ Finset.Icc 1 n, (k * (i : ℤ) ^ p -
        2 * ∑ j ∈ Finset.Icc 1 ((p + 1) / 2),
          (p.choose (2 * j - 1) : ℤ) * (i : ℤ) ^ (p + 1 - 2 * j)) *
        lucasU ⟨k, -1, by decide⟩ (n - i)

/-- **Power-weighted convolution of k-Fibonacci numbers.** Let $k$ be a nonzero integer and let
$F_{k,n}$ be the $k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$: $F_{k,0} = 0$,
$F_{k,1} = 1$ and $F_{k,n+2} = k F_{k,n+1} + F_{k,n}$. Let $A_k^{(0)} = 1$ and
$A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)}$ for
$p \ge 1$. Then for all natural numbers $n$ and $p$, with $0^0 = 1$,
$$
k \sum_{i=0}^{n} i^p F_{k,n-i} = A_k^{(p)} F_{k,n+1} +
\sum_{r=0}^{p} A_k^{(r)} \binom{p}{r} \left((-1)^{p-r} F_{k,n} - n^{p-r}\right).
$$

The source takes $k$ to be a positive integer.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 4 (`jis-2024-24.6.4-thm-4`). -/
public theorem_wanted kFibonacci_power_convolution (k : ℤ) (hk : k ≠ 0) (n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ (n - i) =
      brousseauA k p * lucasU ⟨k, -1, by decide⟩ (n + 1) +
        ∑ r ∈ Finset.range (p + 1), brousseauA k r * (p.choose r : ℚ) *
          ((-1) ^ (p - r) * lucasU ⟨k, -1, by decide⟩ n - (n : ℚ) ^ (p - r))

/-- **Brousseau sums of $k$-Fibonacci numbers.** For an integer $k$, let $F_{k,n}$ be the
$k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$ ($F_{k,0} = 0$, $F_{k,1} = 1$,
$F_{k,n+2} = k F_{k,n+1} + F_{k,n}$), and let $C_k^{(p)}$ be the coefficient polynomials. For
every nonzero integer $k$ and all $n, p \ge 0$,
$$
k \sum_{i=0}^{n} i^p F_{k,i} = C_k^{(p)}(n) F_{k,n+1} + C_k^{(p)}(n+1) F_{k,n} - C_k^{(p)}(0),
$$
where $0^0 = 1$.

The paper assumes $k \ge 1$.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 6 (`jis-2024-24.6.4-thm-6`). -/
public theorem_wanted kFibonacci_brousseau_sum (k : ℤ) (hk : k ≠ 0) (n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ i =
      brousseauCoeff k p n * lucasU ⟨k, -1, by decide⟩ (n + 1) +
        brousseauCoeff k p (n + 1) * lucasU ⟨k, -1, by decide⟩ n - brousseauCoeff k p 0

/-- **Brousseau sums of Fibonacci numbers along an odd step.** Let $F_n$ be the Fibonacci
numbers, $L_n$ the Lucas numbers and $C_k^{(p)}$ the coefficient polynomials. For every odd
natural number $m$ and all $n, p \ge 0$,
$$
L_m \sum_{i=1}^{n} i^p F_{mi} = C_{L_m}^{(p)}(n) F_{m(n+1)} + C_{L_m}^{(p)}(n+1) F_{mn} -
C_{L_m}^{(p)}(0) F_m.
$$

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Corollary 9 (`jis-2024-24.6.4-cor-9`). -/
public theorem_wanted fibonacci_brousseau_sum_mul_odd (m : ℕ) (hm : Odd m) (n p : ℕ) :
    (lucasNumber m : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * Nat.fib (m * i) =
      brousseauCoeff (lucasNumber m) p n * Nat.fib (m * (n + 1)) +
        brousseauCoeff (lucasNumber m) p (n + 1) * Nat.fib (m * n) -
        brousseauCoeff (lucasNumber m) p 0 * Nat.fib m

/-- **Power-weighted Pell sums along odd multiples.** Let $P_n$ be the Pell numbers and $Q_n$ the
Pell–Lucas numbers, the Lucas sequence $V(2, -1)$: $Q_0 = Q_1 = 2$ and
$Q_{n+2} = 2 Q_{n+1} + Q_n$. Let $m$ be an odd natural number and write $k = Q_m$. Let
$A_k^{(0)} = 1$ and
$A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)}$ for
$p \ge 1$, and let $C_k^{(p)}(x) = \sum_{r=0}^{p} (-1)^r A_k^{(r)} \binom{p}{r} x^{p-r}$, with
$0^0 = 1$. Then for all natural numbers $n$ and $p$,
$$
Q_m \sum_{i=1}^{n} i^p P_{mi} = C_k^{(p)}(n) P_{m(n+1)} + C_k^{(p)}(n+1) P_{mn} -
C_k^{(p)}(0) P_m.
$$

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Corollary 10
(`jis-2024-24.6.4-cor-10`). -/
public theorem_wanted pell_brousseau_sum_mul_odd (m : ℕ) (hm : Odd m) (n p : ℕ) :
    (lucasV ⟨2, -1, by decide⟩ m : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * pellNumber (m * i) =
      brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p n * pellNumber (m * (n + 1)) +
        brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p (n + 1) * pellNumber (m * n) -
        brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p 0 * pellNumber m

/-- **Shifted power-weighted sums of k-Fibonacci numbers.** Let $k$ be a nonzero integer and let
$F_{k,n}$ be the $k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$: $F_{k,0} = 0$,
$F_{k,1} = 1$ and $F_{k,n+2} = k F_{k,n+1} + F_{k,n}$. Let $A_k^{(0)} = 1$ and
$A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)}$ for
$p \ge 1$, and let $C_k^{(p)}(x) = \sum_{r=0}^{p} (-1)^r A_k^{(r)} \binom{p}{r} x^{p-r}$, with
$0^0 = 1$. Then for all natural numbers $m$, $n$ and $p$,
$$
k \sum_{i=1}^{n} i^p F_{k,m+i} = C_k^{(p)}(n) F_{k,m+n+1} + C_k^{(p)}(n+1) F_{k,m+n} -
C_k^{(p)}(0) F_{k,m+1} - C_k^{(p)}(1) F_{k,m}.
$$

The source takes $k$ to be a positive integer.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 11 (`jis-2024-24.6.4-thm-11`). -/
public theorem_wanted kFibonacci_shifted_brousseau_sum (k : ℤ) (hk : k ≠ 0) (m n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ (m + i) =
      brousseauCoeff k p n * lucasU ⟨k, -1, by decide⟩ (m + n + 1) +
        brousseauCoeff k p (n + 1) * lucasU ⟨k, -1, by decide⟩ (m + n) -
        brousseauCoeff k p 0 * lucasU ⟨k, -1, by decide⟩ (m + 1) -
        brousseauCoeff k p 1 * lucasU ⟨k, -1, by decide⟩ m

end

end MetaMathlibExt
