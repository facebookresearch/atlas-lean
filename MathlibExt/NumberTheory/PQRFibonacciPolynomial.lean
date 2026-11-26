/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.GaussianBinomial
import Mathlib.Tactic.Ring

/-!
# The (p,q)-analogue of the r-Fibonacci polynomials

We define the polynomials using the division-free (p,q)-binomial coefficients and
prove their first recurrence over a commutative semiring.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **$(p,q)$-binomial coefficient.** Let $R$ be a commutative semiring and $p, q \in R$. For
natural numbers $n$ and $k$, the $(p,q)$-binomial coefficient $\binom{n}{k}_{p,q} \in R$ is
defined recursively by $\binom{n}{0}_{p,q} = 1$, $\binom{0}{k+1}_{p,q} = 0$ and
$\binom{n+1}{k+1}_{p,q} = p^{n-k} \binom{n}{k}_{p,q} + q^{k+1} \binom{n}{k+1}_{p,q}$, where $n - k$
is truncated subtraction ($0$ when $k > n$).

For $k \le n$, where the $(p,q)$-factorials are invertible, $\binom{n}{k}_{p,q}$ equals
$[n]_{p,q}! / ([k]_{p,q}! \, [n-k]_{p,q}!)$, where $[j]_{p,q} = p^{j-1} + p^{j-2} q + \dots +
q^{j-1}$; this is the definition used in the source. At $p = 1$ it is the Gaussian binomial
coefficient $\binom{n}{k}_q$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3, Equation (3). -/
public def pqBinomial {R : Type*} [CommSemiring R] (p q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => p ^ (n - k) * pqBinomial p q n k + q ^ (k + 1) * pqBinomial p q n (k + 1)

/-- **$(p,q)$-binomial coefficients with lower index zero.** For all elements $p, q$ of a
commutative semiring and every natural number $n$, the $(p,q)$-binomial coefficient
$\binom{n}{0}_{p,q}$ equals $1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3. -/
public theorem pqBinomial_zero_right {R : Type*} [CommSemiring R] (p q : R) (n : ℕ) :
    pqBinomial p q n 0 = 1 := by
  cases n <;> rfl

/-- **$(p,q)$-binomial coefficients with upper index zero and positive lower index.** For all
elements $p, q$ of a commutative semiring and every natural number $k$, the $(p,q)$-binomial
coefficient $\binom{0}{k+1}_{p,q}$ equals $0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3. -/
public theorem pqBinomial_zero_succ {R : Type*} [CommSemiring R] (p q : R) (k : ℕ) :
    pqBinomial p q 0 (k + 1) = 0 := rfl

/-- **Pascal recursion for $(p,q)$-binomial coefficients.** For all elements $p, q$ of a
commutative semiring and all natural numbers $n$ and $k$, the $(p,q)$-binomial coefficients satisfy
$\binom{n+1}{k+1}_{p,q} = p^{n-k} \binom{n}{k}_{p,q} + q^{k+1} \binom{n}{k+1}_{p,q}$, where $n - k$
is truncated subtraction ($0$ when $k > n$).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3, Equation (3). -/
public theorem pqBinomial_succ_succ {R : Type*} [CommSemiring R] (p q : R) (n k : ℕ) :
    pqBinomial p q (n + 1) (k + 1)
      = p ^ (n - k) * pqBinomial p q n k + q ^ (k + 1) * pqBinomial p q n (k + 1) := rfl

/-- **The $(p, q)$-binomial coefficients at $p = 1$.** Let $R$ be a commutative semiring and
$q \in R$. For all natural numbers $n$ and $k$, the $(p, q)$-binomial coefficient
$[n, k]_{p,q}$ at $p = 1$ equals the Gaussian binomial coefficient $\binom{n}{k}_q$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3 (Remark 1: `p = 1` gives the `q`-analogue). -/
public theorem pqBinomial_one_left {R : Type*} [CommSemiring R] (q : R) (n k : ℕ) :
    pqBinomial 1 q n k = MathlibExt.gaussBinom q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [pqBinomial_zero_right, pqBinomial_zero_succ]
  | succ n ih =>
    cases k with
    | zero => simp [pqBinomial_zero_right]
    | succ k => rw [pqBinomial_succ_succ, MathlibExt.gaussBinom_succ_succ, ih, ih]; simp

/-- **$(p,q)$-analogue of the $r$-Fibonacci polynomial.** Let $R$ be a commutative semiring, let
$r$ and $m$ be natural numbers and let $x, y, p, q \in R$. The $(p,q)$-analogue
$U^{(r)}_n(x, y, p, q, m) \in R$ of the $r$-Fibonacci polynomial is defined by
$U^{(r)}_0(x, y, p, q, m) = 0$ and, for every natural number $n$,
$$
U^{(r)}_{n+1}(x, y, p, q, m) = \sum_{k=0}^{\lfloor n/(r+1) \rfloor} p^{\binom{n+1-(r+1)k}{2}}
q^{\binom{k+1}{2} + m \binom{k}{2}} \binom{n-rk}{k}_{p,q} x^{n-(r+1)k} y^k,
$$
where $\binom{a}{b}_{p,q}$ is the $(p,q)$-binomial coefficient.

The source also states $U^{(r)}_j = p^{\binom{j+1}{2}} x^{j-1}$ for $1 \le j \le r$, which
contradicts this sum: the sum gives $p^{\binom{j}{2}} x^{j-1}$ (for example $U^{(2)}_2 = p x$,
not $p^3 x$). The sum, which Theorem 2 of the source requires, is used.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 1. -/
public def pqRFibonacci {R : Type*} [CommSemiring R] (r : ℕ) (x y p q : R) (m : ℕ) : ℕ → R
  | 0 => 0
  | n + 1 => ∑ k ∈ Finset.range (n / (r + 1) + 1),
      p ^ (n + 1 - (r + 1) * k).choose 2 * q ^ ((k + 1).choose 2 + m * k.choose 2) *
        pqBinomial p q (n - r * k) k * x ^ (n - (r + 1) * k) * y ^ k

/-- **Zeroth value of the $(p,q)$-analogue of the $r$-Fibonacci polynomial.** For all natural
numbers $r$ and $m$ and all elements $x, y, p, q$ of a commutative semiring, the
$(p,q)$-analogue of the $r$-Fibonacci polynomial satisfies $U^{(r)}_0(x, y, p, q, m) = 0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 1. -/
public theorem pqRFibonacci_zero {R : Type*} [CommSemiring R] (r : ℕ) (x y p q : R)
    (m : ℕ) : pqRFibonacci r x y p q m 0 = 0 := rfl

/-- **First value of the $(p,q)$-analogue of the $r$-Fibonacci polynomial.** For all natural
numbers $r$ and $m$ and all elements $x, y, p, q$ of a commutative semiring, the
$(p,q)$-analogue of the $r$-Fibonacci polynomial satisfies $U^{(r)}_1(x, y, p, q, m) = 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 1. -/
public theorem pqRFibonacci_one {R : Type*} [CommSemiring R] (r : ℕ) (x y p q : R)
    (m : ℕ) : pqRFibonacci r x y p q m 1 = 1 := by
  simp [pqRFibonacci, pqBinomial_zero_right]

end

variable {R : Type*} [CommSemiring R]

private theorem pqBinomial_eq_zero_of_lt (p q : R) {n k : ℕ} (h : n < k) :
    pqBinomial p q n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => exact pqBinomial_zero_succ p q k
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [pqBinomial_succ_succ, ih (by omega), ih (by omega), mul_zero, mul_zero, add_zero]

-- The summand with x-degree `d` and y-degree `k`, before imposing the range of the sum.
private def pqRFibonacciWeight (x y p q : R) (m d k : ℕ) : R :=
  p ^ (d + 1).choose 2 * q ^ ((k + 1).choose 2 + m * k.choose 2) *
    pqBinomial p q (d + k) k * x ^ d * y ^ k

private def pqRFibonacciTerm (r : ℕ) (x y p q : R) (m n k : ℕ) : R :=
  if (r + 1) * k < n then pqRFibonacciWeight x y p q m (n - 1 - (r + 1) * k) k else 0

private theorem pqRFibonacci_eq_sum_term (r : ℕ) (x y p q : R) (m n b : ℕ) (h : n ≤ b) :
    pqRFibonacci r x y p q m n = ∑ k ∈ Finset.range b, pqRFibonacciTerm r x y p q m n k := by
  cases n with
  | zero => simp [pqRFibonacci_zero, pqRFibonacciTerm]
  | succ n =>
    rw [pqRFibonacci]
    have hmem (k : ℕ) : k ∈ Finset.range (n / (r + 1) + 1) ↔ (r + 1) * k < n + 1 := by
      simp only [Finset.mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (Nat.succ_pos r),
        Nat.mul_comm k (r + 1)]
    calc
      _ = ∑ k ∈ Finset.range (n / (r + 1) + 1), pqRFibonacciTerm r x y p q m (n + 1) k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := (hmem k).mp hk
        have hmul : (r + 1) * k = r * k + k := Nat.succ_mul r k
        simp only [pqRFibonacciTerm, ite_eq_left hk', Nat.add_sub_cancel, pqRFibonacciWeight]
        rw [show n + 1 - (r + 1) * k = n - (r + 1) * k + 1 by omega,
          show n - r * k = n - (r + 1) * k + k by omega]
      _ = _ := by
        have hdiv := Nat.div_le_self n (r + 1)
        refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
        intro k _ hk
        exact ite_eq_right (fun hk' => hk ((hmem k).mpr hk'))

private theorem pqRFibonacciTerm_zero_right (r : ℕ) (x y p q : R) (m n : ℕ) (hn : 0 < n) :
    pqRFibonacciTerm r x y p q m (n + 1) 0 =
      p * x * pqRFibonacciTerm r (p * x) (q * y) p q m n 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [pqRFibonacciTerm, Nat.mul_zero, Nat.zero_lt_succ, ite_true, Nat.succ_sub_one,
    Nat.sub_zero, pqRFibonacciWeight, Nat.add_zero, pqBinomial_zero_right,
    Nat.choose_eq_zero_of_lt (by decide : 1 < 2), Nat.choose_zero_succ, Nat.mul_zero,
    pow_zero, mul_one, Nat.succ_eq_add_one]
  rw [Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
  simp only [mul_pow, pow_add, pow_one]
  ring

private theorem pqRFibonacciWeight_succ_right (x y p q : R) (m d k : ℕ) :
    pqRFibonacciWeight x y p q m d (k + 1) =
      (if d = 0 then 0 else p * x * pqRFibonacciWeight (p * x) (q * y) p q m (d - 1) (k + 1)) +
        q * y * pqRFibonacciWeight (p * x) (q ^ (m + 1) * y) p q m d k := by
  have hq : (k + 1 + 1).choose 2 + m * (k + 1).choose 2 =
      ((k + 1).choose 2 + m * k.choose 2) + (m + 1) * k + 1 := by
    rw [Nat.choose_succ_succ (k + 1) 1, Nat.choose_one_right, Nat.choose_succ_succ k 1,
      Nat.choose_one_right]
    ring
  rw [add_comm _ (q * y * pqRFibonacciWeight (p * x) (q ^ (m + 1) * y) p q m d k)]
  unfold pqRFibonacciWeight
  rw [show d + (k + 1) = d + k + 1 by omega, pqBinomial_succ_succ, Nat.add_sub_cancel]
  simp only [mul_add, add_mul]
  congr 1
  · rw [hq]
    simp only [mul_pow, ← pow_mul, pow_add, pow_one]
    ring
  · -- At x-degree zero the same-index binomial coefficient is out of range.
    cases d with
    | zero => simp [pqBinomial_eq_zero_of_lt p q (Nat.lt_succ_self k)]
    | succ d =>
      simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
      rw [show d + 1 + k = d + (k + 1) by omega, Nat.choose_succ_succ (d + 1) 1,
        Nat.choose_one_right]
      simp only [mul_pow, pow_add, pow_one]
      ring

private theorem pqRFibonacciTerm_succ_right (r : ℕ) (x y p q : R) (m n k : ℕ) :
    pqRFibonacciTerm r x y p q m (n + 1) (k + 1) =
      p * x * pqRFibonacciTerm r (p * x) (q * y) p q m n (k + 1) +
        q * y * pqRFibonacciTerm r (p * x) (q ^ (m + 1) * y) p q m (n - r) k := by
  have hstep : (r + 1) * (k + 1) = (r + 1) * k + r + 1 := by
    rw [Nat.mul_succ, Nat.add_assoc]
  unfold pqRFibonacciTerm
  by_cases h : (r + 1) * (k + 1) ≤ n
  · rw [ite_eq_left (show (r + 1) * (k + 1) < n + 1 by omega),
      ite_eq_left (show (r + 1) * k < n - r by omega), Nat.add_sub_cancel,
      show n - r - 1 - (r + 1) * k = n - (r + 1) * (k + 1) by omega,
      pqRFibonacciWeight_succ_right]
    congr 1
    by_cases h' : (r + 1) * (k + 1) < n
    · rw [ite_eq_left h', ite_eq_right (by omega),
        show n - 1 - (r + 1) * (k + 1) = n - (r + 1) * (k + 1) - 1 by omega]
    · rw [ite_eq_right h', ite_eq_left (by omega), mul_zero]
  · rw [ite_eq_right (show ¬(r + 1) * (k + 1) < n + 1 by omega),
      ite_eq_right (show ¬(r + 1) * (k + 1) < n by omega),
      ite_eq_right (show ¬(r + 1) * k < n - r by omega), mul_zero, mul_zero, add_zero]

/-- **First recurrence for the $(p,q)$-analogue of the $r$-Fibonacci polynomial.** Let $R$ be a
commutative semiring, let $r \ge 1$, $n \ge r$ and $m$ be natural numbers and let
$x, y, p, q \in R$. Write $U_j(x, y)$ for $U^{(r)}_j(x, y, p, q, m)$, the $(p,q)$-analogue of the
$r$-Fibonacci polynomial with $r$, $p$, $q$ and $m$ fixed. Then
$$U_{n+1}(x, y) = p x \, U_n(p x, q y) + q y \, U_{n-r}(p x, q^{m+1} y).$$

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 2, Equation (4) (`integers-2025-A38-thm-2`). -/
public theorem pqRFibonacci_succ_eq_left {R : Type*} [CommSemiring R] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (x y p q : R) (m : ℕ) :
    pqRFibonacci r x y p q m (n + 1)
      = p * x * pqRFibonacci r (p * x) (q * y) p q m n
        + q * y * pqRFibonacci r (p * x) (q ^ (m + 1) * y) p q m (n - r) := by
  rw [pqRFibonacci_eq_sum_term r x y p q m (n + 1) (n + 1) le_rfl,
    pqRFibonacci_eq_sum_term r (p * x) (q * y) p q m n (n + 1) (Nat.le_succ n),
    pqRFibonacci_eq_sum_term r (p * x) (q ^ (m + 1) * y) p q m (n - r) n (Nat.sub_le n r),
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp_rw [pqRFibonacciTerm_succ_right, pqRFibonacciTerm_zero_right r x y p q m n (by omega),
    Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  rw [add_right_comm]

end MetaMathlibExt
