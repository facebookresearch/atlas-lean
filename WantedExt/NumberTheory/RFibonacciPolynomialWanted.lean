/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.GaussianBinomial

namespace MetaMathlibExt

@[expose] public section

/-- The `r`-Fibonacci polynomial `U^{(r)}_n(x, y)`: `U_0 = 0`, `U_k = x^{k-1}` for
`1 ≤ k ≤ r`, and `U_{n+1} = x U_n + y U_{n-r}` for `n ≥ r`. These are the
initial values and recurrence displayed for `ξ_n = m^{n-1} U_n` in the paper,
at `m = 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public def rFibonacciPolynomial {R : Type*} [CommSemiring R] (r : ℕ) (x y : R) : ℕ → R
  | 0 => 0
  | n + 1 =>
    if n < r then x ^ n
    else x * rFibonacciPolynomial r x y n + y * rFibonacciPolynomial r x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- `U_0 = 0`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public theorem rFibonacciPolynomial_zero {R : Type*} [CommSemiring R] (r : ℕ) (x y : R) :
    rFibonacciPolynomial r x y 0 = 0 := by
  rw [rFibonacciPolynomial]

/-- `U_{n+1} = x^n` for `n < r`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public theorem rFibonacciPolynomial_succ_of_lt {R : Type*} [CommSemiring R] {r n : ℕ}
    (x y : R) (h : n < r) : rFibonacciPolynomial r x y (n + 1) = x ^ n := by
  rw [rFibonacciPolynomial]
  simp [h]

/-- `U_{n+1} = x U_n + y U_{n-r}` for `n ≥ r`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 4. -/
public theorem rFibonacciPolynomial_succ_of_le {R : Type*} [CommSemiring R] {r n : ℕ}
    (x y : R) (h : r ≤ n) :
    rFibonacciPolynomial r x y (n + 1)
      = x * rFibonacciPolynomial r x y n + y * rFibonacciPolynomial r x y (n - r) := by
  rw [rFibonacciPolynomial]
  simp [show ¬n < r by omega]

/-- For `r = 1` and `x = y = 1` the `r`-Fibonacci polynomials are the Fibonacci
numbers.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rFibonacciPolynomial_one_one_one :
    ∀ n, rFibonacciPolynomial 1 (1 : ℕ) 1 n = Nat.fib n
  | 0 => by rw [rFibonacciPolynomial_zero]; rfl
  | 1 => by rw [rFibonacciPolynomial_succ_of_lt _ _ (by omega)]; simp
  | n + 2 => by
    rw [rFibonacciPolynomial_succ_of_le _ _ (by omega), rFibonacciPolynomial_one_one_one (n + 1),
      show n + 1 - 1 = n by omega, rFibonacciPolynomial_one_one_one n, Nat.fib_add_two]
    ring

/-- Theorem 4: for `ξ_n = m^{n-1} U^{(r)}_n` (`r ≥ 1`) and
`P(1) = 1 - m x - m^{r+1} y ≠ 0`,
`∑_{j=1}^{n} ξ_j = (1 - ξ_{n+1} - m^{r+1} y ∑_{j=1}^{r} ξ_{n-r+j}) / P(1)`.
Terms with `n - r + j ≤ 0` vanish (`ξ_0 = 0`; the index is the truncated
`n + j - r`). The paper takes `m` a positive integer; here `m` is any element of
the field.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 4 (`integers-2025-A38-thm-4`). -/
public theorem_wanted sum_pow_mul_rFibonacciPolynomial {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (x y m : K) (hP : 1 - m * x - m ^ (r + 1) * y ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, m ^ (j - 1) * rFibonacciPolynomial r x y j
      = (1 - m ^ n * rFibonacciPolynomial r x y (n + 1)
          - m ^ (r + 1) * y * ∑ j ∈ Finset.Icc 1 r,
              m ^ (n + j - r - 1) * rFibonacciPolynomial r x y (n + j - r))
        / (1 - m * x - m ^ (r + 1) * y)

/-- Corollary 2: for `r ≥ 1` and `1 - x - y ≠ 0`,
`∑_{j=1}^{n} U_j = (1 - U_{n+1} - y ∑_{j=1}^{r} U_{n-r+j}) / (1 - x - y)`
(terms with `n - r + j ≤ 0` vanish).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 2 (`integers-2025-A38-cor-2`). -/
public theorem_wanted sum_rFibonacciPolynomial {K : Type*} [Field K] {r : ℕ} (hr : 1 ≤ r)
    (x y : K) (hP : 1 - x - y ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, rFibonacciPolynomial r x y j
      = (1 - rFibonacciPolynomial r x y (n + 1)
          - y * ∑ j ∈ Finset.Icc 1 r, rFibonacciPolynomial r x y (n + j - r))
        / (1 - x - y)

/-- Corollary 3: for `r ≥ 1` and `1 + x + (-1)^r y ≠ 0`,
`∑_{j=1}^{n} (-1)^{j-1} U_j = (1 - (-1)^n U_{n+1}
+ (-1)^r y ∑_{j=1}^{r} (-1)^{n-r+j-1} U_{n-r+j}) / (1 + x + (-1)^r y)`
(terms with `n - r + j ≤ 0` vanish).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 3 (`integers-2025-A38-cor-3`). -/
public theorem_wanted sum_neg_one_pow_mul_rFibonacciPolynomial {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (x y : K) (hP : 1 + x + (-1) ^ r * y ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (-1) ^ (j - 1) * rFibonacciPolynomial r x y j
      = (1 - (-1) ^ n * rFibonacciPolynomial r x y (n + 1)
          + (-1) ^ r * y * ∑ j ∈ Finset.Icc 1 r,
              (-1) ^ (n + j - r - 1) * rFibonacciPolynomial r x y (n + j - r))
        / (1 + x + (-1) ^ r * y)


/-- The `r`-Lucas polynomial of type `s`, `V^{(r,s)}_n(x, y)`: `V_0 = s + 1`,
`V_k = x^k` for `1 ≤ k ≤ r`, and `V_{n+1} = x V_n + y V_{n-r}` for `n ≥ r`.
The paper takes `1 ≤ s ≤ r`; the definition makes sense for every `s`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public def rLucasPolynomial {R : Type*} [CommSemiring R] (r s : ℕ) (x y : R) : ℕ → R
  | 0 => (s : R) + 1
  | n + 1 =>
    if n < r then x ^ (n + 1)
    else x * rLucasPolynomial r s x y n + y * rLucasPolynomial r s x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- `V_0 = s + 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rLucasPolynomial_zero {R : Type*} [CommSemiring R] (r s : ℕ) (x y : R) :
    rLucasPolynomial r s x y 0 = (s : R) + 1 := by
  rw [rLucasPolynomial]

/-- `V_{n+1} = x^{n+1}` for `n < r`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rLucasPolynomial_succ_of_lt {R : Type*} [CommSemiring R] {r n : ℕ} (s : ℕ)
    (x y : R) (h : n < r) : rLucasPolynomial r s x y (n + 1) = x ^ (n + 1) := by
  rw [rLucasPolynomial]
  simp [h]

/-- `V_{n+1} = x V_n + y V_{n-r}` for `n ≥ r`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 1. -/
public theorem rLucasPolynomial_succ_of_le {R : Type*} [CommSemiring R] {r n : ℕ} (s : ℕ)
    (x y : R) (h : r ≤ n) :
    rLucasPolynomial r s x y (n + 1)
      = x * rLucasPolynomial r s x y n + y * rLucasPolynomial r s x y (n - r) := by
  rw [rLucasPolynomial]
  simp [show ¬n < r by omega]

/-- Theorem 1 (i), `U` part (Binet formula, distinct zeros): if
`t^{r+1} - x t^r - y = ∏_k (t - α_k)` with pairwise distinct `α_k`, then
`U^{(r)}_{n+1} = ∑_k α_k^{n+1} / ((r+1) α_k - r x)`. The paper's hypothesis
`y ≠ (-1/r)(rx/(r+1))^{r+1}` is replaced by the distinctness of the zeros it is
meant to guarantee (it does not exclude the multiple zero `0` when `y = 0`,
`r ≥ 2`).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 1 (`integers-2025-A38-thm-1`). -/
public theorem_wanted rFibonacciPolynomial_eq_sum_roots {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (x y : K) (α : Fin (r + 1) → K) (hα : Function.Injective α)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C x * Polynomial.X ^ r - Polynomial.C y
      : Polynomial K) = ∏ k, (Polynomial.X - Polynomial.C (α k))) (n : ℕ) :
    rFibonacciPolynomial r x y (n + 1)
      = ∑ k, α k ^ (n + 1) / ((r + 1) * α k - r * x)

/-- Theorem 1 (i), `V` part (Binet formula, distinct zeros): under the same
hypotheses, `V^{(r,s)}_n = ∑_k α_k^n ((s+1) α_k - s x) / ((r+1) α_k - r x)` for
every `n ≥ 0`. The paper takes `1 ≤ s ≤ r`; the identity holds for every `s`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 1 (`integers-2025-A38-thm-1`). -/
public theorem_wanted rLucasPolynomial_eq_sum_roots {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (s : ℕ) (x y : K) (α : Fin (r + 1) → K) (hα : Function.Injective α)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C x * Polynomial.X ^ r - Polynomial.C y
      : Polynomial K) = ∏ k, (Polynomial.X - Polynomial.C (α k))) (n : ℕ) :
    rLucasPolynomial r s x y n
      = ∑ k, α k ^ n * ((s + 1) * α k - s * x) / ((r + 1) * α k - r * x)

/-- Theorem 1 (ii), `U` part (Binet formula, one double zero): if
`t^{r+1} - x t^r - y = (t - α)^2 P̃(t)` with `P̃(t) = ∏_k (t - β_k)`, the `β_k`
pairwise distinct and different from `α`, then
`U^{(r)}_{n+1} = α^{n+r-1}/P̃(α) · ((n + r) - α P̃'(α)/P̃(α))
+ ∑_k β_k^{n+1} / ((r+1) β_k - r x)`. The paper's hypothesis
`y = (-1/r)(rx/(r+1))^{r+1}` (which makes `α = rx/(r+1)` the double zero) is
replaced by the factorization it yields.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 1 (`integers-2025-A38-thm-1`). -/
public theorem_wanted rFibonacciPolynomial_eq_of_double_root {K : Type*} [Field K]
    [CharZero K] {r : ℕ} (hr : 1 ≤ r) (x y α : K) (β : Fin (r - 1) → K)
    (hβ : Function.Injective β) (hβα : ∀ k, β k ≠ α)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C x * Polynomial.X ^ r - Polynomial.C y
      : Polynomial K) = (Polynomial.X - Polynomial.C α) ^ 2 *
        ∏ k, (Polynomial.X - Polynomial.C (β k))) (n : ℕ) :
    rFibonacciPolynomial r x y (n + 1)
      = α ^ (n + r - 1) / (∏ k, (Polynomial.X - Polynomial.C (β k))).eval α *
          ((n + r : K) - α * (Polynomial.derivative
              (∏ k, (Polynomial.X - Polynomial.C (β k)))).eval α /
            (∏ k, (Polynomial.X - Polynomial.C (β k))).eval α)
        + ∑ k, β k ^ (n + 1) / ((r + 1) * β k - r * x)

/-- Theorem 1 (ii), `V` part (Binet formula, one double zero): under the same
hypotheses, `V^{(r,s)}_n = α^{n+r-1}/P̃(α) · (n (r-s)/r + (r + s/r)
- α ((r-s)/r) P̃'(α)/P̃(α)) + ∑_k β_k^n ((s+1) β_k - s x) / ((r+1) β_k - r x)`.
The paper takes `1 ≤ s ≤ r`; the identity holds for every `s`. The hypothesis `α ≠ 0` is
added: for `r = 2`, `y = 0` the factorization `t²(t - x)` has `α = 0` and the formula fails at
`n = 0` (`x = s = 1`: `V_0 = 2`, right side `1`). In the paper's setting `α = rx/(r+1)` with
`x ≠ 0`, so `α ≠ 0`; the only other `α = 0` case, `r = 1`, `x = y = 0`, is dropped.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 1 (`integers-2025-A38-thm-1`). -/
public theorem_wanted rLucasPolynomial_eq_of_double_root {K : Type*} [Field K]
    [CharZero K] {r : ℕ} (hr : 1 ≤ r) (s : ℕ) (x y α : K) (hα : α ≠ 0) (β : Fin (r - 1) → K)
    (hβ : Function.Injective β) (hβα : ∀ k, β k ≠ α)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C x * Polynomial.X ^ r - Polynomial.C y
      : Polynomial K) = (Polynomial.X - Polynomial.C α) ^ 2 *
        ∏ k, (Polynomial.X - Polynomial.C (β k))) (n : ℕ) :
    rLucasPolynomial r s x y n
      = α ^ (n + r - 1) / (∏ k, (Polynomial.X - Polynomial.C (β k))).eval α *
          (n * ((r - s) / r) + (r + s / r) - α * ((r - s) / r) *
            (Polynomial.derivative (∏ k, (Polynomial.X - Polynomial.C (β k)))).eval α /
              (∏ k, (Polynomial.X - Polynomial.C (β k))).eval α)
        + ∑ k, β k ^ n * ((s + 1) * β k - s * x) / ((r + 1) * β k - r * x)

/-- The `(p, q)`-binomial coefficient `[n, k]_{p,q}`, defined by the paper's
Pascal recursion (3): `[n, 0] = 1`, `[0, k+1] = 0`,
`[n+1, k+1] = p^{n-k} [n, k] + q^{k+1} [n, k+1]`. Where the `(p,q)`-factorials are
invertible it equals `[n]_{p,q}! / ([k]_{p,q}! [n-k]_{p,q}!)`, the paper's
definition; at `p = 1` it is the Gaussian binomial `MathlibExt.gaussBinom q`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3, Equation (3). -/
public def pqBinomial {R : Type*} [CommSemiring R] (p q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => p ^ (n - k) * pqBinomial p q n k + q ^ (k + 1) * pqBinomial p q n (k + 1)

/-- `[n, 0]_{p,q} = 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3. -/
public theorem pqBinomial_zero_right {R : Type*} [CommSemiring R] (p q : R) (n : ℕ) :
    pqBinomial p q n 0 = 1 := by
  cases n <;> rfl

/-- `[0, k+1]_{p,q} = 0`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3. -/
public theorem pqBinomial_zero_succ {R : Type*} [CommSemiring R] (p q : R) (k : ℕ) :
    pqBinomial p q 0 (k + 1) = 0 := rfl

/-- The Pascal recursion (3): `[n+1, k+1] = p^{n-k} [n, k] + q^{k+1} [n, k+1]`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Section 3, Equation (3). -/
public theorem pqBinomial_succ_succ {R : Type*} [CommSemiring R] (p q : R) (n k : ℕ) :
    pqBinomial p q (n + 1) (k + 1)
      = p ^ (n - k) * pqBinomial p q n k + q ^ (k + 1) * pqBinomial p q n (k + 1) := rfl

/-- At `p = 1` the `(p, q)`-binomial is the Gaussian binomial coefficient.

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

/-- Definition 1: the `(p, q)`-analogue of the `r`-Fibonacci polynomial,
`U_0 = 0` and, for all `n ≥ 0`,
`U_{n+1}(x, y, p, q, m) = ∑_{k=0}^{⌊n/(r+1)⌋} p^{C(n+1-(r+1)k, 2)} q^{C(k+1, 2) + m C(k, 2)}
[n - rk, k]_{p,q} x^{n-(r+1)k} y^k`. The paper's extra clause
`U_j = p^{C(j+1,2)} x^{j-1}` (`1 ≤ j ≤ r`) contradicts this sum (which gives
`p^{C(j,2)} x^{j-1}`, e.g. `U_2 = p x` for `r = 2`, not `p^3 x`); the sum, which
Theorem 2 requires, is used.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 1. -/
public def pqRFibonacci {R : Type*} [CommSemiring R] (r : ℕ) (x y p q : R) (m : ℕ) : ℕ → R
  | 0 => 0
  | n + 1 => ∑ k ∈ Finset.range (n / (r + 1) + 1),
      p ^ (n + 1 - (r + 1) * k).choose 2 * q ^ ((k + 1).choose 2 + m * k.choose 2) *
        pqBinomial p q (n - r * k) k * x ^ (n - (r + 1) * k) * y ^ k

/-- `U_0 = 0` for the `(p, q)`-analogue.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 1. -/
public theorem pqRFibonacci_zero {R : Type*} [CommSemiring R] (r : ℕ) (x y p q : R)
    (m : ℕ) : pqRFibonacci r x y p q m 0 = 0 := rfl

/-- At `p = q = 1`, `m = 0`, the first values agree with `U^{(r)}`: `U_1 = 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 1. -/
public theorem pqRFibonacci_one {R : Type*} [CommSemiring R] (r : ℕ) (x y p q : R)
    (m : ℕ) : pqRFibonacci r x y p q m 1 = 1 := by
  simp [pqRFibonacci, pqBinomial_zero_right]

/-- Theorem 2, Equation (4): for `n ≥ r`,
`U_{n+1}(x, y) = p x U_n(px, qy) + q y U_{n-r}(px, q^{m+1} y)` (parameters `p, q, m`
unchanged).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 2, Equation (4) (`integers-2025-A38-thm-2`). -/
public theorem_wanted pqRFibonacci_succ_eq_left {R : Type*} [CommSemiring R] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (x y p q : R) (m : ℕ) :
    pqRFibonacci r x y p q m (n + 1)
      = p * x * pqRFibonacci r (p * x) (q * y) p q m n
        + q * y * pqRFibonacci r (p * x) (q ^ (m + 1) * y) p q m (n - r)

/-- Theorem 2, Equation (5): for `n ≥ r`,
`U_{n+1}(x, y) = p x U_n(px, py) + q y U_{n-r}(qx, q^{m+1} y)`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 2, Equation (5) (`integers-2025-A38-thm-2`). -/
public theorem_wanted pqRFibonacci_succ_eq_right {R : Type*} [CommSemiring R] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (x y p q : R) (m : ℕ) :
    pqRFibonacci r x y p q m (n + 1)
      = p * x * pqRFibonacci r (p * x) (p * y) p q m n
        + q * y * pqRFibonacci r (q * x) (q ^ (m + 1) * y) p q m (n - r)

/-- Definition 2, first kind: the `(p, q)`-analogue `V^{(r,s)}_n(x, y, p, q, m)` of the
`r`-Lucas polynomial of type `s`, `V_0 = s + 1` and for `n ≥ 1`
`V_n = ∑_{k=0}^{⌊n/(r+1)⌋} p^{C(n-(r+1)k, 2)} q^{(m+1) C(k, 2)}
([n - rk, k]_{p,q} + s p^{n-(r+1)k} [n - rk - 1, k - 1]_{p,q}) x^{n-(r+1)k} y^k`
(the `s`-term is absent for `k = 0`). The paper writes the bracket as
`[n - rk, k]_{p,q} (1 + s p^{n-(r+1)k} [k]_{p,q} / [n - rk]_{p,q})`; the
division-free form is the first step of the paper's proof of Theorem 3 and agrees
with it whenever `[n - rk]_{p,q} ≠ 0`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 2. -/
public def pqRLucas {R : Type*} [CommSemiring R] (r s : ℕ) (x y p q : R) (m : ℕ) : ℕ → R
  | 0 => (s : R) + 1
  | n + 1 => ∑ k ∈ Finset.range ((n + 1) / (r + 1) + 1),
      p ^ (n + 1 - (r + 1) * k).choose 2 * q ^ ((m + 1) * k.choose 2) *
        (pqBinomial p q (n + 1 - r * k) k +
          if k = 0 then 0 else s * p ^ (n + 1 - (r + 1) * k) * pqBinomial p q (n - r * k) (k - 1)) *
        x ^ (n + 1 - (r + 1) * k) * y ^ k

/-- `V_0 = s + 1` (first kind).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 2. -/
public theorem pqRLucas_zero {R : Type*} [CommSemiring R] (r s : ℕ) (x y p q : R) (m : ℕ) :
    pqRLucas r s x y p q m 0 = (s : R) + 1 := rfl

/-- Definition 2, second kind: `𝕍^{(r,s)}_0 = s + 1` and for `n ≥ 1`
`𝕍_n = ∑_{k=0}^{⌊n/(r+1)⌋} p^{C(n-(r+1)k, 2)} q^{C(k+1, 2) + m C(k, 2)} p^{-k}
([n - rk, k]_{p,q} + s q^{n-(r+1)k} [n - rk - 1, k - 1]_{p,q}) x^{n-(r+1)k} y^k`,
the division-free form of the paper's
`[n - rk, k]_{p,q} (1 + s q^{n-(r+1)k} [k]_{p,q} / [n - rk]_{p,q})` (see `pqRLucas`).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 2. -/
public def pqRLucasSecond {K : Type*} [Field K] (r s : ℕ) (x y p q : K) (m : ℕ) : ℕ → K
  | 0 => (s : K) + 1
  | n + 1 => ∑ k ∈ Finset.range ((n + 1) / (r + 1) + 1),
      p ^ (n + 1 - (r + 1) * k).choose 2 * q ^ ((k + 1).choose 2 + m * k.choose 2) / p ^ k *
        (pqBinomial p q (n + 1 - r * k) k +
          if k = 0 then 0 else s * q ^ (n + 1 - (r + 1) * k) * pqBinomial p q (n - r * k) (k - 1)) *
        x ^ (n + 1 - (r + 1) * k) * y ^ k

/-- `𝕍_0 = s + 1` (second kind).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 2. -/
public theorem pqRLucasSecond_zero {K : Type*} [Field K] (r s : ℕ) (x y p q : K) (m : ℕ) :
    pqRLucasSecond r s x y p q m 0 = (s : K) + 1 := rfl

/-- Theorem 3.1, first kind: for `n ≥ r`,
`V^{(r,s)}_n(x, y) = U_{n+1}(x/p, y/q) + s y U_{n-r}(x, y q^m)`. The paper takes
positive `s`; the identity holds for every `s ∈ ℕ`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 1 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucas_eq_pqRFibonacci_add {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (s : ℕ) (x y p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (m : ℕ) :
    pqRLucas r s x y p q m n
      = pqRFibonacci r (x / p) (y / q) p q m (n + 1)
        + s * y * pqRFibonacci r x (y * q ^ m) p q m (n - r)

/-- Theorem 3.1, second kind: for `n ≥ r`,
`𝕍^{(r,s)}_n(x, y) = U_{n+1}(x/p, y/p) + s y (q/p)^{n-r} U_{n-r}(x, y p^r q^{m-r})`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 1 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucasSecond_eq_pqRFibonacci_add {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (s : ℕ) (x y p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (m : ℕ) :
    pqRLucasSecond r s x y p q m n
      = pqRFibonacci r (x / p) (y / p) p q m (n + 1)
        + s * y * (q / p) ^ (n - r) * pqRFibonacci r x (y * p ^ r * q ^ m / q ^ r) p q m (n - r)

/-- Theorem 3.2, first kind: for all `n ≥ 0`,
`V^{(r,s)}_n(x, y) = (s + 1) U_{n+1}(x/p, y/q) - s x U_n(x, y)`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 2 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucas_eq_succ_mul_sub {K : Type*} [Field K] {r : ℕ} (hr : 1 ≤ r)
    (s : ℕ) (x y p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (m n : ℕ) :
    pqRLucas r s x y p q m n
      = (s + 1) * pqRFibonacci r (x / p) (y / q) p q m (n + 1)
        - s * x * pqRFibonacci r x y p q m n

/-- Theorem 3.2, second kind: for all `n ≥ 0`,
`𝕍^{(r,s)}_n(x, y) = (s + 1) U_{n+1}(x/p, y/p) - s x U_n(x, y)`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 2 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucasSecond_eq_succ_mul_sub {K : Type*} [Field K] {r : ℕ}
    (hr : 1 ≤ r) (s : ℕ) (x y p q : K) (hp : p ≠ 0) (m n : ℕ) :
    pqRLucasSecond r s x y p q m n
      = (s + 1) * pqRFibonacci r (x / p) (y / p) p q m (n + 1)
        - s * x * pqRFibonacci r x y p q m n

/-- Theorem 3.3, first kind: for `n ≥ r`,
`V^{(r,s)}_n(x, y) = x U_n(x, y) + (1 + s) y U_{n-r}(x, y q^m)`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 3 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucas_eq_mul_add {R : Type*} [CommSemiring R] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (s : ℕ) (x y p q : R) (m : ℕ) :
    pqRLucas r s x y p q m n
      = x * pqRFibonacci r x y p q m n
        + (1 + s) * y * pqRFibonacci r x (y * q ^ m) p q m (n - r)

/-- Theorem 3.3, second kind: for `n ≥ r`,
`𝕍^{(r,s)}_n(x, y) = x U_n(x, y) + (1 + s) (q/p)^{n-r} y U_{n-r}(x, y p^r q^{m-r})`
(the paper's argument list `(x, y p^r q^{m-r}, m)` drops `p, q`; they are unchanged).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 3, part 3 (`integers-2025-A38-thm-3`). -/
public theorem_wanted pqRLucasSecond_eq_mul_add {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n) (s : ℕ) (x y p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (m : ℕ) :
    pqRLucasSecond r s x y p q m n
      = x * pqRFibonacci r x y p q m n
        + (1 + s) * (q / p) ^ (n - r) * y *
            pqRFibonacci r x (y * p ^ r * q ^ m / q ^ r) p q m (n - r)

/-- Theorem 5: for `η_n = m^n V^{(r,s)}_n`, `r ≥ 1`, `n ≥ r - 1` and
`P(1) = 1 - m x - m^{r+1} y ≠ 0`,
`∑_{j=1}^{n} η_j = (1 + s m^{r+1} y - η_{n+1} - m^{r+1} y ∑_{j=1}^{r} η_{n-r+j}) / P(1) - 1`.
The paper takes `m` a positive integer (here any field element) and states no
range for `n`; for `n < r - 1` the right side involves `η` at negative indices.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 5 (`integers-2025-A38-thm-5`). -/
public theorem_wanted sum_pow_mul_rLucasPolynomial {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n + 1) (s : ℕ) (x y m : K) (hP : 1 - m * x - m ^ (r + 1) * y ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, m ^ j * rLucasPolynomial r s x y j
      = (1 + s * m ^ (r + 1) * y - m ^ (n + 1) * rLucasPolynomial r s x y (n + 1)
          - m ^ (r + 1) * y * ∑ j ∈ Finset.Icc 1 r,
              m ^ (n + j - r) * rLucasPolynomial r s x y (n + j - r))
        / (1 - m * x - m ^ (r + 1) * y) - 1

/-- Corollary 4: for `r ≥ 1`, `n ≥ 1`, `n ≥ r - 1` and `1 - x - y ≠ 0`,
`∑_{j=1}^{n} V_j = (1 + s y - V_{n+1} - y ∑_{j=1}^{r} V_{n-r+j}) / (1 - x - y) - 1`.
The paper states `n ≥ 1`; for `n < r - 1` the right side involves `V` at negative
indices.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 4 (`integers-2025-A38-cor-4`). -/
public theorem_wanted sum_rLucasPolynomial {K : Type*} [Field K] {r n : ℕ} (hr : 1 ≤ r)
    (hn1 : 1 ≤ n) (hn : r ≤ n + 1) (s : ℕ) (x y : K) (hP : 1 - x - y ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, rLucasPolynomial r s x y j
      = (1 + s * y - rLucasPolynomial r s x y (n + 1)
          - y * ∑ j ∈ Finset.Icc 1 r, rLucasPolynomial r s x y (n + j - r))
        / (1 - x - y) - 1

/-- Corollary 5: for `r ≥ 1`, `n ≥ r - 1` and `1 + x + (-1)^r y ≠ 0`,
`∑_{j=1}^{n} (-1)^j V_j = (1 - (-1)^r s y + (-1)^n V_{n+1}
+ (-1)^r y ∑_{j=1}^{r} (-1)^{n-r+j} V_{n-r+j}) / (1 + x + (-1)^r y) - 1`.
For `n < r - 1` the right side involves `V` at negative indices.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Corollary 5 (`integers-2025-A38-cor-5`). -/
public theorem_wanted sum_neg_one_pow_mul_rLucasPolynomial {K : Type*} [Field K] {r n : ℕ}
    (hr : 1 ≤ r) (hn : r ≤ n + 1) (s : ℕ) (x y : K) (hP : 1 + x + (-1) ^ r * y ≠ 0) :
    ∑ j ∈ Finset.Icc 1 n, (-1) ^ j * rLucasPolynomial r s x y j
      = (1 - (-1) ^ r * s * y + (-1) ^ n * rLucasPolynomial r s x y (n + 1)
          + (-1) ^ r * y * ∑ j ∈ Finset.Icc 1 r,
              (-1) ^ (n + j - r) * rLucasPolynomial r s x y (n + j - r))
        / (1 + x + (-1) ^ r * y) - 1

/-- Definition 3: the `(-r)`-Fibonacci polynomial `U^{(-r)}_n(x, y)` over a commutative
ring with `y` a unit: `U_0 = 0`, `U_1 = 1`, `U_2 = ⋯ = U_r = 0`, and
`U_{n+1} = y^{-1} U_{n-r+1} - y^{-1} x U_{n-r}` for `n ≥ r`. The paper takes `r ≥ 2`;
the guard `r = 0` only makes the definition total.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public def negRFibonacci {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) : ℕ → A
  | 0 => 0
  | n + 1 =>
    if n = 0 then 1
    else if n < r ∨ r = 0 then 0
    else (↑y⁻¹ : A) * negRFibonacci r x y (n - r + 1) - ↑y⁻¹ * x * negRFibonacci r x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- `U^{(-r)}_0 = 0`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public theorem negRFibonacci_zero {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) :
    negRFibonacci r x y 0 = 0 := by
  rw [negRFibonacci]

/-- `U^{(-r)}_1 = 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public theorem negRFibonacci_one {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) :
    negRFibonacci r x y 1 = 1 := by
  rw [negRFibonacci]
  simp

/-- `U^{(-r)}_{n+1} = 0` for `1 ≤ n < r`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public theorem negRFibonacci_succ_of_lt {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (h1 : 1 ≤ n) (h : n < r) : negRFibonacci r x y (n + 1) = 0 := by
  rw [negRFibonacci]
  simp [show n ≠ 0 by omega, h]

/-- The recurrence (7): `U_{n+1} = y^{-1} U_{n-r+1} - y^{-1} x U_{n-r}` for `n ≥ r ≥ 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3, Equation (7). -/
public theorem negRFibonacci_succ_of_le {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (hr : 1 ≤ r) (h : r ≤ n) :
    negRFibonacci r x y (n + 1)
      = ↑y⁻¹ * negRFibonacci r x y (n - r + 1) - ↑y⁻¹ * x * negRFibonacci r x y (n - r) := by
  rw [negRFibonacci]
  simp [show n ≠ 0 by omega, show ¬n < r by omega, show r ≠ 0 by omega]

/-- Definition 4: the companion sequence `V^{(-r)}_n(x, y)`: `V_0 = r + 1`,
`V_1 = ⋯ = V_{r-1} = 0`, `V_r = r y^{-1}`, and
`V_{n+1} = y^{-1} V_{n-r+1} - y^{-1} x V_{n-r}` for `n ≥ r`. The paper takes `r ≥ 2`;
the guard `r = 0` only makes the definition total.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public def negRLucas {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) : ℕ → A
  | 0 => (r : A) + 1
  | n + 1 =>
    if r = 0 ∨ n + 1 < r then 0
    else if n + 1 = r then (r : A) * ↑y⁻¹
    else (↑y⁻¹ : A) * negRLucas r x y (n - r + 1) - ↑y⁻¹ * x * negRLucas r x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- `V^{(-r)}_0 = r + 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_zero {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) :
    negRLucas r x y 0 = (r : A) + 1 := by
  rw [negRLucas]

/-- `V^{(-r)}_n = 0` for `1 ≤ n < r`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_succ_of_lt {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (h : n + 1 < r) : negRLucas r x y (n + 1) = 0 := by
  rw [negRLucas]
  simp [h]

/-- `V^{(-r)}_r = r y^{-1}` for `r ≥ 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_self {A : Type*} [CommRing A] {r : ℕ} (x : A) (y : Aˣ)
    (hr : 1 ≤ r) : negRLucas r x y r = (r : A) * ↑y⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [negRLucas]
  simp

/-- The recurrence `V_{n+1} = y^{-1} V_{n-r+1} - y^{-1} x V_{n-r}` for `n ≥ r ≥ 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_succ_of_le {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (hr : 1 ≤ r) (h : r ≤ n) :
    negRLucas r x y (n + 1)
      = ↑y⁻¹ * negRLucas r x y (n - r + 1) - ↑y⁻¹ * x * negRLucas r x y (n - r) := by
  rw [negRLucas]
  simp [show r ≠ 0 by omega, show ¬n + 1 < r by omega, show n + 1 ≠ r by omega]

/-- Theorem 6, first form: for `r ≥ 2`,
`U^{(-r)}_{n+1} = ∑_{k=0}^{⌊n/r⌋} C(k, n - rk) y^{-k} (-x)^{n-rk}` (the terms with
`k < ⌊n/(r+1)⌋` vanish). The paper states `n ≥ 1` and `x` a unit; the identity holds
for `n = 0` and every `x`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 6 (`integers-2025-A38-thm-6`). -/
public theorem_wanted negRFibonacci_succ_eq_sum {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) (n : ℕ) :
    negRFibonacci r x y (n + 1)
      = ∑ k ∈ Finset.range (n / r + 1),
          ((k.choose (n - r * k) : ℕ) : A) * (↑y⁻¹ : A) ^ k * (-x) ^ (n - r * k)

/-- Theorem 6, second form: for `r ≥ 2`,
`U^{(-r)}_{n+1} = ∑ C((n-k)/r, k) y^{-(n-k)/r} (-x)^k` over `0 ≤ k ≤ ⌊n/r⌋` with
`r ∣ n - k`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 6 (`integers-2025-A38-thm-6`). -/
public theorem_wanted negRFibonacci_succ_eq_sum' {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) (n : ℕ) :
    negRFibonacci r x y (n + 1)
      = ∑ k ∈ (Finset.range (n / r + 1)).filter (fun k => r ∣ n - k),
          ((((n - k) / r).choose k : ℕ) : A) * (↑y⁻¹ : A) ^ ((n - k) / r) * (-x) ^ k

/-- Proposition 1: for `r ≥ 2` and `n ≥ r`,
`V^{(-r)}_n = r U^{(-r)}_{n+1} - x y^{-1} U^{(-r)}_{n-r}`. The paper takes `x` a unit;
the identity holds for every `x`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Proposition 1, Equation (8) (`integers-2025-A38-prop-1`). -/
public theorem_wanted negRLucas_eq {A : Type*} [CommRing A] {r n : ℕ} (hr : 2 ≤ r)
    (hn : r ≤ n) (x : A) (y : Aˣ) :
    negRLucas r x y n = r * negRFibonacci r x y (n + 1) - x * ↑y⁻¹ * negRFibonacci r x y (n - r)

/-- Theorem 7, first form: for `r ≥ 2` and `n ≥ 1`,
`V^{(-r)}_n = ∑_k n/(n - rk) C(k - 1, n - 1 - rk) y^{-k} (-x)^{n-rk} + r y^{-n/r} [r ∣ n]`,
the sum over `1 ≤ k` with `rk < n`. The paper's range `⌊n/(r+1)⌋ ≤ k ≤ ⌊n/r⌋` also
admits `k = n/r` (division by zero; that term is the bracket term) and, for `n ≤ r`,
`k = 0`, whose term `C(-1, n-1)` must be read as `0` (with `C(-1, j) = (-1)^j`,
`r = 2`, `n = 1` gives `-x` instead of `V_1 = 0`); both are excluded. Stated over a
field of characteristic zero for the quotient `n/(n - rk)`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 7 (`integers-2025-A38-thm-7`). -/
public theorem_wanted negRLucas_eq_sum {K : Type*} [Field K] [CharZero K] {r n : ℕ}
    (hr : 2 ≤ r) (hn : 1 ≤ n) (x : K) (y : Kˣ) :
    negRLucas r x y n
      = ∑ k ∈ (Finset.Icc 1 (n / r)).filter (fun k => r * k < n),
          (n : K) / ((n : K) - ((r * k : ℕ) : K)) * ((k - 1).choose (n - 1 - r * k) : K) *
            (↑y⁻¹ : K) ^ k * (-x) ^ (n - r * k)
        + if r ∣ n then (r : K) * (↑y⁻¹ : K) ^ (n / r) else 0

/-- Theorem 7, second form: for `r ≥ 2` and `n ≥ 1`,
`V^{(-r)}_n = ∑_k n/(k+1) C((n-1-r-k)/r, k) y^{-(n-1-k)/r} (-x)^{k+1} + r y^{-n/r} [r ∣ n]`,
the sum over `0 ≤ k ≤ ⌊n/(r+1)⌋ - 1` with `r ∣ n - k - 1`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 7 (`integers-2025-A38-thm-7`). -/
public theorem_wanted negRLucas_eq_sum' {K : Type*} [Field K] [CharZero K] {r n : ℕ}
    (hr : 2 ≤ r) (hn : 1 ≤ n) (x : K) (y : Kˣ) :
    negRLucas r x y n
      = ∑ k ∈ (Finset.range (n / (r + 1))).filter (fun k => r ∣ n - k - 1),
          (n : K) / (k + 1) * (((n - 1 - r - k) / r).choose k : K) *
            (↑y⁻¹ : K) ^ ((n - 1 - k) / r) * (-x) ^ (k + 1)
        + if r ∣ n then (r : K) * (↑y⁻¹ : K) ^ (n / r) else 0

/-- Theorem 8, `U` part, as an identity of formal power series: for `r ≥ 2`,
`(1 - y^{-1} z^r + x y^{-1} z^{r+1}) ∑_{n ≥ 0} U^{(-r)}_{n+1} z^n = 1`. The paper
states it for `z ∈ ℂ`; convergence is not part of this statement.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 8 (`integers-2025-A38-thm-8`). -/
public theorem_wanted negRFibonacci_generatingFunction {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) :
    (1 - PowerSeries.C (↑y⁻¹ : A) * PowerSeries.X ^ r
        + PowerSeries.C (x * ↑y⁻¹) * PowerSeries.X ^ (r + 1)) *
      PowerSeries.mk (fun n => negRFibonacci r x y (n + 1)) = 1

/-- Theorem 8, `V` part, as an identity of formal power series: for `r ≥ 2`,
`(1 - y^{-1} z^r + x y^{-1} z^{r+1}) ∑_{n ≥ 0} V^{(-r)}_n z^n = r + 1 - y^{-1} z^r`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 8 (`integers-2025-A38-thm-8`). -/
public theorem_wanted negRLucas_generatingFunction {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) :
    (1 - PowerSeries.C (↑y⁻¹ : A) * PowerSeries.X ^ r
        + PowerSeries.C (x * ↑y⁻¹) * PowerSeries.X ^ (r + 1)) *
      PowerSeries.mk (fun n => negRLucas r x y n)
      = PowerSeries.C ((r : A) + 1) - PowerSeries.C (↑y⁻¹ : A) * PowerSeries.X ^ r

/-- Lemma 1, corrected: for `r ≥ 1`, `y ≠ 0` and `(r+1)^{r+1} x^r y ≠ r^r`, the
polynomial `t^{r+1} - y^{-1} t + x y^{-1}` has no multiple zeros. The printed
hypothesis `x ≠ (r/(r+1)) ((r+1) y)^{-1/r}` names one `r`-th root only and is
insufficient: `r = 2`, `y = 1/3`, `x = -2/3` satisfies it
(`(2/3)·1^{-1/2} = 2/3`), yet `t^3 - 3t - 2 = (t + 1)^2 (t - 2)`. The paper's proof
shows a multiple zero `β` forces `x = rβ/(r+1)` with `β^r = 1/((r+1)y)`, i.e.
`(r+1)^{r+1} x^r y = r^r`, the branch-free condition used here.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Lemma 1 (`integers-2025-A38-lem-1`). -/
public theorem_wanted separable_negRFibonacci_charPoly {K : Type*} [Field K] [CharZero K]
    {r : ℕ} (hr : 1 ≤ r) (x : K) (y : Kˣ)
    (h : ((r : K) + 1) ^ (r + 1) * x ^ r * y ≠ (r : K) ^ r) :
    (Polynomial.X ^ (r + 1) - Polynomial.C (↑y⁻¹ : K) * Polynomial.X
      + Polynomial.C (x * ↑y⁻¹) : Polynomial K).Separable

/-- Theorem 9, `U` part (Binet formula): for `r ≥ 2`, if
`t^{r+1} - y^{-1} t + x y^{-1} = ∏_k (t - β_k)` with pairwise distinct `β_k`, then
`U^{(-r)}_{n+1} = ∑_k β_k^{n+r+1} / (r β_k^{r+1} - x y^{-1})`. The paper's hypothesis
`x ≠ (r/(r+1))((r+1)y)^{-1/r}` is replaced by the distinctness of the zeros (see
`separable_negRFibonacci_charPoly`).

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 9 (`integers-2025-A38-thm-9`). -/
public theorem_wanted negRFibonacci_eq_sum_roots {K : Type*} [Field K] {r : ℕ} (hr : 2 ≤ r)
    (x : K) (y : Kˣ) (β : Fin (r + 1) → K) (hβ : Function.Injective β)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C (↑y⁻¹ : K) * Polynomial.X
      + Polynomial.C (x * ↑y⁻¹) : Polynomial K) = ∏ k, (Polynomial.X - Polynomial.C (β k)))
    (n : ℕ) :
    negRFibonacci r x y (n + 1) = ∑ k, β k ^ (n + r + 1) / (r * β k ^ (r + 1) - x * ↑y⁻¹)

/-- Theorem 9, `V` part (Binet formula): under the same hypotheses,
`V^{(-r)}_n = ∑_k β_k^n` for every `n ≥ 0`.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 9 (`integers-2025-A38-thm-9`). -/
public theorem_wanted negRLucas_eq_sum_roots {K : Type*} [Field K] {r : ℕ} (hr : 2 ≤ r)
    (x : K) (y : Kˣ) (β : Fin (r + 1) → K) (hβ : Function.Injective β)
    (hP : (Polynomial.X ^ (r + 1) - Polynomial.C (↑y⁻¹ : K) * Polynomial.X
      + Polynomial.C (x * ↑y⁻¹) : Polynomial K) = ∏ k, (Polynomial.X - Polynomial.C (β k)))
    (n : ℕ) :
    negRLucas r x y n = ∑ k, β k ^ n

end

end MetaMathlibExt
