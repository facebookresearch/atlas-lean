/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The equation `Σ_{j=1}^k j U_j^p = U_n^q` for Lucas sequences

Statements from Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun,
*Extension of the Equation `Σ_{j=1}^k j F_j^p = F_n^q` to a Family of Lucas Sequences*, The
Fibonacci Quarterly 62 (2024), no. 3 (primary text: arXiv:2607.09105).

`U_n(x, y)` and `V_n(x, y)` are `lucasU P n` and `lucasV P n` with `x = P.p`, `y = P.q` (so
`y ≠ 0`); `D = x² - 4y` and `α = (x + √D)/2`.
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Powers of a root of the Lucas characteristic polynomial.** Let $x$ and $y \neq 0$ be
integers and let $(U_n)$ be the Lucas sequence with parameters $(x, y)$, given by $U_0 = 0$,
$U_1 = 1$ and $U_{n+2} = x U_{n+1} - y U_n$. If $\alpha$ is a complex number with
$\alpha^2 - x\alpha + y = 0$, then $\alpha^n = \alpha U_n - y U_{n-1}$ for every $n \geq 1$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (i), (ii) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasU_root_pow (P : LucasSequenceParams) {α : ℂ}
    (hα : α ^ 2 - P.p * α + P.q = 0) {n : ℕ} (hn : 1 ≤ n) :
    α ^ n = α * lucasU P n - P.q * lucasU P (n - 1)

/-- **The companion Lucas sequence in terms of the fundamental one.** Let $x$ and $y \neq 0$ be
integers and let $(U_n)$ and $(V_n)$ be the Lucas sequences with parameters $(x, y)$, given by
$U_0 = 0$, $U_1 = 1$, $V_0 = 2$, $V_1 = x$ and $W_{n+2} = x W_{n+1} - y W_n$ for $W = U, V$.
Then $V_n = U_{n+1} - y U_{n-1}$ for every $n \geq 1$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (iii) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasV_eq_lucasU_succ_sub (P : LucasSequenceParams) {n : ℕ} (hn : 1 ≤ n) :
    lucasV P n = lucasU P (n + 1) - P.q * lucasU P (n - 1)

/-- **Addition formula for the Lucas sequence $U$.** Let $x$ and $y \neq 0$ be integers and let
$(U_n)$ and $(V_n)$ be the Lucas sequences with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$,
$V_0 = 2$, $V_1 = x$ and $W_{n+2} = x W_{n+1} - y W_n$ for $W = U, V$. Then for all natural
numbers $n \leq m$, $U_{m+n} = U_m V_n - y^n U_{m-n}$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (iv) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasU_add_eq_mul_lucasV_sub (P : LucasSequenceParams) {m n : ℕ}
    (hnm : n ≤ m) :
    lucasU P (m + n) = lucasU P m * lucasV P n - P.q ^ n * lucasU P (m - n)

/-- **Square of the companion Lucas sequence.** Let $x$ and $y \neq 0$ be integers and let
$(U_n)$ and $(V_n)$ be the Lucas sequences with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$,
$V_0 = 2$, $V_1 = x$ and $W_{n+2} = x W_{n+1} - y W_n$ for $W = U, V$. Then for every natural
number $n$, $V_n^2 = (x^2 - 4y) U_n^2 + 4 y^n$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (vi) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasV_sq_eq (P : LucasSequenceParams) (n : ℕ) :
    lucasV P n ^ 2 = (P.p ^ 2 - 4 * P.q) * lucasU P n ^ 2 + 4 * P.q ^ n

/-- **Binomial-sum formula for the Lucas sequence $U$.** Let $x$ and $y \neq 0$ be integers and
let $(U_n)$ be the Lucas sequence with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and
$U_{n+2} = x U_{n+1} - y U_n$. Then for every $r \geq 1$,
$$
U_r = \sum_{i=0}^{\lfloor (r-1)/2 \rfloor} (-y)^i \binom{r-i-1}{i} x^{r-2i-1}.
$$

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (vii) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasU_eq_sum_choose (P : LucasSequenceParams) {r : ℕ} (hr : 1 ≤ r) :
    lucasU P r = ∑ i ∈ Finset.range ((r - 1) / 2 + 1),
      (-P.q) ^ i * ((r - i - 1).choose i : ℤ) * P.p ^ (r - 2 * i - 1)

/-- **Bounds on Lucas sequences by powers of the dominant root.** Let $x$ and $y \neq 0$ be
integers with $x \geq 1$, $|y + 1| \leq x$ and $D = x^2 - 4y > 0$, let $(U_n)$ and $(V_n)$ be the
Lucas sequences with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$, $V_0 = 2$, $V_1 = x$
and $W_{n+2} = x W_{n+1} - y W_n$ for $W = U, V$, and put $\alpha = (x + \sqrt{D})/2$. Then for
every $n \geq 2$ we have $x \alpha^{n-2} \leq U_n$; if $y \leq 0$, then $U_n \leq \alpha^{n-1}$
and $x \alpha^{n-1} \leq V_n \leq \alpha^{n+1}/x$; and if $y \geq 0$, then
$U_n \leq \alpha^n/\sqrt{D}$ and $\alpha^n \leq V_n \leq \alpha^{n+1}/\sqrt{D}$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.2 (`fq-2024-earplynch07182024-lem-2.2`). -/
public theorem_wanted lucasU_lucasV_alpha_bounds (P : LucasSequenceParams) (hx : 1 ≤ P.p)
    (hy : |P.q + 1| ≤ P.p) (hD : 0 < P.p ^ 2 - 4 * P.q) {n : ℕ} (hn : 2 ≤ n) :
    let α : ℝ := (P.p + Real.sqrt (P.p ^ 2 - 4 * P.q)) / 2
    (P.p : ℝ) * α ^ (n - 2) ≤ lucasU P n ∧
      (P.q ≤ 0 → (lucasU P n : ℝ) ≤ α ^ (n - 1)) ∧
      (0 ≤ P.q → (lucasU P n : ℝ) ≤ α ^ n / Real.sqrt (P.p ^ 2 - 4 * P.q)) ∧
      (P.q ≤ 0 → (P.p : ℝ) * α ^ (n - 1) ≤ lucasV P n ∧ (lucasV P n : ℝ) ≤ α ^ (n + 1) / P.p) ∧
      (0 ≤ P.q → α ^ n ≤ (lucasV P n : ℝ) ∧
        (lucasV P n : ℝ) ≤ α ^ (n + 1) / Real.sqrt (P.p ^ 2 - 4 * P.q))

/-- **Lower bounds for ratios of consecutive Lucas terms.** Let $x$ and $y \neq 0$ be integers
with $x \geq 1$ and $|y + 1| \leq x$, and let $(U_n)$ be the Lucas sequence with parameters
$(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{n+2} = x U_{n+1} - y U_n$. If $y < 0$, then
$U_n / U_{n-1} \geq x - xy/(x^2 - y)$ for every $n > 2$. If $y > 0$, then
$U_n / U_{n-1} \geq (x + \sqrt{x^2 - 4y})/2$ for every $n \geq 2$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.3 (`fq-2024-earplynch07182024-lem-2.3`). -/
public theorem_wanted lucasU_ratio_lower_bound (P : LucasSequenceParams) (hx : 1 ≤ P.p)
    (hy : |P.q + 1| ≤ P.p) :
    (P.q < 0 → ∀ n : ℕ, 2 < n →
      (P.p : ℝ) - P.p * P.q / (P.p ^ 2 - P.q) ≤ (lucasU P n : ℝ) / lucasU P (n - 1)) ∧
    (0 < P.q → ∀ n : ℕ, 2 ≤ n →
      (P.p + Real.sqrt (P.p ^ 2 - 4 * P.q)) / 2 ≤ (lucasU P n : ℝ) / lucasU P (n - 1))

/-- **Logarithmic bounds for weighted Lucas power sums when $y < 0$.** Let $x \ge 1$ and $y < 0$
be integers with $|y + 1| \le x$, let $(U_m)$ be the Lucas sequence with parameters $(x, y)$,
given by $U_0 = 0$, $U_1 = 1$ and $U_{m+2} = x U_{m+1} - y U_m$, and let
$\alpha = (x + \sqrt{x^2 - 4y})/2$. Let $k$ be a natural number and $n$, $p$, $q$ positive
integers with $\sum_{j=1}^k j U_j^p = U_n^q$. If $k \ge 2$, then
$\log_\alpha k + p \log_\alpha x + (k - 2)p < (n - 1)q$. If $k \ge 3$, then
$q \log_\alpha x + (n - 2)q < (k - 1)p + \log_\alpha k +
\log_\alpha\bigl(1 + (x^2 - 2y)/(x^{p-1}(x^3 - x^2 - 2xy + y))\bigr)$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.4 (`fq-2024-earplynch07182024-lem-2.4`). -/
public theorem_wanted weighted_power_sum_log_bounds_of_neg (P : LucasSequenceParams)
    (hx : 1 ≤ P.p) (hyneg : P.q < 0) (hy : |P.q + 1| ≤ P.p) {n k p q : ℕ} (hn : 0 < n)
    (hp : 0 < p) (hq : 0 < q)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let α : ℝ := (P.p + Real.sqrt (P.p ^ 2 - 4 * P.q)) / 2
    (2 ≤ k → Real.logb α k + p * Real.logb α P.p + ((k : ℝ) - 2) * p < ((n : ℝ) - 1) * q) ∧
    (3 ≤ k → q * Real.logb α P.p + ((n : ℝ) - 2) * q <
      ((k : ℝ) - 1) * p + Real.logb α k + Real.logb α (1 + ((P.p : ℝ) ^ 2 - 2 * P.q) /
        ((P.p : ℝ) ^ (p - 1) * ((P.p : ℝ) ^ 3 - P.p ^ 2 - 2 * P.p * P.q + P.q))))

/-- **Logarithmic bounds for weighted Lucas power sums when $y > 0$.** Let $x$ and $y > 0$ be
integers with $|y + 1| \le x$ and $D = x^2 - 4y > 0$, let $(U_m)$ be the Lucas sequence with
parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{m+2} = x U_{m+1} - y U_m$, and let
$\alpha = (x + \sqrt{D})/2$. Let $k$ be a natural number and $n$, $p$, $q$ positive integers
with $\sum_{j=1}^k j U_j^p = U_n^q$. If $k \ge 2$, then
$\log_\alpha k + p \log_\alpha x + (k - 2)p < q(n - \log_\alpha \sqrt{D})$. If $k \ge 3$, then
$q \log_\alpha x + (n - 2)q < \log_\alpha k + p(k + 1 - \log_\alpha \sqrt{D}) -
\log_\alpha(\alpha^p - 1)$.

The hypothesis $D > 0$ is added to the statement of the paper: for $x = 2$, $y = 1$ one has
$\alpha = 1$, and $\log_\alpha$ is undefined.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.5 (`fq-2024-earplynch07182024-lem-2.5`). -/
public theorem_wanted weighted_power_sum_log_bounds_of_pos (P : LucasSequenceParams)
    (hypos : 0 < P.q) (hy : |P.q + 1| ≤ P.p) (hD : 0 < P.p ^ 2 - 4 * P.q) {n k p q : ℕ}
    (hn : 0 < n) (hp : 0 < p) (hq : 0 < q)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    (2 ≤ k → Real.logb α k + p * Real.logb α P.p + ((k : ℝ) - 2) * p <
      q * (n - Real.logb α (Real.sqrt D))) ∧
    (3 ≤ k → q * Real.logb α P.p + ((n : ℝ) - 2) * q <
      Real.logb α k + p * ((k : ℝ) + 1 - Real.logb α (Real.sqrt D)) - Real.logb α (α ^ p - 1))

/-- **Valuation of $U_n$ at a prime dividing the discriminant.** Let $x \ge 1$ and $y \ne 0$ be
coprime integers with $|y + 1| \le x$, let $(U_m)$ be the Lucas sequence with parameters $(x, y)$,
given by $U_0 = 0$, $U_1 = 1$ and $U_{m+2} = x U_{m+1} - y U_m$, and let $\ell$ be a prime
dividing $D = x^2 - 4y$. Write $\nu_\ell$ for the $\ell$-adic valuation of an integer, with
$\nu_\ell(0) = 0$. Then for every $n \ge 1$, $\nu_\ell(U_n) = \nu_\ell(n) + \nu_\ell(U_\ell) - 1$
if $\ell \mid n$, and $\nu_\ell(U_n) = 0$ if $\ell \nmid n$. Moreover, $\nu_\ell(U_\ell) = 1$ if
$\ell \ge 5$.

Coprimality of $x$ and $y$ (Sanna's standing hypothesis) is added to the statement of the paper:
without it, $x = 6$, $y = 3$ and $\ell = 3 \mid D = 24$ give $\nu_3(U_2) = \nu_3(6) = 1 \ne 0$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.6 (`fq-2024-earplynch07182024-lem-2.6`). -/
public theorem_wanted padicValInt_lucasU_of_dvd_discr (P : LucasSequenceParams) (hx : 1 ≤ P.p)
    (hy : |P.q + 1| ≤ P.p) (hcop : IsCoprime P.p P.q) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓD : (ℓ : ℤ) ∣ P.p ^ 2 - 4 * P.q) {n : ℕ} (hn : 1 ≤ n) :
    (ℓ ∣ n → padicValInt ℓ (lucasU P n) = padicValNat ℓ n + padicValInt ℓ (lucasU P ℓ) - 1) ∧
    (¬ ℓ ∣ n → padicValInt ℓ (lucasU P n) = 0) ∧
    (5 ≤ ℓ → padicValInt ℓ (lucasU P ℓ) = 1)

/-- **A quadratic equation in the companion Lucas sequence.** Let $x$ be a positive integer,
let $(V_n)$ be the companion Lucas sequence with parameters $(x, -1)$, given by $V_0 = 2$,
$V_1 = x$ and $V_{n+2} = x V_{n+1} + V_n$, and let $D = x^2 + 4$. Let $p, q, k$ be natural numbers
with $p$ odd and $q, k$ positive. If
$$
V_p k^2 + (V_p - 2) k - 1 = \pm D^{p-q} V_p^2
$$
in $\mathbb{Q}$, where the exponent $p - q$ may be negative, then $(p, q, k, x)$ is one of
$(1, 1, 1, 1)$, $(1, 1, 2, 1)$ and $(1, 1, 2, 5)$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.7 (`fq-2024-earplynch07182024-lem-2.7`). -/
public theorem_wanted lucasV_quadratic_eq_pm_discr_zpow (P : LucasSequenceParams)
    (hyP : P.q = -1) {p q k : ℕ} (hx : 0 < P.p) (hp : Odd p) (hq : 0 < q) (hk : 0 < k)
    (h : let V : ℚ := lucasV P p
      let D : ℚ := (P.p : ℚ) ^ 2 + 4
      V * k ^ 2 + (V - 2) * k - 1 = D ^ ((p : ℤ) - q) * V ^ 2 ∨
        V * k ^ 2 + (V - 2) * k - 1 = -(D ^ ((p : ℤ) - q) * V ^ 2)) :
    (p = 1 ∧ q = 1 ∧ k = 1 ∧ P.p = 1) ∨ (p = 1 ∧ q = 1 ∧ k = 2 ∧ P.p = 1) ∨
      (p = 1 ∧ q = 1 ∧ k = 2 ∧ P.p = 5)

/-- **Solutions of $1 + 2x^p = U_n^q$ for Lucas sequences with $y = \pm 1$.** Let $x$ be a
positive integer, let $y \in \{1, -1\}$, and let $(U_m)$ be the Lucas sequence with parameters
$(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{m+2} = x U_{m+1} - y U_m$. For positive integers
$n$, $p$, $q$, the equation $1 + 2x^p = U_n^q$ holds if and only if $(n, p, q, x, y)$ is one of
$(4, p, 1, 1, -1)$, $(1 + 2^{p+1}, p, 1, 2, 1)$, $(3, 2, 2, 2, 1)$, $(3, 1, 1, 2, -1)$ and
$(5, 3, 1, 3, 1)$, where $p$ is arbitrary in the first two.

Since $U_1 = 1$ and $U_2 = x$, this is the case $k = 2$ of the equation
$\sum_{j=1}^k j U_j^p = U_n^q$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Theorem 1.1 (`fq-2024-earplynch07182024-thm-1.1`) and Proposition 3.1
(`fq-2024-earplynch07182024-prop-3.1`). -/
public theorem_wanted one_add_two_mul_pow_eq_lucasU_pow_iff (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) {n p q : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hq : 0 < q) :
    1 + 2 * P.p ^ p = lucasU P n ^ q ↔
      (n = 4 ∧ q = 1 ∧ P.p = 1 ∧ P.q = -1) ∨ (n = 1 + 2 ^ (p + 1) ∧ q = 1 ∧ P.p = 2 ∧ P.q = 1) ∨
        (n = 3 ∧ p = 2 ∧ q = 2 ∧ P.p = 2 ∧ P.q = 1) ∨
        (n = 3 ∧ p = 1 ∧ q = 1 ∧ P.p = 2 ∧ P.q = -1) ∨
        (n = 5 ∧ p = 3 ∧ q = 1 ∧ P.p = 3 ∧ P.q = 1)

/-- **No solutions of $\sum_{j=1}^k j U_j^p = U_n^q$ when $y = -1$ and $x \ge 2$ or $y = 1$ and
$x \ge 3$, with $k \ge 3$ and exponents at most $11$.** Let $y \in \{1, -1\}$, let $x$ be an
integer with $x \ge 2$ if $y = -1$ and $x \ge 3$ if $y = 1$, and let $(U_m)$ be the Lucas sequence
with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{m+2} = x U_{m+1} - y U_m$. If $n$,
$p$, $q$ are positive integers with $p \le 11$ and $q \le 11$, and $k \ge 3$ is an integer, then
$\sum_{j=1}^k j U_j^p \ne U_n^q$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Theorem 1.1 (`fq-2024-earplynch07182024-thm-1.1`), second part. -/
public theorem_wanted weighted_power_sum_ne_lucasU_pow (P : LucasSequenceParams)
    (hy : (P.q = -1 ∧ 2 ≤ P.p) ∨ (P.q = 1 ∧ 3 ≤ P.p)) {n k p q : ℕ} (hn : 0 < n)
    (hp : 0 < p) (hq : 0 < q) (hp11 : p ≤ 11) (hq11 : q ≤ 11) (hk : 3 ≤ k) :
    ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p ≠ lucasU P n ^ q

/-- **Remainder form of the weighted power-sum equation for Lucas sequences.** Let $x$ be a
positive integer, let $y \in \{1, -1\}$, and let $(U_n)$ be the Lucas sequence with parameters
$(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{n+2} = x U_{n+1} - y U_n$. Suppose
$D = x^2 - 4y > 0$ and put $\alpha = (x + \sqrt{D})/2$. Let $n, p, q$ be positive integers and
$k \geq 3$ an integer with
$$
\sum_{j=1}^{k} j \, U_j^p = U_n^q.
$$
Then there are real numbers $R_1, R_2$ with $|R_1| < k^2 \alpha^{k(p-2)}$,
$|R_2| < \alpha^{n(q-2)}$ and
$$
\frac{D^{(q-p)/2} (k\alpha^p - (k+1))}{(\alpha^p - 1)^2} \alpha^{p(k+1)} - \alpha^{qn} =
D^{q/2} R_2 - D^{q/2} R_1 - \frac{D^{(q-p)/2} \alpha^p}{(\alpha^p - 1)^2}.
$$

The remainders $R_1, R_2$ are only asserted to exist; the source defines them explicitly in its
proof.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Proposition 4.1 (`fq-2024-earplynch07182024-prop-4.1`). -/
public theorem_wanted exists_remainders_weighted_power_sum (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) (hD : 0 < P.p ^ 2 - 4 * P.q) {n k p q : ℕ}
    (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    ∃ R₁ R₂ : ℝ, |R₁| < (k : ℝ) ^ 2 * α ^ ((k : ℝ) * ((p : ℝ) - 2)) ∧
      |R₂| < α ^ ((n : ℝ) * ((q : ℝ) - 2)) ∧
      D ^ (((q : ℝ) - p) / 2) * (k * α ^ p - (k + 1)) / (α ^ p - 1) ^ 2 * α ^ (p * (k + 1)) -
          α ^ (q * n) =
        D ^ ((q : ℝ) / 2) * R₂ - D ^ ((q : ℝ) / 2) * R₁ -
          D ^ (((q : ℝ) - p) / 2) * α ^ p / (α ^ p - 1) ^ 2

/-- **Bound on the parameter in the weighted power-sum equation for Lucas sequences.** Let $x$
be a positive integer, let $y \in \{1, -1\}$, and let $(U_n)$ be the Lucas sequence with
parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and $U_{n+2} = x U_{n+1} - y U_n$.
If $n, p, q$ are positive integers and $k \geq 3$ is an integer with
$$
\sum_{j=1}^{k} j \, U_j^p = U_n^q,
$$
then $x \leq (k + 1)^2/4 + 1$.

The hypothesis $k \geq 3$ cannot be dropped entirely: for $k = 1$ and $y = -1$,
$(n, p, q, x) = (1, 1, 1, 5)$ is a solution and $5 > (1 + 1)^2/4 + 1 = 2$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 4.4 (`fq-2024-earplynch07182024-lem-4.4`). -/
public theorem_wanted le_of_weighted_power_sum_eq (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) {n k p q : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    (P.p : ℚ) ≤ ((k : ℚ) + 1) ^ 2 / 4 + 1

/-- **Remainder bound for weighted Lucas power sums when $y = -1$.** Let $x$ be a positive
integer, let $(U_m)$ be the Lucas sequence with parameters $(x, -1)$, given by $U_0 = 0$,
$U_1 = 1$ and $U_{m+2} = x U_{m+1} + U_m$, and let $D = x^2 + 4$ and $\alpha = (x + \sqrt{D})/2$.
If positive integers $n$, $p$, $q$ and an integer $k \ge 3$ satisfy
$\sum_{j=1}^k j U_j^p = U_n^q$, then the remainder $R_2 = U_n^q - \alpha^{nq}/D^{q/2}$ satisfies
$D^{q/2} |R_2| < k (D + 1/x)^{q+1} \alpha^{kp - 2k/q + 1}$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 4.2 (`fq-2024-earplynch07182024-lem-4.2`). -/
public theorem_wanted remainder_bound_of_neg (P : LucasSequenceParams) (hyP : P.q = -1)
    (hx : 0 < P.p) {n k p q : ℕ} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    D ^ ((q : ℝ) / 2) * |(lucasU P n : ℝ) ^ q - α ^ (n * q) / D ^ ((q : ℝ) / 2)| <
      k * (D + 1 / P.p) ^ (q + 1) * α ^ ((k : ℝ) * p - 2 * k / q + 1)

/-- **Remainder bound for weighted Lucas power sums when $y = 1$.** Let $x$ be a positive integer
with $D = x^2 - 4 > 0$, let $(U_m)$ be the Lucas sequence with parameters $(x, 1)$, given by
$U_0 = 0$, $U_1 = 1$ and $U_{m+2} = x U_{m+1} - U_m$, let $V_2 = x^2 - 2$ be the term of index $2$
of the companion Lucas sequence, and let $\alpha = (x + \sqrt{D})/2$. If positive integers $n$,
$p$, $q$ and an integer $k \ge 3$ satisfy $\sum_{j=1}^k j U_j^p = U_n^q$, then the remainder
$R_2 = U_n^q - \alpha^{nq}/D^{q/2}$ satisfies
$D^{q/2} |R_2| < k (V_2 + 1/x)^{q+1} \alpha^{kp - 2k/q + 1/2}$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 4.3 (`fq-2024-earplynch07182024-lem-4.3`). -/
public theorem_wanted remainder_bound_of_pos (P : LucasSequenceParams) (hyP : P.q = 1)
    (hD : 0 < P.p ^ 2 - 4 * P.q) (hx : 0 < P.p) {n k p q : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    D ^ ((q : ℝ) / 2) * |(lucasU P n : ℝ) ^ q - α ^ (n * q) / D ^ ((q : ℝ) / 2)| <
      k * ((lucasV P 2 : ℝ) + 1 / P.p) ^ (q + 1) * α ^ ((k : ℝ) * p - 2 * k / q + 1 / 2)

end

end MetaMathlibExt
