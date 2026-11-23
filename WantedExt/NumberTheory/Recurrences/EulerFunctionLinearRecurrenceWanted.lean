/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
Statements from Luca and Manape on the Euler function of linearly recurrent sequences.

A sequence `(U_n)_{n ≥ 1}` is encoded as `U : ℕ → R` whose shift `fun n => U (n + 1)` solves a
Mathlib `LinearRecurrence R` `E`; `U 0` is unused. Following the paper, `E` is taken of minimal
order, and nondegeneracy says that `0` is not a root of the characteristic polynomial and no
quotient of two distinct roots is a root of unity.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- **Lower bound for Euler's function and upper bound for the sum of divisors.** Let $\varphi$
be Euler's totient function and $\sigma(n)$ the sum of the positive divisors of $n$. There is a
constant $C > 0$ such that $\varphi(n)/n \ge C/\log\log n$ for every integer $n \ge 3$, and there
is a constant $C'$ such that $\sigma(n)/n \le C' \log\log n$ for every integer $n \ge 3$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 1 (`fq-2024-luca09162024rev2-lem-1`),
quoted from Hardy and Wright, Theorems 323, 328 and 329. -/
public theorem_wanted totient_div_gg_and_sigma_div_ll_log_log :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
        C / Real.log (Real.log n) ≤ (Nat.totient n : ℝ) / n) ∧
      ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
        (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ C * Real.log (Real.log n)

/-- **Sieve bound for integers without small prime factors.** Write $p(n)$ for the least prime
factor of an integer $n \ge 2$, and set $p(1) = 1$. There is a constant $C$ such that for all real
$x$ and $y$ with $2 \le y \le x$, the number of integers $1 \le n \le x$ with $p(n) > y$ is at
most $C x / \log y$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 2 (`fq-2024-luca09162024rev2-lem-2`),
quoted from Tenenbaum, page 397. -/
public theorem_wanted card_minFac_gt_le_div_log :
    ∃ C : ℝ, ∀ x y : ℝ, 2 ≤ y → y ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => y < (Nat.minFac n : ℝ))).card ≤
        C * x / Real.log y

/-- **Integers with many prime factors are rare.** Let $\Omega(n)$ be the number of prime factors
of $n$ counted with multiplicity. There is a constant $C$ such that for every real $x \ge 10$, the
number of integers $1 \le n \le x$ with $\Omega(n) \ge 10 \log\log x$ is at most
$C x / (\log x)^2$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 3 (`fq-2024-luca09162024rev2-lem-3`). -/
public theorem_wanted card_cardFactors_ge_ten_log_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 10 ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          10 * Real.log (Real.log x) ≤ (ArithmeticFunction.cardFactors n : ℝ))).card ≤
        C * x / Real.log x ^ 2

/-- **Integers whose sum of divisors has many divisors.** Let $\sigma(n)$ be the sum of the
positive divisors of $n$ and $\tau(m)$ the number of positive divisors of $m$. There is a constant
$C$ such that for every real $x \ge 10$, the number of integers $1 \le n \le x$ with
$\tau(\sigma(n)) > \exp(\sqrt{\log x})$ is at most $C x / (\log x)^2$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 4 (`fq-2024-luca09162024rev2-lem-4`). -/
public theorem_wanted card_divisors_sigma_gt_exp_sqrt_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 10 ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          Real.exp (Real.sqrt (Real.log x)) <
            ((Nat.divisors (ArithmeticFunction.sigma 1 n)).card : ℝ))).card ≤
        C * x / Real.log x ^ 2

/-- **Schmidt's bound on the zeros of a linear recurrence.** Let $(U_n)_{n \ge 1}$ be a sequence
of complex numbers satisfying $U_{m+k} = c_0 U_m + c_1 U_{m+1} + \dots + c_{k-1} U_{m+k-1}$ for
all $m \ge 1$, with complex coefficients $c_i$, where the order $k$ of this recurrence is minimal
among all linear recurrences with complex coefficients satisfied by $(U_n)_{n \ge 1}$, and
$k \ge 2$. Suppose the recurrence is nondegenerate: no root of its characteristic polynomial
$X^k - c_{k-1} X^{k-1} - \dots - c_0$ is $0$, and no quotient of two distinct roots is a root of
unity. Then $U_n = 0$ for only finitely many $n \ge 1$, and there are at most
$\exp(\exp(\exp(3k \log k)))$ such $n$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Theorem 3 (`fq-2024-luca09162024rev2-thm-3`), quoted from Schmidt. -/
public theorem_wanted zero_set_card_le_exp_exp_exp (E : LinearRecurrence ℂ) (U : ℕ → ℂ)
    (hU : E.IsSolution (fun n => U (n + 1)))
    (hmin : ∀ E' : LinearRecurrence ℂ, E'.IsSolution (fun n => U (n + 1)) → E.order ≤ E'.order)
    (hnd : ∀ α β : ℂ, E.charPoly.IsRoot α → E.charPoly.IsRoot β →
      α ≠ 0 ∧ (α ≠ β → ∀ m : ℕ, 0 < m → (α / β) ^ m ≠ 1))
    (hk : 2 ≤ E.order) :
    {n : ℕ | 1 ≤ n ∧ U n = 0}.Finite ∧
      ({n : ℕ | 1 ≤ n ∧ U n = 0}.ncard : ℝ) ≤
        Real.exp (Real.exp (Real.exp (3 * E.order * Real.log E.order)))

/-- **Few small values of a nondegenerate integer linear recurrence.** Let $(U_n)_{n \ge 1}$ be a
sequence of integers satisfying $U_{m+k} = c_0 U_m + c_1 U_{m+1} + \dots + c_{k-1} U_{m+k-1}$ for
all $m \ge 1$, with integer coefficients $c_i$, where the order $k$ of this recurrence is minimal
among all linear recurrences with integer coefficients satisfied by $(U_n)_{n \ge 1}$. Suppose the
recurrence is nondegenerate: no complex root of its characteristic polynomial
$X^k - c_{k-1} X^{k-1} - \dots - c_0$ is $0$, and no quotient of two distinct complex roots is a
root of unity. Suppose also that the characteristic polynomial has at least two distinct complex
roots, and let $\alpha_1$ be a complex root of maximal modulus. Then there are a real $c$ with
$0 < c < 1/3$ and real constants $x_0$ and $C$ such that for every real $x \ge x_0$, the number of
integers $1 \le n \le x$ with $|U_n| \le |\alpha_1|^{n(1 - x^{-c})}$ is at most $C \sqrt{x}$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 5 (`fq-2024-luca09162024rev2-lem-5`). -/
public theorem_wanted card_abs_le_dominant_root_pow_le_sqrt (E : LinearRecurrence ℤ)
    (U : ℕ → ℤ) (hU : E.IsSolution (fun n => U (n + 1)))
    (hmin : ∀ E' : LinearRecurrence ℤ, E'.IsSolution (fun n => U (n + 1)) → E.order ≤ E'.order)
    (hnd : ∀ α β : ℂ, (E.charPoly.map (Int.castRingHom ℂ)).IsRoot α →
      (E.charPoly.map (Int.castRingHom ℂ)).IsRoot β →
      α ≠ 0 ∧ (α ≠ β → ∀ m : ℕ, 0 < m → (α / β) ^ m ≠ 1))
    (hs : ∃ α β : ℂ, (E.charPoly.map (Int.castRingHom ℂ)).IsRoot α ∧
      (E.charPoly.map (Int.castRingHom ℂ)).IsRoot β ∧ α ≠ β)
    (α₁ : ℂ) (hα₁ : (E.charPoly.map (Int.castRingHom ℂ)).IsRoot α₁)
    (hmax : ∀ β : ℂ, (E.charPoly.map (Int.castRingHom ℂ)).IsRoot β → ‖β‖ ≤ ‖α₁‖) :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 3 ∧ ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          (|U n| : ℝ) ≤ ‖α₁‖ ^ ((n : ℝ) * (1 - x ^ (-c))))).card ≤ C * Real.sqrt x

/-- **Euler's function and the sum of divisors along a linear recurrence.** Let
$(U_n)_{n \ge 1}$ be a sequence of integers satisfying
$U_{m+k} = c_0 U_m + c_1 U_{m+1} + \dots + c_{k-1} U_{m+k-1}$ for all $m \ge 1$, with integer
coefficients $c_i$, where the order $k$ of this recurrence is minimal among all linear recurrences
with integer coefficients satisfied by $(U_n)_{n \ge 1}$. Suppose the recurrence is nondegenerate:
no complex root of its characteristic polynomial $X^k - c_{k-1} X^{k-1} - \dots - c_0$ is $0$, and
no quotient of two distinct complex roots is a root of unity. Suppose also that there is no
polynomial $P$ with rational coefficients such that $|U_n| = P(n)$ for all sufficiently large $n$.
Let $\varphi$ be Euler's totient function and $\sigma(m)$ the sum of the positive divisors of $m$,
with $\varphi(0) = \sigma(0) = 0$. Then there are real constants $x_0$ and $C$ such that for every
real $x \ge x_0$, the number of integers $1 \le n \le x$ with $\varphi(|U_n|) < |U_{\varphi(n)}|$
is at most $C x / \log x$, and the number of integers $1 \le n \le x$ with
$|U_{\sigma(n)}| < \sigma(|U_n|)$ is at most $C x / \log x$.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Theorem 1 (`fq-2024-luca09162024rev2-thm-1`). -/
public theorem_wanted card_totient_sigma_inequality_fails_le_div_log (E : LinearRecurrence ℤ)
    (U : ℕ → ℤ) (hU : E.IsSolution (fun n => U (n + 1)))
    (hmin : ∀ E' : LinearRecurrence ℤ, E'.IsSolution (fun n => U (n + 1)) → E.order ≤ E'.order)
    (hnd : ∀ α β : ℂ, (E.charPoly.map (Int.castRingHom ℂ)).IsRoot α →
      (E.charPoly.map (Int.castRingHom ℂ)).IsRoot β →
      α ≠ 0 ∧ (α ≠ β → ∀ m : ℕ, 0 < m → (α / β) ^ m ≠ 1))
    (hpoly : ¬ ∃ P : Polynomial ℚ, ∀ᶠ n in atTop, ((|U n| : ℤ) : ℚ) = P.eval (n : ℚ)) :
    ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          ((Nat.totient (U n).natAbs : ℕ) : ℤ) < |U (Nat.totient n)|)).card ≤
          C * x / Real.log x ∧
        ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          |U (ArithmeticFunction.sigma 1 n)| <
            ((ArithmeticFunction.sigma 1 (U n).natAbs : ℕ) : ℤ))).card ≤
          C * x / Real.log x

end

end MetaMathlibExt
