/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.LucasPolytopicNumber
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

/-!
# Simplicial `d`-polytopic numbers on Lucas sequences

Statements from Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas
Sequences*, Journal of Integer Sequences 28 (2025), Article 25.5.6 (arXiv `2501.11490`).

The bracket `{n}_{s,t}` is `lucasBracket P n` and the fibonomial `[n, k]_{s,t}` is
`lucasnomial P n k` from `MathlibExt.NumberTheory.LucasPolytopicNumber`. The constants
`φ_{s,t}`, `φ'_{s,t}` are the two roots of `x ^ 2 - s x - t`; in the polynomial identities
they are any real pair with `φ + φ' = s` and `φ φ' = -t` (each identity was checked for both
orderings), and in the series identities they are the paper's
`φ = (s + √(s ^ 2 + 4 t)) / 2`, `φ' = (s - √(s ^ 2 + 4 t)) / 2`. The paper's `q` is
`φ' / φ` (stated in the proof of Theorem 13), so `(φ^d x; q)_{d+1} = ∏_{k ≤ d} (1 - φ^{d-k} φ'^k x)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sum formula for Lucasnomial coefficients.** Let $(s, t)$ be nondegenerate Lucas parameters,
with Lucasnomial coefficients $\binom{n}{k}_{s,t}$, and let $\varphi$ and $\varphi'$ be real
numbers with $\varphi + \varphi' = s$ and $\varphi \varphi' = -t$. For all natural numbers
$n \ge 1$ and $d$,
$$\binom{n+d}{d+1}_{s,t} = \sum_{k=1}^{n} \varphi^{(d+1)(n-k)} \varphi'^{k-1}
\binom{k+d-1}{d}_{s,t},$$
and the same holds with $\varphi$ and $\varphi'$ exchanged.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 2
(`jis-2025-25.5.6-thm-2`). -/
public theorem_wanted lucasnomial_succ_eq_sum_lucasPolytopic (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) (n d : ℕ) (hn : 1 ≤ n) :
    lucasnomial P (n + d) (d + 1) =
        ∑ k ∈ Finset.Icc 1 n, φ ^ ((d + 1) * (n - k)) * φ' ^ (k - 1) *
          lucasnomial P (k + d - 1) d ∧
      lucasnomial P (n + d) (d + 1) =
        ∑ k ∈ Finset.Icc 1 n, φ' ^ ((d + 1) * (n - k)) * φ ^ (k - 1) *
          lucasnomial P (k + d - 1) d

/-- **Identities for the Lucas triangular numbers.** Let $(s, t)$ be nondegenerate Lucas
parameters and let $\varphi, \varphi'$ be real numbers with $\varphi + \varphi' = s$ and
$\varphi\varphi' = -t$; write $\{n\}_{s,t}$ for the Lucas brackets and $\binom{n}{k}_{s,t}$ for
the Lucasnomial coefficients. Then
$\binom{n+1}{2}_{s,t} = t\binom{n}{2}_{s,t} + \{n\}_{s,t}^2$ and
$\binom{n+1}{2}_{s,t} = \sum_{k=1}^{n} t^{n-k}\{k\}_{s,t}^2$ for every natural number $n$, and
$\varphi'^{n-1}\binom{n+1}{2}_{s,t} + \varphi^{n+1}\binom{n}{2}_{s,t} =
\frac{\varphi^n + \varphi'^n}{\{2\}_{s,t}}\{n\}_{s,t}^2$ for every natural number $n \ge 1$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 3
(`jis-2025-25.5.6-thm-3`). -/
public theorem_wanted lucasTriangular_identities (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) :
    (∀ n : ℕ, lucasnomial P (n + 1) 2 = P.t * lucasnomial P n 2 + lucasBracket P n ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n →
      φ' ^ (n - 1) * lucasnomial P (n + 1) 2 + φ ^ (n + 1) * lucasnomial P n 2 =
        (φ ^ n + φ' ^ n) / lucasBracket P 2 * lucasBracket P n ^ 2) ∧
    (∀ n : ℕ, lucasnomial P (n + 1) 2 =
      ∑ k ∈ Finset.Icc 1 n, P.t ^ (n - k) * lucasBracket P k ^ 2)

/-- **Weighted difference of consecutive squared Lucas triangular numbers.** Let $(s, t)$ be
nondegenerate Lucas parameters, with Lucas brackets $\{n\}_{s,t}$ and Lucasnomial coefficients
$\binom{n}{k}_{s,t}$. For every natural number $n$,
$$\binom{n+2}{2}_{s,t}^{2} - t^2 \binom{n+1}{2}_{s,t}^{2} =
\frac{\{n+2\}_{s,t} + t \{n\}_{s,t}}{s} \{n+1\}_{s,t}^{3}.$$

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 4
(`jis-2025-25.5.6-thm-4`). -/
public theorem_wanted lucasTriangular_sq_sub_sq (P : LucasParameters) (n : ℕ) :
    lucasnomial P (n + 2) 2 ^ 2 - P.t ^ 2 * lucasnomial P (n + 1) 2 ^ 2 =
      (lucasBracket P (n + 2) + P.t * lucasBracket P n) / P.s * lucasBracket P (n + 1) ^ 3

/-- **Weighted sum of cubes of Lucas brackets.** Let $(s, t)$ be nondegenerate Lucas parameters,
with Lucas brackets $\{n\}_{s,t}$ and Lucasnomial coefficients $\binom{n}{k}_{s,t}$. For every
natural number $n$,
$$\sum_{k=1}^{n} t^{2(n-k)} \frac{\{k+1\}_{s,t} + t \{k-1\}_{s,t}}{s} \{k\}_{s,t}^{3} =
\binom{n+1}{2}_{s,t}^{2}.$$

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 5
(`jis-2025-25.5.6-thm-5`). -/
public theorem_wanted sum_cubes_eq_lucasTriangular_sq (P : LucasParameters) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, P.t ^ (2 * (n - k)) *
        ((lucasBracket P (k + 1) + P.t * lucasBracket P (k - 1)) / P.s) * lucasBracket P k ^ 3 =
      lucasnomial P (n + 1) 2 ^ 2

/-- **Sum-of-cubes identities for Fibonacci, Pell, Jacobsthal and Mersenne numbers.** Let $F_n$
be the Fibonacci numbers, $P_n$ the Pell numbers, and $J_n$ the Jacobsthal numbers, that is, the
Lucas sequence $U(1, -2)$, with $J_0 = 0$, $J_1 = 1$ and $J_{n+2} = J_{n+1} + 2 J_n$. For every
natural number $n$,
$$\sum_{k=1}^{n} (F_{k+1} + F_{k-1}) F_k^3 = F_n^2 F_{n+1}^2,$$
$$\sum_{k=1}^{n} (P_{k+1} + P_{k-1}) P_k^3 = \tfrac{1}{2} P_n^2 P_{n+1}^2,$$
$$\sum_{k=1}^{n} 4^{n-k} (J_{k+1} + 2 J_{k-1}) J_k^3 = J_n^2 J_{n+1}^2,$$
$$\sum_{k=1}^{n} 4^{n-k} (2^k + 1) (2^k - 1)^3 = \tfrac{1}{3} (2^n - 1)^2 (2^{n+1} - 1)^2,$$
and, for every real number $q$ with $q \ne 1$ and $q \ne -1$ (Warnaar's identity),
$$\sum_{k=1}^{n} q^{2(n-k)} \frac{1 - q^{2k}}{1 - q^2} \Big(\frac{1 - q^k}{1 - q}\Big)^2 =
\Big(\frac{(1 - q^{n+1}) (1 - q^n)}{(1 - q) (1 - q^2)}\Big)^2.$$

The numbers $2^k - 1$ are the Mersenne numbers, and the right side of the last identity is the
square of the Gaussian binomial coefficient $\binom{n+1}{2}_q$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Corollary 6
(`jis-2025-25.5.6-cor-6`). -/
public theorem_wanted sum_cubes_specializations (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.fib (k + 1) + Nat.fib (k - 1)) * Nat.fib k ^ 3 =
        Nat.fib n ^ 2 * Nat.fib (n + 1) ^ 2 ∧
    (∑ k ∈ Finset.Icc 1 n, ((pellNumber (k + 1) + pellNumber (k - 1)) * pellNumber k ^ 3 : ℚ)) =
        1 / 2 * pellNumber n ^ 2 * pellNumber (n + 1) ^ 2 ∧
    ∑ k ∈ Finset.Icc 1 n, 4 ^ (n - k) *
        (lucasU ⟨1, -2, by decide⟩ (k + 1) + 2 * lucasU ⟨1, -2, by decide⟩ (k - 1)) *
          lucasU ⟨1, -2, by decide⟩ k ^ 3 =
        lucasU ⟨1, -2, by decide⟩ n ^ 2 * lucasU ⟨1, -2, by decide⟩ (n + 1) ^ 2 ∧
    (∑ k ∈ Finset.Icc 1 n, (4 ^ (n - k) * (2 ^ k + 1) * (2 ^ k - 1) ^ 3 : ℚ)) =
        1 / 3 * (2 ^ n - 1) ^ 2 * (2 ^ (n + 1) - 1) ^ 2 ∧
    ∀ q : ℝ, q ≠ 1 → q ≠ -1 →
      ∑ k ∈ Finset.Icc 1 n, q ^ (2 * (n - k)) * ((1 - q ^ (2 * k)) / (1 - q ^ 2)) *
          ((1 - q ^ k) / (1 - q)) ^ 2 =
        ((1 - q ^ (n + 1)) * (1 - q ^ n) / ((1 - q) * (1 - q ^ 2))) ^ 2

/-- **Recurrence for the Lucas tetrahedral numbers.** Let $(s, t)$ be nondegenerate Lucas
parameters, and write $\{n\}_{s,t}$ for the Lucas brackets and $\binom{n}{k}_{s,t}$ for the
Lucasnomial coefficients. For every natural number $n$,
$$\binom{n+3}{3}_{s,t} = st\binom{n+2}{3}_{s,t} + \{n+1\}_{s,t}\binom{n+2}{2}_{s,t}.$$

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 7
(`jis-2025-25.5.6-thm-7`). -/
public theorem_wanted lucasTetrahedral_recurrence (P : LucasParameters) (n : ℕ) :
    lucasnomial P (n + 3) 3 =
      P.s * P.t * lucasnomial P (n + 2) 3 + lucasBracket P (n + 1) * lucasnomial P (n + 2) 2

/-- **Lucas derivative.** For real numbers $\varphi$ and $\varphi'$, the Lucas derivative
$D_{\varphi,\varphi'}$ sends a function $f : \mathbb{R} \to \mathbb{R}$ to the function whose
value at $x \ne 0$ is $(f(\varphi x) - f(\varphi' x))/((\varphi - \varphi')x)$, read as $0$ when
$\varphi = \varphi'$, and whose value at $0$ is the derivative $f'(0)$, read as $0$ when $f$ is
not differentiable at $0$.

In the paper $\varphi \ne \varphi'$ are the roots of $x^2 - sx - t$; its separate definition for
$s^2 + 4t = 0$ is not covered.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
noncomputable def lucasDerivative (φ φ' : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then deriv f 0 else (f (φ * x) - f (φ' * x)) / ((φ - φ') * x)

/-- **The Lucas derivative away from the origin.** For all real numbers $\varphi$, $\varphi'$
and $x \ne 0$ and every function $f : \mathbb{R} \to \mathbb{R}$, the Lucas derivative
$D_{\varphi,\varphi'}$ satisfies
$D_{\varphi,\varphi'} f(x) = (f(\varphi x) - f(\varphi' x))/((\varphi - \varphi')x)$, where the
quotient is read as $0$ when $\varphi = \varphi'$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
theorem lucasDerivative_of_ne_zero (φ φ' : ℝ) (f : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    lucasDerivative φ φ' f x = (f (φ * x) - f (φ' * x)) / ((φ - φ') * x) := by
  simp [lucasDerivative, hx]

/-- **The Lucas derivative at the origin.** For all real numbers $\varphi$, $\varphi'$ and every
function $f : \mathbb{R} \to \mathbb{R}$, the Lucas derivative $D_{\varphi,\varphi'}$ satisfies
$D_{\varphi,\varphi'} f(0) = f'(0)$, where $f'(0)$ is read as $0$ when $f$ is not differentiable
at $0$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
theorem lucasDerivative_zero (φ φ' : ℝ) (f : ℝ → ℝ) :
    lucasDerivative φ φ' f 0 = deriv f 0 := by
  simp [lucasDerivative]

/-- **The Lucas derivative of the identity.** For distinct real numbers $\varphi \ne \varphi'$,
the Lucas derivative $D_{\varphi,\varphi'}$ of the identity function $y \mapsto y$ equals $1$ at
every real number $x$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
theorem lucasDerivative_id {φ φ' : ℝ} (h : φ ≠ φ') (x : ℝ) :
    lucasDerivative φ φ' (fun y => y) x = 1 := by
  by_cases hx : x = 0
  · simp [lucasDerivative, hx]
  · rw [lucasDerivative_of_ne_zero _ _ _ hx, ← sub_mul]
    exact div_self (mul_ne_zero (sub_ne_zero.mpr h) hx)

/-- **Iterated Lucas derivatives of $1/(1 - x)$.** Let $(s, t)$ be nondegenerate Lucas
parameters, let $\varphi \ne \varphi'$ be real numbers with $\varphi + \varphi' = s$ and
$\varphi\varphi' = -t$, write $D_{\varphi,\varphi'}$ for the Lucas derivative and
$\{n\}_{s,t}!$ for the $s,t$-factorial. For every natural number $n$ and every real number $x$
with $\prod_{k=0}^{n} (1 - \varphi^{n-k}\varphi'^k x) \ne 0$, the $n$-fold iterate of
$D_{\varphi,\varphi'}$ applied to the function $y \mapsto 1/(1 - y)$ has value at $x$
$$\frac{\{n\}_{s,t}!}{\prod_{k=0}^{n} (1 - \varphi^{n-k}\varphi'^k x)}.$$

With $q = \varphi'/\varphi$ the denominator is the $q$-Pochhammer symbol
$(\varphi^n x; q)_{n+1}$ of the paper, which states the identity for $n \ge 1$. Real distinct
$\varphi, \varphi'$ exist only when $s^2 + 4t > 0$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 8
(`jis-2025-25.5.6-thm-8`). -/
public theorem_wanted iterate_lucasDerivative_inv_one_sub (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) (hne : φ ≠ φ') (n : ℕ) (x : ℝ)
    (hx : ∏ k ∈ Finset.range (n + 1), (1 - φ ^ (n - k) * φ' ^ k * x) ≠ 0) :
    (lucasDerivative φ φ')^[n] (fun y => 1 / (1 - y)) x =
      lucasFactorial P n / ∏ k ∈ Finset.range (n + 1), (1 - φ ^ (n - k) * φ' ^ k * x)

/-- **Generating function of the simplicial Lucas-polytopic numbers.** Let $(s, t)$ be
nondegenerate Lucas parameters, let $\varphi, \varphi'$ be real numbers with
$\varphi + \varphi' = s$ and $\varphi\varphi' = -t$, let $d$ be a natural number and write
$\binom{n}{k}_{s,t}$ for the Lucasnomial coefficients, so that the $n$-th simplicial
$d$-Lucas-polytopic number is $\binom{n+d-1}{d}_{s,t}$. Then, as formal power series in $x$ with
real coefficients,
$$\Big(\sum_{n\ge 1}\binom{n+d-1}{d}_{s,t}x^n\Big)\prod_{k=0}^{d}(1-\varphi^{d-k}\varphi'^k x)=x.$$

This is the paper's identity $\sum_{n \ge 1} \binom{n+d-1}{d}_{s,t} x^n = x/(\varphi^d x; q)_{d+1}$
with $q = \varphi'/\varphi$ and the denominator cleared.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 9
(`jis-2025-25.5.6-thm-9`). -/
public theorem_wanted lucasPolytopic_generatingFunction (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) (d : ℕ) :
    PowerSeries.mk (fun n => if n = 0 then 0 else lucasPolytopicNumber P n d) *
        ∏ k ∈ Finset.range (d + 1), (1 - PowerSeries.C (φ ^ (d - k) * φ' ^ k) * PowerSeries.X) =
      PowerSeries.X

/-- **Generating function of the squared Lucas triangular numbers.** Let $(s, t)$ be nondegenerate
Lucas parameters, with Lucas brackets $\{n\}_{s,t}$ and Lucasnomial coefficients
$\binom{n}{k}_{s,t}$, and let $\varphi$ and $\varphi'$ be real numbers with
$\varphi + \varphi' = s$ and $\varphi \varphi' = -t$. Then, as formal power series in $x$ with
real coefficients,
$$\Big(\sum_{n \ge 1} \binom{n+1}{2}_{s,t}^{2} x^n\Big) (1 - t^2 x) (1 - \varphi'^4 x)
\prod_{k=0}^{3} (1 - \varphi^{4-k} \varphi'^k x) = x + (\{4\}_{s,t} \varphi - \varphi^4) x^2 -
\{3\}_{s,t} \varphi^3 \varphi'^3 x^3 +
(\{3\}_{s,t} \varphi^7 \varphi'^3 - \{4\}_{s,t} \varphi^6 \varphi'^3) x^4.$$

This is the paper's quotient formula for $\sum_{n \ge 1} \binom{n+1}{2}_{s,t}^{2} x^n$ with the
denominator cleared; the paper writes the product over $k$ as $(\varphi^4 x; q)_4$ with
$q = \varphi' / \varphi$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 10
(`jis-2025-25.5.6-thm-10`). -/
public theorem_wanted lucasTriangular_sq_generatingFunction (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) :
    PowerSeries.mk (fun n => if n = 0 then 0 else lucasnomial P (n + 1) 2 ^ 2) *
        ((1 - PowerSeries.C (P.t ^ 2) * PowerSeries.X) *
          (1 - PowerSeries.C (φ' ^ 4) * PowerSeries.X) *
          ∏ k ∈ Finset.range 4, (1 - PowerSeries.C (φ ^ (4 - k) * φ' ^ k) * PowerSeries.X)) =
      PowerSeries.X +
        PowerSeries.C (lucasBracket P 4 * φ - φ ^ 4) * PowerSeries.X ^ 2 -
        PowerSeries.C (lucasBracket P 3 * φ ^ 3 * φ' ^ 3) * PowerSeries.X ^ 3 +
        PowerSeries.C (lucasBracket P 3 * φ ^ 7 * φ' ^ 3 - lucasBracket P 4 * φ ^ 6 * φ' ^ 3) *
          PowerSeries.X ^ 4

/-- **Even-index Lucas-bracket series as Lambert series.** Let $(s, t)$ be nondegenerate Lucas
parameters with $s > 0$ and $s^2 + 4t > 0$, write $\{n\}_{s,t}$ for the Lucas brackets, let
$\varphi' = (s - \sqrt{s^2 + 4t})/2$ and let $L(x) = \sum_{n \ge 1} x^n/(1 - x^n)$ be the Lambert
series. Then the series $\sum_{n \ge 1} t^n/\{2n\}_{s,t}$ converges absolutely, and its sum is
$\sqrt{s^2 + 4t}\,\bigl(L(\varphi'^2/t) - L(\varphi'^4/t^2)\bigr)$.

The hypotheses make $\varphi'$ real with $|\varphi'| < (s + \sqrt{s^2 + 4t})/2$, so both Lambert
arguments lie in $(-1, 1)$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 11
(`jis-2025-25.5.6-thm-11`). -/
public theorem_wanted hasSum_pow_div_lucasBracket_two_mul (P : LucasParameters) (hs : 0 < P.s)
    (hdisc : 0 < P.s ^ 2 + 4 * P.t) :
    HasSum (fun n : ℕ => P.t ^ (n + 1) / lucasBracket P (2 * (n + 1)))
      (Real.sqrt (P.s ^ 2 + 4 * P.t) *
        ((∑' n : ℕ, (((P.s - Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) ^ 2 / P.t) ^ (n + 1) /
            (1 - (((P.s - Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) ^ 2 / P.t) ^ (n + 1))) -
          ∑' n : ℕ, (((P.s - Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) ^ 4 / P.t ^ 2) ^ (n + 1) /
            (1 - (((P.s - Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) ^ 4 / P.t ^ 2) ^ (n + 1))))

/-- **Sum of reciprocals of products of consecutive Lucas brackets.** Let $(s, t)$ be
nondegenerate Lucas parameters with $s > 0$, $s^2 + 4t > 0$ and $|t| > 1$, write $\{n\}_{s,t}$
for the Lucas brackets and let $\varphi = (s + \sqrt{s^2 + 4t})/2$. Then the series
$\sum_{n \ge 1} 1/(\{n\}_{s,t}\{n+1\}_{s,t})$ converges absolutely, and its sum is
$\varphi - (1 + t)\ln_{s,t}(1 + \varphi/t)$, where
$\ln_{s,t}(1 + \varphi/t) = -\sum_{n \ge 1} (-\varphi/t)^n/\{n\}_{s,t}$ is the Lucas logarithm.

The hypotheses $s > 0$ and $s^2 + 4t > 0$ make $\varphi$ real with $0 < |q| < 1$, where
$q = \varphi'/\varphi$ and $\varphi' = (s - \sqrt{s^2 + 4t})/2$; and $|t| > 1$ puts $-\varphi/t$ in
the paper's convergence range $(-|\varphi|, |\varphi|)$ of the Lucas logarithm. Without
$|t| > 1$ the logarithm series diverges: for $s = t = 1$ its terms $(-\varphi)^n/F_n$, with $F_n$
the Fibonacci numbers, do not tend to $0$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 13
(`jis-2025-25.5.6-thm-13`). -/
public theorem_wanted hasSum_inv_lucasBracket_mul_succ (P : LucasParameters) (hs : 0 < P.s)
    (hdisc : 0 < P.s ^ 2 + 4 * P.t) (ht : 1 < |P.t|) :
    HasSum (fun n : ℕ => 1 / (lucasBracket P (n + 1) * lucasBracket P (n + 2)))
      ((P.s + Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2 -
        (1 + P.t) * -∑' n : ℕ, (-((P.s + Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) / P.t) ^ (n + 1) /
          lucasBracket P (n + 1))

end

end MetaMathlibExt
