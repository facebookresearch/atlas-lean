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
public import MathlibExt.NumberTheory.LucasnomialSum
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.LucasTetrahedralRecurrence
public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.LucasPolytopicNumberHasSumInvLucasBracketMulSucc
public import MathlibExt.NumberTheory.LucasPolytopicNumberEvenLambertSeries
public import MathlibExt.NumberTheory.LucasPolytopicNumberDerivative

/-!
# Simplicial `d`-polytopic numbers on Lucas sequences

Statements from Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas
Sequences*, Journal of Integer Sequences 28 (2025), Article 25.5.6 (arXiv `2501.11490`).

The bracket `{n}_{s,t}` is `lucasBracket P n` and the fibonomial `[n, k]_{s,t}` is
`lucasnomial P n k` from `MathlibExt.NumberTheory.LucasPolytopicNumber`. The constants
`φ_{s,t}`, `φ'_{s,t}` are the two roots of `x ^ 2 - s x - t`; in the polynomial identities
they are any real pair with `φ + φ' = s` and `φ φ' = -t` (each identity was checked for both
orderings), and in the series identity they are the paper's
`φ = (s + √(s ^ 2 + 4 t)) / 2`, `φ' = (s - √(s ^ 2 + 4 t)) / 2`. The series identity
`hasSum_inv_lucasBracket_mul_succ` is proved in
`MathlibExt.NumberTheory.LucasPolytopicNumberHasSumInvLucasBracketMulSucc`. The paper's `q` is
`φ' / φ` (stated in the proof of Theorem 13), so
`(φ^d x; q)_{d+1} = ∏_{k ≤ d} (1 - φ^{d-k} φ'^k x)`.
-/

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
