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

/-- **Theorem 2.** For `n ≥ 1`,
`[n + d, d + 1] = ∑_{k=1}^n φ^{(d+1)(n-k)} φ'^{k-1} [k + d - 1, d]`, and the same with `φ`
and `φ'` exchanged.

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

/-- **Theorem 3.** (1) `[n + 1, 2] = t [n, 2] + {n}²`; (2) for `n ≥ 1`,
`φ'^{n-1} [n + 1, 2] + φ^{n+1} [n, 2] = (⟨n⟩ / {2}) {n}²` with `⟨n⟩ = φⁿ + φ'ⁿ`;
(3) `[n + 1, 2] = ∑_{k=1}^n t^{n-k} {k}²`.

Parts (1) and (3) are stated for every `n ≥ 0`.

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

/-- **Theorem 4.** `[n + 2, 2]² - t² [n + 1, 2]² = (({n + 2} + t {n}) / s) {n + 1}³`.

Stated for every `n ≥ 0`.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 4
(`jis-2025-25.5.6-thm-4`). -/
public theorem_wanted lucasTriangular_sq_sub_sq (P : LucasParameters) (n : ℕ) :
    lucasnomial P (n + 2) 2 ^ 2 - P.t ^ 2 * lucasnomial P (n + 1) 2 ^ 2 =
      (lucasBracket P (n + 2) + P.t * lucasBracket P n) / P.s * lucasBracket P (n + 1) ^ 3

/-- **Theorem 5.** `∑_{k=1}^n t^{2(n-k)} (({k + 1} + t {k - 1}) / s) {k}³ = [n + 1, 2]²`.

Stated for every `n ≥ 0`.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 5
(`jis-2025-25.5.6-thm-5`). -/
public theorem_wanted sum_cubes_eq_lucasTriangular_sq (P : LucasParameters) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, P.t ^ (2 * (n - k)) *
        ((lucasBracket P (k + 1) + P.t * lucasBracket P (k - 1)) / P.s) * lucasBracket P k ^ 3 =
      lucasnomial P (n + 1) 2 ^ 2

/-- **Corollary 6.** Sum-of-cubes analogues for the Fibonacci, Pell, Jacobsthal and Mersenne
numbers, and Warnaar's `q`-identity
`∑_{k=1}^n q^{2(n-k)} ((1 - q^{2k})/(1 - q²)) ((1 - q^k)/(1 - q))² = [n + 1, 2]_q²`.

Jacobsthal numbers are `lucasU ⟨1, -2, _⟩`. The Gaussian binomial is written as
`(1 - q^{n+1})(1 - q^n) / ((1 - q)(1 - q²))`, for real `q ≠ ±1`. All parts for every `n ≥ 0`.

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

/-- **Theorem 7.** `[n + 3, 3] = s t [n + 2, 3] + {n + 1} [n + 2, 2]` for `n ≥ 0`.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 7
(`jis-2025-25.5.6-thm-7`). -/
public theorem_wanted lucasTetrahedral_recurrence (P : LucasParameters) (n : ℕ) :
    lucasnomial P (n + 3) 3 =
      P.s * P.t * lucasnomial P (n + 2) 3 + lucasBracket P (n + 1) * lucasnomial P (n + 2) 2

/-- The Lucas derivative `D_{φ,φ'}` for distinct roots `φ ≠ φ'` of `x ^ 2 - s x - t`:
`(D f)(x) = (f(φ x) - f(φ' x)) / ((φ - φ') x)` for `x ≠ 0`, and `f'(0)` at `x = 0`.

The paper's separate definition for `s² + 4t = 0` is not covered; when `f` is not
differentiable at `0`, the value at `0` is Mathlib's junk `deriv f 0 = 0`.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
noncomputable def lucasDerivative (φ φ' : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then deriv f 0 else (f (φ * x) - f (φ' * x)) / ((φ - φ') * x)

/-- The Lucas derivative away from `0` is the difference quotient.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
theorem lucasDerivative_of_ne_zero (φ φ' : ℝ) (f : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    lucasDerivative φ φ' f x = (f (φ * x) - f (φ' * x)) / ((φ - φ') * x) := by
  simp [lucasDerivative, hx]

/-- The Lucas derivative at `0` is the ordinary derivative at `0`.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
theorem lucasDerivative_zero (φ φ' : ℝ) (f : ℝ → ℝ) :
    lucasDerivative φ φ' f 0 = deriv f 0 := by
  simp [lucasDerivative]

/-- The Lucas derivative of the identity is `1` at every point, for `φ ≠ φ'`.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
theorem lucasDerivative_id {φ φ' : ℝ} (h : φ ≠ φ') (x : ℝ) :
    lucasDerivative φ φ' (fun y => y) x = 1 := by
  by_cases hx : x = 0
  · simp [lucasDerivative, hx]
  · rw [lucasDerivative_of_ne_zero _ _ _ hx, ← sub_mul]
    exact div_self (mul_ne_zero (sub_ne_zero.mpr h) hx)

/-- **Theorem 8.** For `n ≥ 1`, `D_{φ,φ'}ⁿ (1 / (1 - x)) = {n}! / (φⁿ x; q)_{n+1}`.

With `q = φ' / φ`, `(φⁿ x; q)_{n+1} = ∏_{k ≤ n} (1 - φ^{n-k} φ'^k x)`. Stated for real
`φ ≠ φ'` with `φ + φ' = s`, `φ φ' = -t` (the paper's `s² + 4t ≠ 0`; the identity is symmetric
in `φ, φ'`), at every real `x` where the denominator is nonzero (including `x = 0`), and
extended to `n = 0`.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 8
(`jis-2025-25.5.6-thm-8`). -/
public theorem_wanted iterate_lucasDerivative_inv_one_sub (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) (hne : φ ≠ φ') (n : ℕ) (x : ℝ)
    (hx : ∏ k ∈ Finset.range (n + 1), (1 - φ ^ (n - k) * φ' ^ k * x) ≠ 0) :
    (lucasDerivative φ φ')^[n] (fun y => 1 / (1 - y)) x =
      lucasFactorial P n / ∏ k ∈ Finset.range (n + 1), (1 - φ ^ (n - k) * φ' ^ k * x)

/-- **Theorem 9.** The generating function of the simplicial `d`-Lucas-polytopic numbers:
`∑_{n ≥ 1} [n + d - 1, d] xⁿ = x / (φ^d x; q)_{d+1}`.

Stated as an identity of formal power series with the denominator cleared, and with
`q = φ' / φ` eliminated: `(φ^d x; q)_{d+1} = ∏_{k ≤ d} (1 - φ^{d-k} φ'^k x)`.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 9
(`jis-2025-25.5.6-thm-9`). -/
public theorem_wanted lucasPolytopic_generatingFunction (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) (d : ℕ) :
    PowerSeries.mk (fun n => if n = 0 then 0 else lucasPolytopicNumber P n d) *
        ∏ k ∈ Finset.range (d + 1), (1 - PowerSeries.C (φ ^ (d - k) * φ' ^ k) * PowerSeries.X) =
      PowerSeries.X

/-- **Theorem 10.** The generating function of the squared Lucas-triangular numbers:
`∑_{n ≥ 1} [n + 1, 2]² xⁿ = (x + ({4}φ - φ⁴)x² - {3}φ³φ'³x³ + ({3}φ⁷φ'³ - {4}φ⁶φ'³)x⁴) /
((1 - t²x)(1 - φ'⁴x)(φ⁴x; q)₄)`.

Stated as an identity of formal power series with the denominator cleared, and with
`(φ⁴x; q)₄ = ∏_{k < 4} (1 - φ^{4-k} φ'^k x)`.

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

/-- **Theorem 11.** With `φ' = (s - √(s² + 4t)) / 2` and `L(x) = ∑_{n ≥ 1} xⁿ / (1 - xⁿ)` the
Lambert series, `∑_{n ≥ 1} tⁿ / {2n} = √(s² + 4t) (L(φ'² / t) - L(φ'⁴ / t²))`.

The hypotheses `0 < s` and `0 < s² + 4t` make `φ'` real with `|φ'| < φ`, so both Lambert
arguments lie in `(-1, 1)`; the left series is asserted to converge.

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

/-- **Theorem 13.** With `φ = (s + √(s² + 4t)) / 2` and the Lucas logarithm
`ln_{s,t}(1 - x) = -∑_{n ≥ 1} xⁿ / {n}`,
`∑_{n ≥ 1} 1 / ({n}{n + 1}) = φ - (1 + t) ln_{s,t}(1 + φ / t)`.

Added hypotheses: `0 < s` and `0 < s² + 4t` (the paper's `0 < |q| < 1`, real `φ`) and
`1 < |t|`, the paper's convergence range `x ∈ (-|φ|, |φ|)` for `ln_{s,t}(1 - x)` at
`x = -φ / t`. Without `1 < |t|` the logarithm series diverges (`s = t = 1`: its terms
`(-φ)ⁿ / Fₙ` do not tend to `0`). `ln_{s,t}(1 + φ / t)` is written out as
`-∑' n, (-φ / t)^{n+1} / {n + 1}`.

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
