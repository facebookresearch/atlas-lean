/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integral values of generating functions of Fibonacci polynomials

Statements from Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating
Functions of Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024.

For positive integers `a`, `b` the paper's polynomials `F_i(x)` (`F_0 = 0`, `F_1 = 1`) and
`L_i(x)` (`L_0 = 2`, `L_1 = ax`), both with `G_{i+2}(x) = ax G_{i+1}(x) + b G_i(x)`, are the
existing `generalizedFibonacciPolynomial` sequences over `ℤ[X]`. The generating functions are the
rational functions `f(x, t) = t / (1 - axt - bt²)` and `l(x, t) = (2 - axt) / (1 - axt - bt²)`.
The paper's case `d = 1` of its `√d` sequences is the evaluation at `x = 1`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
public import MathlibExt.NumberTheory.LucasSequence

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- The paper's Fibonacci polynomials `F_i(x)` with parameters `a`, `b`. -/
local notation "𝔽[" a ", " b "]" =>
  generalizedFibonacciPolynomial 0 1 (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

/-- The paper's Lucas polynomials `L_i(x)` with parameters `a`, `b`. -/
local notation "𝕃[" a ", " b "]" =>
  generalizedFibonacciPolynomial 2 (C ((a : ℕ) : ℤ) * X) (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

/-- A polynomial with integer coefficients, viewed as a rational function over `ℚ`. -/
local notation:max "ι" p:max => algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.map (Int.castRingHom ℚ) p)

/-- Theorem 1.2: if `b ∣ a` and `q(x) ∈ ℚ(x)`, then `f(x, q(x)) ∈ ℤ[x]` if and only if
`q(x) = F_i(x) / F_{i+1}(x)` for some `i ∈ ℕ` or `q(x) = -F_{i+1}(x) / (b F_i(x))` for some
`i ≥ 1`.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Theorem 1.2
(`fq-2024-tsuno05142024-thm-1.2`). -/
public theorem_wanted fibonacciPolyGenFun_mem_intPoly_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (q : RatFunc ℚ) :
    (∃ P : ℤ[X], q / (1 - (a : RatFunc ℚ) * RatFunc.X * q - (b : RatFunc ℚ) * q ^ 2) = ι P) ↔
      (∃ i : ℕ, q = ι (𝔽[a, b] i) / ι (𝔽[a, b] (i + 1))) ∨
        ∃ i : ℕ, 0 < i ∧ q = -ι (𝔽[a, b] (i + 1)) / ((b : RatFunc ℚ) * ι (𝔽[a, b] i))

/-- Theorem 1.3: if `b ∣ a` and `q(x) ∈ ℚ(x)`, then `l(x, q(x)) ∈ ℤ[x]` if and only if
`q(x)` is one of `F_i(x) / F_{i+1}(x)`, `L_i(x) / L_{i+1}(x)`, `-L_{i+1}(x) / (b L_i(x))` for some
`i ∈ ℕ`, or `-F_{i+1}(x) / (b F_i(x))` for some `i ≥ 1`.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Theorem 1.3
(`fq-2024-tsuno05142024-thm-1.3`). -/
public theorem_wanted lucasPolyGenFun_mem_intPoly_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (q : RatFunc ℚ) :
    (∃ P : ℤ[X], (2 - (a : RatFunc ℚ) * RatFunc.X * q) /
        (1 - (a : RatFunc ℚ) * RatFunc.X * q - (b : RatFunc ℚ) * q ^ 2) = ι P) ↔
      (∃ i : ℕ, q = ι (𝔽[a, b] i) / ι (𝔽[a, b] (i + 1)) ∨
          q = ι (𝕃[a, b] i) / ι (𝕃[a, b] (i + 1)) ∨
          q = -ι (𝕃[a, b] (i + 1)) / ((b : RatFunc ℚ) * ι (𝕃[a, b] i))) ∨
        ∃ i : ℕ, 0 < i ∧ q = -ι (𝔽[a, b] (i + 1)) / ((b : RatFunc ℚ) * ι (𝔽[a, b] i))

/-- Theorem 1.4 (case `d = 1`): if `b ∣ a`, `q ∈ ℚ` and `F_i = F_i(1)`, then
`f(q) = q / (1 - aq - bq²) ∈ ℤ` if and only if `q = F_i / F_{i+1}` for some `i ∈ ℕ` or
`q = -F_{i+1} / (b F_i)` for some `i ≥ 1`.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Theorem 1.4
(`fq-2024-tsuno05142024-thm-1.4`). -/
public theorem_wanted fibonacciGenFun_eval_isInt_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (q : ℚ) :
    (∃ n : ℤ, q / (1 - a * q - b * q ^ 2) = n) ↔
      (∃ i : ℕ, q = (((𝔽[a, b] i).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ)) ∨
        ∃ i : ℕ, 0 < i ∧
          q = -(((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ) / (b * (((𝔽[a, b] i).eval 1 : ℤ) : ℚ))

/-- Theorem 1.5 (case `d = 1`): if `b ∣ a`, `q ∈ ℚ`, `F_i = F_i(1)` and `L_i = L_i(1)`, then
`l(q) = (2 - aq) / (1 - aq - bq²) ∈ ℤ` if and only if `q` is one of `F_i / F_{i+1}`,
`L_i / L_{i+1}`, `-L_{i+1} / (b L_i)` for some `i ∈ ℕ`, or `-F_{i+1} / (b F_i)` for some `i ≥ 1`.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Theorem 1.5
(`fq-2024-tsuno05142024-thm-1.5`). -/
public theorem_wanted lucasGenFun_eval_isInt_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (q : ℚ) :
    (∃ n : ℤ, (2 - a * q) / (1 - a * q - b * q ^ 2) = n) ↔
      (∃ i : ℕ, q = (((𝔽[a, b] i).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ) ∨
          q = (((𝕃[a, b] i).eval 1 : ℤ) : ℚ) / (((𝕃[a, b] (i + 1)).eval 1 : ℤ) : ℚ) ∨
          q = -(((𝕃[a, b] (i + 1)).eval 1 : ℤ) : ℚ) / (b * (((𝕃[a, b] i).eval 1 : ℤ) : ℚ))) ∨
        ∃ i : ℕ, 0 < i ∧
          q = -(((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ) / (b * (((𝔽[a, b] i).eval 1 : ℤ) : ℚ))

/-- Corollary 1.6 (= Theorem 1.1, Bulawa and Lee): if `b ∣ a` and the rational `q` lies in the
interval of convergence `|q| < 2 / (a + √(a² + 4b))` of `f(t) = t / (1 - at - bt²)`, then
`f(q) ∈ ℤ` if and only if `q = F_{2i} / F_{2i+1}` for some `i ∈ ℕ`, where `F_i = F_i(1)`.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Corollary 1.6
(`fq-2024-tsuno05142024-cor-1.6`) and Theorem 1.1 (`fq-2024-tsuno05142024-thm-1.1`). -/
public theorem_wanted fibonacciGenFun_eval_isInt_iff_of_abs_lt_radius {a b : ℕ} (ha : 0 < a)
    (hb : 0 < b) (hba : b ∣ a) {q : ℚ}
    (hq : |(q : ℝ)| < 2 / (a + Real.sqrt (a ^ 2 + 4 * b))) :
    (∃ n : ℤ, q / (1 - a * q - b * q ^ 2) = n) ↔
      ∃ i : ℕ, q = (((𝔽[a, b] (2 * i)).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (2 * i + 1)).eval 1 : ℤ) : ℚ)

/-- Corollary 1.7: if `b ∣ a`, `a ≠ 1` and the rational `q` lies in the interval of convergence
`|q| < 2 / (a + √(a² + 4b))` of `l(t) = (2 - at) / (1 - at - bt²)`, then `l(q) ∈ ℤ` if and only
if `q = F_{2i} / F_{2i+1}` or `q = L_{2i+1} / L_{2i+2}` for some `i ∈ ℕ`, where `F_i = F_i(1)` and
`L_i = L_i(1)`.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Corollary 1.7
(`fq-2024-tsuno05142024-cor-1.7`). -/
public theorem_wanted lucasGenFun_eval_isInt_iff_of_abs_lt_radius {a b : ℕ} (ha : 0 < a)
    (ha1 : a ≠ 1) (hb : 0 < b) (hba : b ∣ a) {q : ℚ}
    (hq : |(q : ℝ)| < 2 / (a + Real.sqrt (a ^ 2 + 4 * b))) :
    (∃ n : ℤ, (2 - a * q) / (1 - a * q - b * q ^ 2) = n) ↔
      ∃ i : ℕ, q = (((𝔽[a, b] (2 * i)).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (2 * i + 1)).eval 1 : ℤ) : ℚ) ∨
        q = (((𝕃[a, b] (2 * i + 1)).eval 1 : ℤ) : ℚ) / (((𝕃[a, b] (2 * i + 2)).eval 1 : ℤ) : ℚ)

/-- Corollary 1.8 (`a = 1`, hence `b = 1`): if the rational `q` satisfies
`|q| < 2 / (1 + √5)`, then `(2 - q) / (1 - q - q²) ∈ ℤ` if and only if `q = -1/2`, or
`q = F_{2i} / F_{2i+1}` or `q = L_{2i+1} / L_{2i+2}` for some `i ∈ ℕ` (Fibonacci and Lucas
numbers).

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Corollary 1.8
(`fq-2024-tsuno05142024-cor-1.8`). -/
public theorem_wanted lucasNumberGenFun_eval_isInt_iff_of_abs_lt_radius {q : ℚ}
    (hq : |(q : ℝ)| < 2 / (1 + Real.sqrt 5)) :
    (∃ n : ℤ, (2 - q) / (1 - q - q ^ 2) = n) ↔
      (∃ i : ℕ, q = (Nat.fib (2 * i) : ℚ) / Nat.fib (2 * i + 1) ∨
        q = (lucasNumber (2 * i + 1) : ℚ) / lucasNumber (2 * i + 2)) ∨ q = -1 / 2

/-- Proposition 2.1: if `P(x), Q(x) ∈ ℚ[x]` have nonnegative leading coefficients and
`P(x)² - (a²x² + 4b) Q(x)² = 4(-b)^{r₀}` with `r₀ ∈ {0, 1}`, then there is `n ∈ ℕ` with
`b^⌊n/2⌋ P(x) = L_n(x)`, `b^⌊n/2⌋ Q(x) = F_n(x)` and `n ≡ r₀ (mod 2)`.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024,
Proposition 2.1 (`fq-2024-tsuno05142024-prop-2.1`). -/
public theorem_wanted fibLucasPoly_of_pell_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {P Q : ℚ[X]} (hP : 0 ≤ P.leadingCoeff) (hQ : 0 ≤ Q.leadingCoeff) {r₀ : ℕ} (hr₀ : r₀ ≤ 1)
    (h : P ^ 2 - (C ((a : ℚ) ^ 2) * X ^ 2 + C (4 * (b : ℚ))) * Q ^ 2 = C (4 * (-(b : ℚ)) ^ r₀)) :
    ∃ n : ℕ, C ((b : ℚ) ^ (n / 2)) * P = (𝕃[a, b] n).map (Int.castRingHom ℚ) ∧
      C ((b : ℚ) ^ (n / 2)) * Q = (𝔽[a, b] n).map (Int.castRingHom ℚ) ∧ n % 2 = r₀

/-- Proposition 2.2: if `b ∣ a`, `b` is squarefree and `P, Q ∈ ℕ` satisfy
`P² - (a² + 4b) Q² = -4b`, then `b^n P = L_{2n+1}` and `b^n Q = F_{2n+1}` for some `n ∈ ℕ`, where
`F_i = F_i(1)` and `L_i = L_i(1)`.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024,
Proposition 2.2 (`fq-2024-tsuno05142024-prop-2.2`). -/
public theorem_wanted fibLucas_odd_of_pell_eq_of_squarefree {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (hsq : Squarefree b) {P Q : ℕ}
    (h : (P : ℤ) ^ 2 - (a ^ 2 + 4 * b) * Q ^ 2 = -4 * b) :
    ∃ n : ℕ, (b : ℤ) ^ n * P = (𝕃[a, b] (2 * n + 1)).eval 1 ∧
      (b : ℤ) ^ n * Q = (𝔽[a, b] (2 * n + 1)).eval 1

/-- Proposition 2.3: if `b ∣ a` and `P, Q ∈ ℕ` satisfy `P² - (a² + 4b) Q² = -4b`, then
`b^n P = L_{2n+1}` and `b^n Q = F_{2n+1}` for some `n ∈ ℕ`, where `F_i = F_i(1)` and
`L_i = L_i(1)`.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024,
Proposition 2.3 (`fq-2024-tsuno05142024-prop-2.3`). -/
public theorem_wanted fibLucas_odd_of_pell_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b ∣ a)
    {P Q : ℕ} (h : (P : ℤ) ^ 2 - (a ^ 2 + 4 * b) * Q ^ 2 = -4 * b) :
    ∃ n : ℕ, (b : ℤ) ^ n * P = (𝕃[a, b] (2 * n + 1)).eval 1 ∧
      (b : ℤ) ^ n * Q = (𝔽[a, b] (2 * n + 1)).eval 1

end

end MetaMathlibExt
