/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Pairs of intertwined integer sequences (Kassel–Reutenauer)

Statements from C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4
(arXiv:2507.15780).

Notation used throughout:

* `Polynomial.Chebyshev.C ℤ k` is the paper's monic Chebyshev polynomial
  `T̄_k(X)` (`T̄_k(q + q⁻¹) = q^k + q^{-k}`, `T̄_0 = 2`, `T̄_1 = X`).
* `chebyshevCPartialSum n` is the paper's `F_n(X) = 1 + ∑_{k=1}^n T̄_k(X)`.
* `kasselReutenauerPoly n` is the paper's `P̄_n(X)`, with
  `P̄_n(q + q⁻¹) = P_n(q) / q^{n-1}`; in the ring `ℤ[T;T⁻¹]` of Laurent
  polynomials in `q = T 1`, the Laurent polynomial `P_n(q) / q^{n-1}` is
  `aeval (T 1 + T (-1)) (kasselReutenauerPoly n)` and, by the paper's relation
  `C_n(q) / q^n = q⁻¹ (q - 1)² P_n(q) / q^{n-1}`, the Laurent polynomial
  `C_n(q) / q^n` is `(T 1 - 2 + T (-1)) * aeval (T 1 + T (-1)) (kasselReutenauerPoly n)`.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- The coefficient `a_{n,i}` of the paper: the number of divisors `d` of `n`
with `(i + √(2n + i²))/2 < d ≤ i + √(2n + i²)`. Over `ℕ` the two inequalities
are equivalent to `d (d - 2i) ≤ 2n` and `n < 2d (d - i)` (truncated subtraction;
for `d ≤ i`, resp. `d ≤ 2i`, the truncated forms give the correct truth value).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, display (2.3), quoting
their earlier Theorem 1.3 of *Complete determination of the zeta function of the
Hilbert scheme of n points on a two-dimensional torus*. -/
public def kasselReutenauerCoeff (n i : ℕ) : ℕ :=
  ((Nat.divisors n).filter fun d => d * (d - 2 * i) ≤ 2 * n ∧ n < 2 * d * (d - i)).card

/-- The polynomial `P̄_n(X) = a_{n,0} + ∑_{i=1}^{n-1} a_{n,i} T̄_i(X)` of degree
`n - 1`, characterized in the paper by `P̄_n(q + q⁻¹) = P_n(q)/q^{n-1}`, where
`(q - 1)² P_n(q)` counts the ideals of codimension `n` of
`𝔽_q[x, y, x⁻¹, y⁻¹]`. The ideal-counting definition is not formalized; the
polynomial is defined by the paper's explicit expansion (2.4) with coefficients
(2.3). Meaningful for `n ≥ 1` (the value at `n = 0` is `0`).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (2.1)–(2.4) and Table 2. -/
public noncomputable def kasselReutenauerPoly (n : ℕ) : ℤ[X] :=
  (kasselReutenauerCoeff n 0 : ℤ[X]) +
    ∑ i ∈ Finset.Icc 1 (n - 1), (kasselReutenauerCoeff n i : ℤ[X]) * Chebyshev.C ℤ i

/-- The polynomial `F_n(X) = 1 + ∑_{k=1}^n T̄_k(X)`, where `T̄_k` is the monic
Chebyshev polynomial (`Polynomial.Chebyshev.C`); equivalently `F_0 = 1` and
`F_n = F_{n-1} + T̄_n`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6)–(3.7). -/
public noncomputable def chebyshevCPartialSum (n : ℕ) : ℤ[X] :=
  1 + ∑ k ∈ Finset.Icc 1 n, Chebyshev.C ℤ k

/-- Characteristic values `a_{1,0} = 1`, `a_{2,0} = a_{2,1} = 1`,
`a_{3,0} = 0`, `a_{3,1} = a_{3,2} = 1`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (2.3) and Table 2. -/
public theorem kasselReutenauerCoeff_small :
    kasselReutenauerCoeff 1 0 = 1 ∧ kasselReutenauerCoeff 2 0 = 1 ∧
      kasselReutenauerCoeff 2 1 = 1 ∧ kasselReutenauerCoeff 3 0 = 0 ∧
      kasselReutenauerCoeff 3 1 = 1 ∧ kasselReutenauerCoeff 3 2 = 1 := by
  decide

/-- Characteristic value `P̄_1(X) = 1` (Table 2).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Table 2. -/
public theorem kasselReutenauerPoly_one : kasselReutenauerPoly 1 = 1 := by
  have h : kasselReutenauerCoeff 1 0 = 1 := by decide
  simp [kasselReutenauerPoly, h]

/-- Characteristic value `P̄_2(X) = X + 1` (Table 2).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Table 2. -/
public theorem kasselReutenauerPoly_two : kasselReutenauerPoly 2 = X + 1 := by
  have h0 : kasselReutenauerCoeff 2 0 = 1 := by decide
  have h1 : kasselReutenauerCoeff 2 1 = 1 := by decide
  simp [kasselReutenauerPoly, h0, h1, add_comm]

/-- Characteristic value `P̄_3(X) = X² + X - 2` (Table 2).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Table 2. -/
public theorem kasselReutenauerPoly_three : kasselReutenauerPoly 3 = X ^ 2 + X - 2 := by
  have h0 : kasselReutenauerCoeff 3 0 = 0 := by decide
  have h1 : kasselReutenauerCoeff 3 1 = 1 := by decide
  have h2 : kasselReutenauerCoeff 3 2 = 1 := by decide
  have hI : Finset.Icc 1 (3 - 1) = {1, 2} := by decide
  rw [kasselReutenauerPoly, hI, Finset.sum_pair (by decide), h0, h1, h2]
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_add]
  rw [Chebyshev.C_one, Chebyshev.C_two]
  ring

/-- Characteristic value `F_0(X) = 1`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6). -/
public theorem chebyshevCPartialSum_zero : chebyshevCPartialSum 0 = 1 := by
  simp [chebyshevCPartialSum]

/-- Defining recurrence `F_{n+1}(X) = F_n(X) + T̄_{n+1}(X)`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6). -/
public theorem chebyshevCPartialSum_succ (n : ℕ) :
    chebyshevCPartialSum (n + 1) = chebyshevCPartialSum n + Chebyshev.C ℤ (n + 1 : ℕ) := by
  simp only [chebyshevCPartialSum, Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), add_assoc]

/-- Characteristic values `F_1(X) = X + 1` and `F_2(X) = X² + X - 1` (Table 4).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Table 4. -/
public theorem chebyshevCPartialSum_one_two :
    chebyshevCPartialSum 1 = X + 1 ∧ chebyshevCPartialSum 2 = X ^ 2 + X - 1 := by
  have h1 : chebyshevCPartialSum 1 = X + 1 := by
    rw [chebyshevCPartialSum_succ, chebyshevCPartialSum_zero]
    simp [add_comm]
  refine ⟨h1, ?_⟩
  rw [chebyshevCPartialSum_succ, h1]
  have hc : Chebyshev.C ℤ ((1 + 1 : ℕ) : ℤ) = X ^ 2 - 2 := by
    simpa using Chebyshev.C_two (R := ℤ)
  rw [hc]
  ring

/-- Positivity: for every `n ≥ 1` and every integer `N ≥ 2`, `P̄_n(N) > 0`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 2.1
(`jis-2026-26.4.4-prop-1`). -/
public theorem_wanted kasselReutenauerPoly_eval_pos (n : ℕ) (hn : 1 ≤ n) (N : ℤ) (hN : 2 ≤ N) :
    0 < (kasselReutenauerPoly n).eval N

/-- Multiplicativity at roots of unity of order `1, 2, 3, 4`: if `q ∈ ℂ` is a
primitive `d`-th root of unity with `d ∈ {1, 2, 3, 4}`, then
`n ↦ |P_n(q)| = |P̄_n(q + q⁻¹)|` is multiplicative. Here `|P_n(q)|` is written as
`‖P̄_n(q + q⁻¹)‖`, which equals it since `|q| = 1`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 2.2
(`jis-2026-26.4.4-prop-2`). -/
public theorem_wanted kasselReutenauerPoly_norm_multiplicative_rootOfUnity (q : ℂ) (d : ℕ)
    (hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4) (hq : IsPrimitiveRoot q d) (m n : ℕ) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hmn : m.Coprime n) :
    ‖aeval (q + q⁻¹) (kasselReutenauerPoly (m * n))‖ =
      ‖aeval (q + q⁻¹) (kasselReutenauerPoly m)‖ * ‖aeval (q + q⁻¹) (kasselReutenauerPoly n)‖

/-- Almost multiplicativity at a primitive sixth root of unity `ω`: for coprime
positive `m, n`, `|P_m(ω)| |P_n(ω)|` equals `|P_{mn}(ω)|` when
`(m, n) ≡ (0,1), (1,1), (1,2) (mod 3)`, equals `2 |P_{mn}(ω)|` when
`(m, n) ≡ (0,2)`, and `4 |P_{mn}(ω)|` when `(m, n) ≡ (2,2)`. As printed, the
residue pairs are ordered; `|P_n(ω)|` is written as `‖P̄_n(ω + ω⁻¹)‖`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 2.3
(`jis-2026-26.4.4-prop-3`). -/
public theorem_wanted kasselReutenauerPoly_norm_almost_multiplicative_sixth (ω : ℂ)
    (hω : IsPrimitiveRoot ω 6) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m.Coprime n) :
    ((m % 3 = 0 ∧ n % 3 = 1 ∨ m % 3 = 1 ∧ n % 3 = 1 ∨ m % 3 = 1 ∧ n % 3 = 2) →
        ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly m)‖ * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly n)‖ =
          ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly (m * n))‖) ∧
      (m % 3 = 0 ∧ n % 3 = 2 →
        ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly m)‖ * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly n)‖ =
          2 * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly (m * n))‖) ∧
      (m % 3 = 2 ∧ n % 3 = 2 →
        ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly m)‖ * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly n)‖ =
          4 * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly (m * n))‖)

/-- For coprime positive `m, n`, `P̄_{mn}(X)² - P̄_m(X)² P̄_n(X)²` is divisible
by `X (X + 1) (X² - 4)`, and moreover by `X (X + 1) (X² - 4) (X - 1)` when
`(m, n) ≡ (0,1), (1,1)` or `(1,2) (mod 3)`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 2.4
(`jis-2026-26.4.4-cor-4`). -/
public theorem_wanted kasselReutenauerPoly_sq_sub_dvd (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m.Coprime n) :
    X * (X + 1) * (X ^ 2 - 4) ∣
        kasselReutenauerPoly (m * n) ^ 2 - kasselReutenauerPoly m ^ 2 * kasselReutenauerPoly n ^ 2 ∧
      ((m % 3 = 0 ∧ n % 3 = 1 ∨ m % 3 = 1 ∧ n % 3 = 1 ∨ m % 3 = 1 ∧ n % 3 = 2) →
        X * (X + 1) * (X ^ 2 - 4) * (X - 1) ∣
          kasselReutenauerPoly (m * n) ^ 2 - kasselReutenauerPoly m ^ 2 * kasselReutenauerPoly n ^ 2)

/-- For an integer `N`, the function `n ↦ |P̄_n(N)|` (on positive integers) is
multiplicative if and only if `N ∈ {-2, -1, 0, 2}`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 2.5
(`jis-2026-26.4.4-prop-5`). -/
public theorem_wanted kasselReutenauerPoly_abs_eval_multiplicative_iff (N : ℤ) :
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m.Coprime n →
        |(kasselReutenauerPoly (m * n)).eval N| =
          |(kasselReutenauerPoly m).eval N| * |(kasselReutenauerPoly n).eval N|) ↔
      N = -2 ∨ N = -1 ∨ N = 0 ∨ N = 2

/-- Positivity of the monic Chebyshev polynomials: `T̄_k(x) > 0` for every
`k ≥ 0` and every real `x ≥ 2`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.1
(`jis-2026-26.4.4-prop-6`). -/
public theorem_wanted chebyshevC_eval_pos_of_two_le (k : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    0 < (Chebyshev.C ℝ k).eval x

/-- Trace formula: `T̄_k(X) = tr(M^k)` for the companion matrix
`M = !![X, -1; 1, 0]` and all `k ≥ 0`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.2
(`jis-2026-26.4.4-prop-7`). -/
public theorem_wanted chebyshevC_eq_trace_pow (k : ℕ) :
    Chebyshev.C ℤ k = Matrix.trace ((!![X, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ[X]) ^ k)

/-- Generating function: `∑_{n ≥ 0} F_n(X) tⁿ = (1 + t)/(1 - X t + t²)`, stated
as `(1 - X t + t²) · ∑ F_n(X) tⁿ = 1 + t` in `ℤ[X]⟦t⟧` (equivalent, since
`1 - X t + t²` is a unit there).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.3
(`jis-2026-26.4.4-prop-8`). -/
public theorem_wanted chebyshevCPartialSum_generatingFunction :
    (1 - PowerSeries.C X * PowerSeries.X + PowerSeries.X ^ 2) *
        PowerSeries.mk (fun n => chebyshevCPartialSum n) =
      (1 + PowerSeries.X : PowerSeries ℤ[X])

/-- Binomial expansion: for `n ≥ 1`,
`F_n(X) = ∑_{0 ≤ m ≤ n/2} (-1)^m C(n-m, m) X^{n-2m}
  + ∑_{0 ≤ m ≤ (n-1)/2} (-1)^m C(n-m-1, m) X^{n-2m-1}`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.4
(`jis-2026-26.4.4-prop-9`). -/
public theorem_wanted chebyshevCPartialSum_eq_binomial_sum (n : ℕ) (hn : 1 ≤ n) :
    chebyshevCPartialSum n =
      ∑ m ∈ Finset.range (n / 2 + 1), (-1 : ℤ[X]) ^ m * ((n - m).choose m : ℤ[X]) * X ^ (n - 2 * m) +
        ∑ m ∈ Finset.range ((n - 1) / 2 + 1),
          (-1 : ℤ[X]) ^ m * ((n - m - 1).choose m : ℤ[X]) * X ^ (n - 2 * m - 1)

/-- Top coefficients of `F_n`: for `n ≥ 5`,
`F_n(X) = Xⁿ + X^{n-1} - (n-1) X^{n-2} - (n-2) X^{n-3} + ((n-2)(n-3)/2) X^{n-4}
  + ((n-3)(n-4)/2) X^{n-5}` plus monomials of degree `≤ n - 6` (stated as: the
difference has degree `< n - 5`). The fractions are written `C(n-2, 2)` and
`C(n-3, 2)`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 3.5
(`jis-2026-26.4.4-cor-10`). -/
public theorem_wanted chebyshevCPartialSum_top_coeffs (n : ℕ) (hn : 5 ≤ n) :
    (chebyshevCPartialSum n -
        (X ^ n + X ^ (n - 1) - ((n - 1 : ℕ) : ℤ[X]) * X ^ (n - 2) - ((n - 2 : ℕ) : ℤ[X]) * X ^ (n - 3) +
          ((n - 2).choose 2 : ℤ[X]) * X ^ (n - 4) + ((n - 3).choose 2 : ℤ[X]) * X ^ (n - 5))).degree <
      ((n - 5 : ℕ) : WithBot ℕ)

/-- Linear recurrence: `F_{k+1}(X) = X F_k(X) - F_{k-1}(X)` for `k ≥ 1`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.6
(`jis-2026-26.4.4-prop-11`). -/
public theorem_wanted chebyshevCPartialSum_recurrence (k : ℕ) (hk : 1 ≤ k) :
    chebyshevCPartialSum (k + 1) = X * chebyshevCPartialSum k - chebyshevCPartialSum (k - 1)

/-- Approximation theorem: for `n ≥ 2`, `P̄_n(X) - F_{n-1}(X)` has degree
`< n/2 - 1`, i.e. every nonzero coefficient sits in a degree `k` with
`2k + 2 < n`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Theorem 4.1
(`jis-2026-26.4.4-thm-12`). -/
public theorem_wanted kasselReutenauerPoly_sub_chebyshevCPartialSum_coeff (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk : (kasselReutenauerPoly n - chebyshevCPartialSum (n - 1)).coeff k ≠ 0) :
    2 * k + 2 < n

/-- Top coefficients of `P̄_n`: for `n ≥ 10`,
`P̄_n(X) = X^{n-1} + X^{n-2} - (n-2) X^{n-3} - (n-3) X^{n-4}
  + ((n-3)(n-4)/2) X^{n-5} + ((n-4)(n-5)/2) X^{n-6}` plus monomials of degree
`≤ n - 7` (stated as: the difference has degree `< n - 6`). The fractions are
written `C(n-3, 2)` and `C(n-4, 2)`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 4.2
(`jis-2026-26.4.4-cor-13`). -/
public theorem_wanted kasselReutenauerPoly_top_coeffs (n : ℕ) (hn : 10 ≤ n) :
    (kasselReutenauerPoly n -
        (X ^ (n - 1) + X ^ (n - 2) - ((n - 2 : ℕ) : ℤ[X]) * X ^ (n - 3) -
          ((n - 3 : ℕ) : ℤ[X]) * X ^ (n - 4) + ((n - 3).choose 2 : ℤ[X]) * X ^ (n - 5) +
          ((n - 4).choose 2 : ℤ[X]) * X ^ (n - 6))).degree <
      ((n - 6 : ℕ) : WithBot ℕ)

/-- `a_{n,i} = 1` whenever `n/2 - 1 ≤ i ≤ n - 1` (for `n ≥ 1`); the lower bound
is written `n ≤ 2i + 2`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Lemma 4.3
(`jis-2026-26.4.4-lem-14`). -/
public theorem_wanted kasselReutenauerCoeff_eq_one (n i : ℕ) (hn : 1 ≤ n) (hi : n ≤ 2 * i + 2)
    (hi' : i ≤ n - 1) : kasselReutenauerCoeff n i = 1

/-- Odd-divisor formula: for `n ≥ 1`, with `r_n(d) = n/d - (d+1)/2`,
`P̄_n(X) = ∑_{d ∣ n, d odd, r_n(d) ≥ 0} F_{r_n(d)}(X)
  - ∑_{d ∣ n, d odd, r_n(d) < 0} F_{-r_n(d)-1}(X)`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Theorem 4.4
(`jis-2026-26.4.4-thm-16`). -/
public theorem_wanted kasselReutenauerPoly_eq_oddDivisor_sum (n : ℕ) (hn : 1 ≤ n) :
    kasselReutenauerPoly n =
      ∑ d ∈ (Nat.divisors n).filter (fun d => Odd d ∧ 0 ≤ ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)),
          chebyshevCPartialSum (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)).toNat -
        ∑ d ∈ (Nat.divisors n).filter (fun d => Odd d ∧ ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) < 0),
          chebyshevCPartialSum (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)) - 1).toNat

/-- `P̄_n(X) = F_{n-1}(X)` if and only if `n` is a power of `2` (for `n ≥ 1`).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 4.5
(`jis-2026-26.4.4-cor-17`). -/
public theorem_wanted kasselReutenauerPoly_eq_chebyshevCPartialSum_iff (n : ℕ) (hn : 1 ≤ n) :
    kasselReutenauerPoly n = chebyshevCPartialSum (n - 1) ↔ ∃ k : ℕ, n = 2 ^ k

/-- Representation formula for `C_n(q)/q^n` (in `ℤ[T;T⁻¹]`, `q = T 1`):
`C_n(q)/q^n = ∑ (-1)^h (q^a + q^{-a})` over all `h ≥ 1`, `a ∈ ℤ` with
`n = h (h + 1 + 2a)/2`; moreover, a solution `(a, h)` is determined by `|a|`.
Every solution satisfies `h ≤ 2n` and `|a| ≤ n`, so the sum is over a finite box.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Lemma 5.2
(`jis-2026-26.4.4-lem-22`). -/
public theorem_wanted kasselReutenauer_C_div_pow_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    (LaurentPolynomial.T 1 - 2 + LaurentPolynomial.T (-1)) *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (kasselReutenauerPoly n) =
      ∑ p ∈ (Finset.Icc 1 (2 * n) ×ˢ Finset.Icc (-(n : ℤ)) n).filter
          (fun p : ℕ × ℤ => (p.1 : ℤ) * (p.1 + 1 + 2 * p.2) = 2 * n),
        (-1) ^ p.1 * (LaurentPolynomial.T p.2 + LaurentPolynomial.T (-p.2)) ∧
    ∀ h h' : ℕ, ∀ a a' : ℤ, 1 ≤ h → 1 ≤ h' → (h : ℤ) * (h + 1 + 2 * a) = 2 * n →
      (h' : ℤ) * (h' + 1 + 2 * a') = 2 * n → |a| = |a'| → h = h' ∧ a = a'

/-- Increasing-sequence and odd-divisor formulas for `C_n(q)/q^n` (in
`ℤ[T;T⁻¹]`, `q = T 1`), `n ≥ 1`:

(i) `C_n(q)/q^n = ∑ (-1)^h (q^a + q^{-a})` over the increasing sequences
`IS(a, h) = {a+1, …, a+h}` (`h ≥ 1`) whose elements sum to `n`, and for given
`|a|` there is a unique such sequence (all such `(h, a)` lie in the box
`h ≤ 2n`, `|a| ≤ n`);

(ii) `C_n(q)/q^n = ∑_{d ∣ n, d odd} (q^{n/d - (d-1)/2} + q^{-n/d + (d-1)/2}
  - q^{n/d - (d+1)/2} - q^{-n/d + (d+1)/2})`, and the exponents `≠ 0` occurring
in this sum are pairwise distinct (the multiset of nonzero exponents is
duplicate-free).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Theorem 5.3
(`jis-2026-26.4.4-thm-23`). -/
public theorem_wanted kasselReutenauer_C_div_pow_increasingSequences (n : ℕ) (hn : 1 ≤ n) :
    ((LaurentPolynomial.T 1 - 2 + LaurentPolynomial.T (-1)) *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (kasselReutenauerPoly n) =
      ∑ p ∈ (Finset.Icc 1 (2 * n) ×ˢ Finset.Icc (-(n : ℤ)) n).filter
          (fun p : ℕ × ℤ => ∑ j ∈ Finset.Icc (p.2 + 1) (p.2 + p.1), j = n),
        (-1) ^ p.1 * (LaurentPolynomial.T p.2 + LaurentPolynomial.T (-p.2))) ∧
    (∀ h h' : ℕ, ∀ a a' : ℤ, 1 ≤ h → 1 ≤ h' → ∑ j ∈ Finset.Icc (a + 1) (a + h), j = n →
      ∑ j ∈ Finset.Icc (a' + 1) (a' + h'), j = n → |a| = |a'| → h = h' ∧ a = a') ∧
    ((LaurentPolynomial.T 1 - 2 + LaurentPolynomial.T (-1)) *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (kasselReutenauerPoly n) =
      ∑ d ∈ (Nat.divisors n).filter Odd,
        (LaurentPolynomial.T (((n / d : ℕ) : ℤ) - ((d - 1) / 2 : ℕ)) +
          LaurentPolynomial.T (-((n / d : ℕ) : ℤ) + ((d - 1) / 2 : ℕ)) -
          LaurentPolynomial.T (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)) -
          LaurentPolynomial.T (-((n / d : ℕ) : ℤ) + ((d + 1) / 2 : ℕ)))) ∧
    ((((Nat.divisors n).filter Odd).val.bind (fun d =>
        ({((n / d : ℕ) : ℤ) - ((d - 1) / 2 : ℕ), -((n / d : ℕ) : ℤ) + ((d - 1) / 2 : ℕ),
          ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ), -((n / d : ℕ) : ℤ) + ((d + 1) / 2 : ℕ)} :
          Multiset ℤ))).filter (· ≠ 0)).Nodup

/-- The sum of the absolute values of the coefficients of `C_n(q)` equals four
times the number of odd divisors of `n` (`n ≥ 1`). Stated for the Laurent
polynomial `C_n(q)/q^n`, which has the same coefficients.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 5.4
(`jis-2026-26.4.4-cor-24`). -/
public theorem_wanted kasselReutenauer_C_abs_coeff_sum (n : ℕ) (hn : 1 ≤ n) :
    ((LaurentPolynomial.T 1 - 2 + LaurentPolynomial.T (-1)) *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (kasselReutenauerPoly n)).coeff.sum (fun _ c => |c|) =
      4 * (((Nat.divisors n).filter Odd).card : ℤ)

/-- For `r ≥ 0`, `q^{r+1} + q^{-r-1} - q^r - q^{-r} = q⁻¹ (q - 1)² F_r(q + q⁻¹)`
in `ℤ[T;T⁻¹]` (`q = T 1`).

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Lemma 6.1
(`jis-2026-26.4.4-lem-26`). -/
public theorem_wanted chebyshevCPartialSum_laurent_identity (r : ℕ) :
    (LaurentPolynomial.T ((r : ℤ) + 1) + LaurentPolynomial.T (-(r : ℤ) - 1) -
        LaurentPolynomial.T (r : ℤ) - LaurentPolynomial.T (-(r : ℤ)) : LaurentPolynomial ℤ) =
      LaurentPolynomial.T (-1) * (LaurentPolynomial.T 1 - 1) ^ 2 *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (chebyshevCPartialSum r)

/-- Increasing-sequence formula for `P_n(q)/q^{n-1} = P̄_n(q + q⁻¹)` (in
`ℤ[T;T⁻¹]`, `q = T 1`), `n ≥ 1`: with `a = r_n(d) = n/d - (d+1)/2`, `h = d`,
`ǎ = -r_n(d) - 1`, `ȟ = 2n/d` and `IS(a, h) = {a+1, …, a+h}`,
`P_n(q)/q^{n-1} = ∑_{d ∣ n odd, r_n(d) ≥ 0} ∑_{i ∈ IS(ǎ,ȟ) \ IS(a,h)} q^i
  - ∑_{d ∣ n odd, r_n(d) < 0} ∑_{i ∈ IS(a,h) \ IS(ǎ,ȟ)} q^i`.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 6.2
(`jis-2026-26.4.4-prop-27`). -/
public theorem_wanted kasselReutenauerPoly_laurent_increasingSequences (n : ℕ) (hn : 1 ≤ n) :
    aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
        (kasselReutenauerPoly n) =
      ∑ d ∈ (Nat.divisors n).filter (fun d => Odd d ∧ 0 ≤ ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)),
          ∑ i ∈ Finset.Icc (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)))
                (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)) - 1 + ((2 * n / d : ℕ) : ℤ)) \
              Finset.Icc (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) + 1)
                (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) + d),
            LaurentPolynomial.T i -
        ∑ d ∈ (Nat.divisors n).filter (fun d => Odd d ∧ ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) < 0),
          ∑ i ∈ Finset.Icc (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) + 1)
                (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) + d) \
              Finset.Icc (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)))
                (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)) - 1 + ((2 * n / d : ℕ) : ℤ)),
            LaurentPolynomial.T i

/-- Local zeta function of the Hilbert scheme `H^n` of `n` points on the two-dimensional torus
over `𝔽_q`, `q = p^k`: for `n ≥ 1`,
`Z_{H^n/𝔽_q}(t) = ∏_{d ∣ n, d odd} (1 - q^{n+r_n(d)} t)(1 - q^{n-r_n(d)} t) /
((1 - q^{n+r_n(d)+1} t)(1 - q^{n-r_n(d)-1} t))`, where `r_n(d) = n/d - (d+1)/2`.
The zeta function is the formal power series `exp (∑_{m ≥ 1} N_m t^m / m)`, where `N_m`, the
number of `𝔽_{q^m}`-points of `H^n`, is the number of ideals of colength `n` in the Laurent
polynomial ring `𝔽_{q^m}[x^{±1}, y^{±1}]` (the group algebra of `ℤ × ℤ`), and `𝔽_{q^m}` is
`GaloisField p (k * m)`. The exponents `n ± r_n(d)`, `n + r_n(d) + 1`, `n - r_n(d) - 1` are
nonnegative; they are written as integer powers.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.4, Proposition 5.5 (`jis-2026-26.4.4-prop-25`). -/
public theorem_wanted hilbertSchemeTorus_zeta_eq_prod (p k n : ℕ) [Fact p.Prime] (hk : 0 < k)
    (hn : 1 ≤ n) :
    let q : ℚ := (p : ℚ) ^ k
    let N : ℕ → ℕ := fun m =>
      Nat.card {I : Ideal (AddMonoidAlgebra (GaloisField p (k * m)) (ℤ × ℤ)) //
        Module.finrank (GaloisField p (k * m))
          (AddMonoidAlgebra (GaloisField p (k * m)) (ℤ × ℤ) ⧸ I) = n}
    let r : ℕ → ℤ := fun d => ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)
    PowerSeries.subst (PowerSeries.mk fun m : ℕ => if m = 0 then (0 : ℚ) else (N m : ℚ) / m)
        (PowerSeries.exp ℚ) =
      ∏ d ∈ n.divisors.filter Odd,
        (1 - PowerSeries.C (q ^ ((n : ℤ) + r d)) * PowerSeries.X) *
          (1 - PowerSeries.C (q ^ ((n : ℤ) - r d)) * PowerSeries.X) *
          ((1 - PowerSeries.C (q ^ ((n : ℤ) + r d + 1)) * PowerSeries.X) *
            (1 - PowerSeries.C (q ^ ((n : ℤ) - r d - 1)) * PowerSeries.X))⁻¹

end

end MetaMathlibExt
