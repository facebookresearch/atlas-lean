/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.PellLucasNumber
public import MathlibExt.NumberTheory.GibonacciNumber
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-! Sums `∑_{α} m_n(α) a_1^{α_1} ⋯ a_n^{α_n}` over `α_1 + 2α_2 + ⋯ + nα_n = n`, with
`m_n(α)` the multinomial coefficient of `(α_1, …, α_n)`, are written below as sums over
the compositions of `n` of the product of `a` over the parts, which is the same number. -/

/-- Generating function form of Trudi's formula: for the `n × n` Toeplitz–Hessenberg
matrices `A_n = (a_{i-j+1})` (`a_0` on the superdiagonal, zeros above it), with
`f(x) = ∑_{n ≥ 1} det(A_n) x^n`, `g(x) = ∑_{i ≥ 1} a_i x^i` and `a_0 ≠ 0`,
`f(x) = -(1/a_0) g(-a_0 x) / (1 + (1/a_0) g(-a_0 x))`, stated in the cleared form
`f (1 + h) = -h` with `h(x) = (1/a_0) g(-a_0 x)`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Lemma 2. -/
public theorem_wanted toeplitzHessenberg_det_generatingFunction {K : Type*} [Field K]
    (a : ℕ → K) (ha0 : a 0 ≠ 0) :
    PowerSeries.mk (fun n => if n = 0 then 0 else
        Matrix.det (fun i j : Fin n =>
          if (j : ℕ) ≤ (i : ℕ) + 1 then a ((i : ℕ) + 1 - (j : ℕ)) else 0)) *
      (1 + PowerSeries.C (a 0)⁻¹ *
        PowerSeries.rescale (-a 0) (PowerSeries.mk fun i => if i = 0 then 0 else a i)) =
    -(PowerSeries.C (a 0)⁻¹ *
        PowerSeries.rescale (-a 0) (PowerSeries.mk fun i => if i = 0 then 0 else a i))

/-- For the Toeplitz–Hessenberg determinants `u_n = det(U_n)` with `a_0 = a` and
`a_i = (bi + c) d^i` (`i ≥ 1`), the generating function `u(x) = ∑_{n ≥ 1} u_n x^n` equals
`dx(b + c + acdx) / (1 + d(2a - b - c)x + ad^2(a - c)x^2)`, stated in the cleared form
(the denominator has constant term `1`).

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Lemma 3. -/
public theorem_wanted toeplitzHessenberg_det_linear_mul_pow_generatingFunction
    {R : Type*} [CommRing R] (a b c d : R) :
    PowerSeries.mk (fun n => if n = 0 then 0 else
        Matrix.det (fun i j : Fin n =>
          if (j : ℕ) ≤ (i : ℕ) + 1 then
            (if (i : ℕ) + 1 - (j : ℕ) = 0 then a
              else (b * (((i : ℕ) + 1 - (j : ℕ) : ℕ) : R) + c) * d ^ ((i : ℕ) + 1 - (j : ℕ)))
          else 0)) *
      (1 + PowerSeries.C (d * (2 * a - b - c)) * X +
        PowerSeries.C (a * d ^ 2 * (a - c)) * X ^ 2) =
    PowerSeries.C d * X * (PowerSeries.C (b + c) + PowerSeries.C (a * c * d) * X)

/-- Multinomial-sum formulas for `F_{2n}`, `F_{3n-1}` and `P_{n-1}` (`n ≥ 1`):
`F_{2n} = ∑ m_n(s) 1^{s_1} 2^{s_2} ⋯ n^{s_n}`,
`F_{3n-1} = 2^{n-1} ∑ m_n(s) (1/1)^{s_1} (3/2)^{s_2} ⋯ ((2n-1)/2^{n-1})^{s_n}`, and
`P_{n-1} = 2^{n-1} ∑_{2s_1 + 3s_2 + ⋯ + ns_{n-1} = n} m_{n-1}(s) (1/2)^{s_1} (2/4)^{s_2}
⋯ ((n-1)/2^{n-1})^{s_{n-1}}`, the last written as a composition sum with weight
`(j-1)/2^{j-1}` for a part `j` (which vanishes on parts `1`). `P` is the Pell sequence
`pellNumber`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Proposition 1. -/
public theorem_wanted fib_pell_composition_sums (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fib (2 * n) : ℚ) =
        ∑ c : Composition n, ∏ i : Fin c.length, (c.blocksFun i : ℚ) ∧
      (Nat.fib (3 * n - 1) : ℚ) = 2 ^ (n - 1) *
        ∑ c : Composition n, ∏ i : Fin c.length,
          (2 * (c.blocksFun i : ℚ) - 1) / 2 ^ (c.blocksFun i - 1) ∧
      (pellNumber (n - 1) : ℚ) = 2 ^ (n - 1) *
        ∑ c : Composition n, ∏ i : Fin c.length,
          ((c.blocksFun i : ℚ) - 1) / 2 ^ (c.blocksFun i - 1)

/-- For `n ≥ 1`, `∑ m_n(α) 1^{α_1} 3^{α_2} ⋯ ((n+1) 2^{n-2})^{α_n}` equals
`5^{(n-1)/2} F_{n+1}` for odd `n` and `5^{(n-2)/2} L_{n+1}` for even `n`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 1, equation (8). -/
public theorem_wanted composition_sum_succ_mul_two_zpow (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, ∏ i : Fin c.length,
        ((c.blocksFun i : ℚ) + 1) * (2 : ℚ) ^ ((c.blocksFun i : ℤ) - 2) =
      if Odd n then 5 ^ ((n - 1) / 2) * (Nat.fib (n + 1) : ℚ)
      else 5 ^ ((n - 2) / 2) * (lucasNumber (n + 1) : ℚ)

/-- Multinomial-sum formulas, for `n ≥ 1`:
`∑ m_n(α) ∏ ((-1)^{i-1}(i+2))^{α_i} = F_{n+3}`,
`∑ m_n(α) ∏ ((-1)^{i-1}(4i+2))^{α_i} = 2F_{3n+1}`,
`∑ m_n(α) ∏ ((-2)^{i-1}(2i+3))^{α_i} = J_{n+3}`,
`∑ m_n(α) ∏ (i 2^{i-1})^{α_i} = J_{2n}`, and `∑ m_n(α) ∏ (4i)^{α_i} = 2P_{2n}`, with
`J = lucasU (1, -2)` (Jacobsthal) and `P = pellNumber` (Pell). Identity (14) is not
formalized (its weights are garbled in the extraction).

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 3, equations (13) and
(15)-(18). -/
public theorem_wanted fib_jacobsthal_pell_composition_sums (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, ∏ i : Fin c.length,
        (-1 : ℚ) ^ (c.blocksFun i - 1) * ((c.blocksFun i : ℚ) + 2) = Nat.fib (n + 3) ∧
      ∑ c : Composition n, ∏ i : Fin c.length,
        (-1 : ℚ) ^ (c.blocksFun i - 1) * (4 * (c.blocksFun i : ℚ) + 2) =
          2 * Nat.fib (3 * n + 1) ∧
      ∑ c : Composition n, ∏ i : Fin c.length,
        (-2 : ℚ) ^ (c.blocksFun i - 1) * (2 * (c.blocksFun i : ℚ) + 3) =
          lucasU ⟨1, -2, by decide⟩ (n + 3) ∧
      ∑ c : Composition n, ∏ i : Fin c.length,
        (c.blocksFun i : ℚ) * 2 ^ (c.blocksFun i - 1) = lucasU ⟨1, -2, by decide⟩ (2 * n) ∧
      ∑ c : Composition n, ∏ i : Fin c.length, 4 * (c.blocksFun i : ℚ) =
          2 * (pellNumber (2 * n) : ℚ)

/-- Among the Fibonacci subsequences `k_n = F_{ℓn+m}` (`ℓ ≥ 1`, `m ≥ 0`), only `F_{n+3}` and
`F_{2n}` are good: there are constants `a, b, c, d` with `k_n = u_n(a, b, c, d)` for all
`n ≥ 1`, where `u_n(a, b, c, d)` is the `n × n` Toeplitz–Hessenberg determinant with
`a_0 = a` and `a_i = (bi + c) d^i` of Lemma 3
(`toeplitzHessenberg_det_linear_mul_pow_generatingFunction`).
"Good" is the paper's definition (a Horadam sequence `v_n` is good if `v_n = u_n(a, b, c, d)`
for all `n ≥ 1` for some constants), taken over `ℂ`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Proposition 2
(`integers-2025-A97-prop-2`). -/
public theorem_wanted fib_mul_add_eq_toeplitzHessenberg_det_iff (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) :
    (∃ a b c d : ℂ, ∀ n : ℕ, 1 ≤ n →
      (Nat.fib (ℓ * n + m) : ℂ) =
        Matrix.det (fun i j : Fin n =>
          if (j : ℕ) ≤ (i : ℕ) + 1 then
            (if (i : ℕ) + 1 - (j : ℕ) = 0 then a
              else (b * (((i : ℕ) + 1 - (j : ℕ) : ℕ) : ℂ) + c) * d ^ ((i : ℕ) + 1 - (j : ℕ)))
          else 0)) ↔
      (ℓ = 1 ∧ m = 3) ∨ (ℓ = 2 ∧ m = 0)

/-- Multinomial-sum formulas with `√2` weights, for `n ≥ 1`:
`∑_{β* = n} m_{n-1}(β) 1^{β_1} (2√2)^{β_2} ⋯ ((n-1)√(2^{n-2}))^{β_{n-1}}` equals `√2 P_{n-1}`
for odd `n` and `Q_{n-1}/2` for even `n` (identity (10), the sum over
`2β_1 + 3β_2 + ⋯ + nβ_{n-1} = n`, written as a composition sum of `n` with weight
`(j-1)√2^{j-2}` for a part `j`, which vanishes on parts `1`), and
`∑ m_n(α) (√2)^{α_1} (3/2)^{α_2} ⋯ ((n+1)/√(2^n))^{α_n}` equals `P_{n+1}/√2` for odd `n` and
`Q_{n+1}/4` for even `n` (identity (11)). `P` is `pellNumber` and `Q` is the Pell–Lucas
sequence `pellLucas` (`Q_0 = Q_1 = 2`).

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 2 (`integers-2025-A97-cor-2`). -/
public theorem_wanted pell_pellLucas_composition_sums_sqrt_two (n : ℕ) (hn : 1 ≤ n) :
    ∑ c : Composition n, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) - 1) * Real.sqrt 2 ^ (c.blocksFun i - 2) =
      (if Odd n then Real.sqrt 2 * (pellNumber (n - 1) : ℝ)
        else (pellLucas (n - 1) : ℝ) / 2) ∧
    ∑ c : Composition n, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) + 1) / Real.sqrt 2 ^ c.blocksFun i =
      (if Odd n then (pellNumber (n + 1) : ℝ) / Real.sqrt 2
        else (pellLucas (n + 1) : ℝ) / 4)

/-- Toeplitz–Hessenberg determinants with Oresme entries `O_k = k/2^k`, for `n ≥ 1`, where
`det(a_0; a_1, …, a_n)` is the determinant of the `n × n` matrix with `a_0` on the
superdiagonal and `a_{i-j+1}` on and below the diagonal:
(19) `det(-2; O_2, …, O_{n+1}) = 5^{(n-1)/2} F_{n+1}/2^n` (odd `n`), `5^{(n-2)/2} L_{n+1}/2^n`
(even `n`); (20) `det(-4; O_0, …, O_{n-1}) = 2^{(n+1)/2} P_{n-1}` (odd `n`),
`2^{(n-2)/2} Q_{n-1}` (even `n`); (21) `det(-1/2; O_2, …, O_{n+1}) = 2^{-(3n+1)/2} P_{n+1}` (odd
`n`), `2^{-(3n+4)/2} Q_{n+1}` (even `n`); (22) `det(1/4; O_3, …, O_{n+2}) = 2^{-3n} F_{n+3}`;
(23) `det(-1/8; O_4, …, O_{n+3}) = 2^{-(3n+2)} F_{2n+4}`;
(24) `det(1/4; O_3, O_5, …, O_{2n+1}) = 2^{-(4n-1)} F_{3n+1}`;
(25) `det(1/4; O_5, O_7, …, O_{2n+3}) = 2^{-5n} J_{n+3}`;
(26) `det(-2; O_1, …, O_n) = 2^{-n} J_{2n}`;
(27) `det(-1/4; O_1, …, O_n) = 2^{-(3n-1)} P_{2n}`. The exponents of (20) are typeset
`2^{(n+1/2)}` and `2^{(n-2/2)}` in the paper; they are read as `2^{(n+1)/2}` and `2^{(n-2)/2}`
(the literal `2^{n+1/2}` is irrational while the determinant is rational: for `n = 3` the
determinant is `8 = 2^2 P_2`). Negative powers of `2` are written as divisions.
`J = lucasU (1, -2)` (Jacobsthal), `P = pellNumber`, `Q = pellLucas`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 4 (`integers-2025-A97-cor-4`). -/
public theorem_wanted oresme_toeplitzHessenberg_det_formulas (n : ℕ) (hn : 1 ≤ n) :
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-2 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) + 1 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) + 1)) else 0) =
      (if Odd n then 5 ^ ((n - 1) / 2) / 2 ^ n * (Nat.fib (n + 1) : ℚ)
        else 5 ^ ((n - 2) / 2) / 2 ^ n * (lucasNumber (n + 1) : ℚ)) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-4 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) - 1 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) - 1)) else 0) =
      (if Odd n then 2 ^ ((n + 1) / 2) * (pellNumber (n - 1) : ℚ)
        else 2 ^ ((n - 2) / 2) * (pellLucas (n - 1) : ℚ)) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-1 / 2 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) + 1 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) + 1)) else 0) =
      (if Odd n then (pellNumber (n + 1) : ℚ) / 2 ^ ((3 * n + 1) / 2)
        else (pellLucas (n + 1) : ℚ) / 2 ^ ((3 * n + 4) / 2)) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (1 / 4 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) + 2 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) + 2)) else 0) =
      (Nat.fib (n + 3) : ℚ) / 2 ^ (3 * n) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-1 / 8 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) + 3 : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ) + 3)) else 0) =
      (Nat.fib (2 * n + 4) : ℚ) / 2 ^ (3 * n + 2) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (1 / 4 : ℚ) else
          ((2 * ((i : ℕ) + 1 - (j : ℕ)) + 1 : ℕ) : ℚ) / 2 ^ (2 * ((i : ℕ) + 1 - (j : ℕ)) + 1))
        else 0) =
      (Nat.fib (3 * n + 1) : ℚ) / 2 ^ (4 * n - 1) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (1 / 4 : ℚ) else
          ((2 * ((i : ℕ) + 1 - (j : ℕ)) + 3 : ℕ) : ℚ) / 2 ^ (2 * ((i : ℕ) + 1 - (j : ℕ)) + 3))
        else 0) =
      (lucasU ⟨1, -2, by decide⟩ (n + 3) : ℚ) / 2 ^ (5 * n) ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-2 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ))) else 0) =
      (lucasU ⟨1, -2, by decide⟩ (2 * n) : ℚ) / 2 ^ n ∧
    Matrix.det (fun i j : Fin n => if (j : ℕ) ≤ (i : ℕ) + 1 then
        (if (i : ℕ) + 1 - (j : ℕ) = 0 then (-1 / 4 : ℚ) else
          (((i : ℕ) + 1 - (j : ℕ) : ℕ) : ℚ) / 2 ^ ((i : ℕ) + 1 - (j : ℕ))) else 0) =
      (pellNumber (2 * n) : ℚ) / 2 ^ (3 * n - 1)

/-- Horadam sequences as composition sums: if `p, q, r, s ∈ ℂ` satisfy
`(q - r)^2 = 4s(p - 1) ≠ 0` and `v_n = r v_{n-1} + s v_{n-2}` with `v_0 = p`, `v_1 = q`, then
for `n ≥ 1`, `v_n = ∑_α ((r-q)/2)^{n-|α|} m_n(α) ∏_i ((q + 2ps/(r-q)) i - 2ps/(r-q))^{α_i}`,
written as a sum over the compositions of `n` (identity (12)). The converse part of the
theorem is `horadam_composition_sum_recurrence`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 1 (`integers-2025-A97-thm-1`). -/
public theorem_wanted horadam_eq_composition_sum (p q r s : ℂ)
    (h : (q - r) ^ 2 = 4 * s * (p - 1)) (h0 : 4 * s * (p - 1) ≠ 0) (v : ℕ → ℂ)
    (hv0 : v 0 = p) (hv1 : v 1 = q) (hv : ∀ k, v (k + 2) = r * v (k + 1) + s * v k)
    (n : ℕ) (hn : 1 ≤ n) :
    v n = ∑ c : Composition n, ((r - q) / 2) ^ (n - c.length) *
      ∏ i : Fin c.length,
        ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q))

/-- Converse part of Theorem 1: if `(q - r)^2 = 4s(p - 1) ≠ 0`, the sequence `w_n` defined for
`n ≥ 1` by the composition sum of identity (12) satisfies `w_n = r w_{n-1} + s w_{n-2}` for
`n ≥ 3`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 1 (`integers-2025-A97-thm-1`). -/
public theorem_wanted horadam_composition_sum_recurrence (p q r s : ℂ)
    (h : (q - r) ^ 2 = 4 * s * (p - 1)) (h0 : 4 * s * (p - 1) ≠ 0) (n : ℕ) (hn : 3 ≤ n) :
    ∑ c : Composition n, ((r - q) / 2) ^ (n - c.length) *
        ∏ i : Fin c.length,
          ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q)) =
      r * ∑ c : Composition (n - 1), ((r - q) / 2) ^ (n - 1 - c.length) *
        ∏ i : Fin c.length,
          ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q)) +
      s * ∑ c : Composition (n - 2), ((r - q) / 2) ^ (n - 2 - c.length) *
        ∏ i : Fin c.length,
          ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q))

/-- Translates of a Gibonacci sequence `G` (`G_0 = y`, `G_1 = z` non-negative integers, not
both zero) as composition sums: for `m ≥ 3`, `n ≥ 1` and `D` either square root of
`(-1)^m (y^2 + yz - z^2)` (the two roots give the paper's two sign choices),
`G_{n+m} = (G_{m+2} + G_m + 2D)^{n-1} / (G_{m+1}^{n-2} (G_m + D)^n)
  · ∑_α (-(G_m + D)^2/(G_{m+2} + G_m + 2D))^{n-|α|} m_n(α) ∏_i (Di + G_m)^{α_i}`
(identity (28)). The uniqueness part is `gibonacci_mul_add_eq_toeplitzHessenberg_det_iff`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 2 (`integers-2025-A97-thm-2`). -/
public theorem_wanted gibonacci_add_eq_composition_sum (y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyz : y ≠ 0 ∨ z ≠ 0) (m : ℕ) (hm : 3 ≤ m) (D : ℂ)
    (hD : D ^ 2 = (-1) ^ m * ((y : ℂ) ^ 2 + y * z - z ^ 2)) (n : ℕ) (hn : 1 ≤ n) :
    (gibonacciNumber y z (n + m) : ℂ) =
      ((gibonacciNumber y z (m + 2) : ℂ) + gibonacciNumber y z m + 2 * D) ^ (n - 1) /
        ((gibonacciNumber y z (m + 1) : ℂ) ^ ((n : ℤ) - 2) *
          ((gibonacciNumber y z m : ℂ) + D) ^ n) *
      ∑ c : Composition n,
        (-((gibonacciNumber y z m : ℂ) + D) ^ 2 /
          ((gibonacciNumber y z (m + 2) : ℂ) + gibonacciNumber y z m + 2 * D)) ^
            (n - c.length) *
        ∏ i : Fin c.length, (D * (c.blocksFun i : ℂ) + gibonacciNumber y z m)

/-- Uniqueness in Theorem 2: for a Gibonacci sequence `G` as in
`gibonacci_add_eq_composition_sum`, `m ≥ 3` and a constant `k ≠ 0`, there are constants
`a, b, c, d` with `k G_{n+m} = u_n(a, b, c, d)` for all `n ≥ 1` (the `n × n` Toeplitz–Hessenberg
determinant with `a_0 = a` and `a_i = (bi + c) d^i`) if and only if
`k = (G_{m+2} + G_m + 2D)/G_{m+1}^2` for a square root `D` of `(-1)^m (y^2 + yz - z^2)`, so there
are exactly the two identities (28). The hypothesis `k ≠ 0` excludes the trivial `k = 0`, which
is `u_n(a, b, c, 0) = 0`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 2 (`integers-2025-A97-thm-2`). -/
public theorem_wanted gibonacci_mul_add_eq_toeplitzHessenberg_det_iff (y z : ℤ) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hyz : y ≠ 0 ∨ z ≠ 0) (m : ℕ) (hm : 3 ≤ m) (k : ℂ) (hk : k ≠ 0) :
    (∃ a b c d : ℂ, ∀ n : ℕ, 1 ≤ n →
      k * (gibonacciNumber y z (n + m) : ℂ) =
        Matrix.det (fun i j : Fin n =>
          if (j : ℕ) ≤ (i : ℕ) + 1 then
            (if (i : ℕ) + 1 - (j : ℕ) = 0 then a
              else (b * (((i : ℕ) + 1 - (j : ℕ) : ℕ) : ℂ) + c) * d ^ ((i : ℕ) + 1 - (j : ℕ)))
          else 0)) ↔
      ∃ D : ℂ, D ^ 2 = (-1) ^ m * ((y : ℂ) ^ 2 + y * z - z ^ 2) ∧
        k = ((gibonacciNumber y z (m + 2) : ℂ) + gibonacciNumber y z m + 2 * D) /
          (gibonacciNumber y z (m + 1) : ℂ) ^ 2

/-- Modular subsequences of a Gibonacci sequence `G` (`G_0 = y`, `G_1 = z` non-negative
integers, not both zero) as composition sums: for `ℓ ≥ 1`, `m ≥ 0`, `n ≥ 1` and `E` either square
root of `(-1)^ℓ G_ℓ (G_ℓ - L_ℓ y) + y^2` (`m` even) or `(-1)^ℓ G_{ℓ+1} (G_{ℓ+1} - L_ℓ z) + z^2`
(`m` odd),
`G_{ℓn+m} = (L_ℓ G_{ℓ+m} - 2(-1)^ℓ G_m + 2E)^{n-1} / (G_{ℓ+m}^{n-2} ((-1)^{ℓ+1} G_m + E)^n)
  · ∑_α (-((-1)^{ℓ+1} G_m + E)^2/(L_ℓ G_{ℓ+m} - 2(-1)^ℓ G_m + 2E))^{n-|α|} m_n(α)
    ∏_i (Ei - (-1)^ℓ G_m)^{α_i}`
(identity (35)), provided `m ≥ ℓ + 2` or `G_{ℓ+m} ((-1)^{ℓ+1} G_m + E) ≠ 0` (the paper's
sufficient condition for `0 ≤ m ≤ ℓ + 1`).

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 3 (`integers-2025-A97-thm-3`). -/
public theorem_wanted gibonacci_mul_add_eq_composition_sum (y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyz : y ≠ 0 ∨ z ≠ 0) (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (E : ℂ)
    (hE : E ^ 2 = if Even m then
        (-1) ^ ℓ * (gibonacciNumber y z ℓ : ℂ) *
          ((gibonacciNumber y z ℓ : ℂ) - lucasNumber ℓ * y) + (y : ℂ) ^ 2
      else
        (-1) ^ ℓ * (gibonacciNumber y z (ℓ + 1) : ℂ) *
          ((gibonacciNumber y z (ℓ + 1) : ℂ) - lucasNumber ℓ * z) + (z : ℂ) ^ 2)
    (hm : ℓ + 2 ≤ m ∨
      (gibonacciNumber y z (ℓ + m) : ℂ) * ((-1) ^ (ℓ + 1) * gibonacciNumber y z m + E) ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) :
    (gibonacciNumber y z (ℓ * n + m) : ℂ) =
      ((lucasNumber ℓ : ℂ) * gibonacciNumber y z (ℓ + m) -
          2 * (-1) ^ ℓ * gibonacciNumber y z m + 2 * E) ^ (n - 1) /
        ((gibonacciNumber y z (ℓ + m) : ℂ) ^ ((n : ℤ) - 2) *
          ((-1) ^ (ℓ + 1) * (gibonacciNumber y z m : ℂ) + E) ^ n) *
      ∑ c : Composition n,
        (-((-1) ^ (ℓ + 1) * (gibonacciNumber y z m : ℂ) + E) ^ 2 /
          ((lucasNumber ℓ : ℂ) * gibonacciNumber y z (ℓ + m) -
            2 * (-1) ^ ℓ * gibonacciNumber y z m + 2 * E)) ^ (n - c.length) *
        ∏ i : Fin c.length,
          (E * (c.blocksFun i : ℂ) - (-1) ^ ℓ * gibonacciNumber y z m)

/-- Fibonacci and Lucas translates as composition sums: for `m ≥ 0` and `n ≥ 1`, with `lam` a
square root of `(-1)^{m+1}` (`± i` for even `m`, `± 1` for odd `m`; only `lam = 1` when
`m = 1`),
`F_{n+m} = (L_{m+1} + 2 lam)^{n-1} / (F_{m+1}^{n-2} (F_m + lam)^n)
  · ∑_α (-(F_m + lam)^2/(L_{m+1} + 2 lam))^{n-|α|} m_n(α) ∏_j (lam j + F_m)^{α_j}` (30), and with
`rho` a square root of `5(-1)^m`,
`L_{n+m} = (L_{m+2} + L_m + 2 rho)^{n-1} / (L_{m+1}^{n-2} (L_m + rho)^n)
  · ∑_α (-(L_m + rho)^2/(L_{m+2} + L_m + 2 rho))^{n-|α|} m_n(α) ∏_j (rho j + L_m)^{α_j}` (31).
The companion identity of (13) is `fib_add_three_companion_composition_sum`; the discussion of
good sequences and rational `k` after the corollary is not formalized.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 5 (`integers-2025-A97-cor-5`). -/
public theorem_wanted fib_lucas_add_eq_composition_sum (m n : ℕ) (hn : 1 ≤ n) :
    (∀ lam : ℂ, lam ^ 2 = (-1) ^ (m + 1) → (m = 1 → lam = 1) →
      (Nat.fib (n + m) : ℂ) =
        ((lucasNumber (m + 1) : ℂ) + 2 * lam) ^ (n - 1) /
          ((Nat.fib (m + 1) : ℂ) ^ ((n : ℤ) - 2) * ((Nat.fib m : ℂ) + lam) ^ n) *
        ∑ c : Composition n,
          (-((Nat.fib m : ℂ) + lam) ^ 2 / ((lucasNumber (m + 1) : ℂ) + 2 * lam)) ^
              (n - c.length) *
          ∏ j : Fin c.length, (lam * (c.blocksFun j : ℂ) + Nat.fib m)) ∧
    (∀ rho : ℂ, rho ^ 2 = 5 * (-1) ^ m →
      (lucasNumber (n + m) : ℂ) =
        ((lucasNumber (m + 2) : ℂ) + lucasNumber m + 2 * rho) ^ (n - 1) /
          ((lucasNumber (m + 1) : ℂ) ^ ((n : ℤ) - 2) * ((lucasNumber m : ℂ) + rho) ^ n) *
        ∑ c : Composition n,
          (-((lucasNumber m : ℂ) + rho) ^ 2 /
            ((lucasNumber (m + 2) : ℂ) + lucasNumber m + 2 * rho)) ^ (n - c.length) *
          ∏ j : Fin c.length, (rho * (c.blocksFun j : ℂ) + lucasNumber m))

/-- The companion of identity (13) (minus sign for `lam` in (30) with `m = 3`): for `n ≥ 1`,
`(5/9) F_{n+3} = (-1/3)^n ∑_α m_n(α) ∏_i (5i - 10)^{α_i}`.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 5 (`integers-2025-A97-cor-5`). -/
public theorem_wanted fib_add_three_companion_composition_sum (n : ℕ) (hn : 1 ≤ n) :
    5 / 9 * (Nat.fib (n + 3) : ℚ) =
      (-1 / 3) ^ n * ∑ c : Composition n, ∏ i : Fin c.length, (5 * (c.blocksFun i : ℚ) - 10)

/-- Gibonacci half-sequences as composition sums: for `G` with `G_0 = y`, `G_1 = z`
non-negative integers, not both zero, `m ≥ 0`, `n ≥ 1` and `F` a square root of
`(-1)^{m+1} (y^2 + yz - z^2)`,
`G_{2n+m} = (G_{m+3} + G_{m+1} + 2F)^{n-1} / (G_{m+2}^{n-2} (-G_m + F)^n)
  · ∑_α (-(-G_m + F)^2/(G_{m+3} + G_{m+1} + 2F))^{n-|α|} m_n(α) ∏_i (Fi - G_m)^{α_i}` (43),
for both roots when `m ≥ 4`; for `m ≤ 3` the hypothesis `F ≠ G_m` excludes exactly the paper's
cases (i) `m = 0, 2y = z`, (ii) `m = 1, y = z`, (iii) `m = 2, y = 0`, (iv) `m = 3, z = 0` with the
positive root (there the positive root equals `G_m`, and only the negative choice is valid).

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 6 (`integers-2025-A97-cor-6`). -/
public theorem_wanted gibonacci_two_mul_add_eq_composition_sum (y z : ℤ) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hyz : y ≠ 0 ∨ z ≠ 0) (m : ℕ) (F : ℂ)
    (hF : F ^ 2 = (-1) ^ (m + 1) * ((y : ℂ) ^ 2 + y * z - z ^ 2))
    (hm : 4 ≤ m ∨ F ≠ (gibonacciNumber y z m : ℂ)) (n : ℕ) (hn : 1 ≤ n) :
    (gibonacciNumber y z (2 * n + m) : ℂ) =
      ((gibonacciNumber y z (m + 3) : ℂ) + gibonacciNumber y z (m + 1) + 2 * F) ^ (n - 1) /
        ((gibonacciNumber y z (m + 2) : ℂ) ^ ((n : ℤ) - 2) *
          (-(gibonacciNumber y z m : ℂ) + F) ^ n) *
      ∑ c : Composition n,
        (-(-(gibonacciNumber y z m : ℂ) + F) ^ 2 /
          ((gibonacciNumber y z (m + 3) : ℂ) + gibonacciNumber y z (m + 1) + 2 * F)) ^
            (n - c.length) *
        ∏ i : Fin c.length, (F * (c.blocksFun i : ℂ) - gibonacciNumber y z m)

end

end MetaMathlibExt
