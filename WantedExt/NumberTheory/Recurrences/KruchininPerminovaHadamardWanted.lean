/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Identities and Hadamard products of generalized sequences

Statement from Vladimir V. Kruchinin and Maria Y. Perminova,
"Identities and Hadamard Product of the Generalized Fibonacci,
Lucas, Catalan, and Harmonic Numbers", *Journal of Integer
Sequences* 28 (2025), Article 25.8.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Perminova/perm3.html>).

The paper's generalized Fibonacci and Lucas numbers have
generating functions `x / (1 - a x - b x ^ 2)` and
`(2 - a x) / (1 - a x - b x ^ 2)`, so they are the Lucas
sequences `U(P, Q)` and `V(P, Q)` with `P = a` and `Q = -b`,
here `MetaMathlibExt.lucasU` and `MetaMathlibExt.lucasV`.
Note this is only an integer specialization of the paper's
Proposition 1: the paper allows real parameters `a, b`
(cf. `MetaMathlibExt.AbGeneralizedFibonacciSequence`),
whereas `LucasSequenceParams` requires integer `P, Q`
with `Q ≠ 0`, i.e. integer `a` and nonzero integer `b`.
The identity below was verified
numerically for `(P, Q)` among seven sample pairs and
`m, n ≤ 12`.

Theorem 2, Theorem 3 and Corollaries 4 and 5 use the same
integer specialization (`a = P`, `b = -Q`). Theorem 3 is
stated analytically near `0`; Corollaries 4 and 5 are stated
as identities of formal power series over `ℚ`, the square
roots being the power series with constant term `1`.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted

/-- **Proposition 1** (integer specialization): for the
generalized Fibonacci numbers `F_n` and Lucas numbers
`L_n` with integer parameters `a` and nonzero integer
`b` (the paper allows real `a, b`),
`2 F_{m + n} = F_m L_n + L_m F_n`.

Source: Vladimir V. Kruchinin and Maria Y. Perminova,
"Identities and Hadamard Product of the Generalized
Fibonacci, Lucas, Catalan, and Harmonic Numbers",
Proposition 1. -/
theorem_wanted two_mul_lucasU_add
    (params : MetaMathlibExt.LucasSequenceParams) (m n : ℕ) :
    2 * MetaMathlibExt.lucasU params (m + n) =
      MetaMathlibExt.lucasU params m * MetaMathlibExt.lucasV params n +
        MetaMathlibExt.lucasV params m * MetaMathlibExt.lucasU params n

/-- **Theorem 2** (integer specialization): for a symmetric
array `T` (`T_{i, j} = T_{j, i}`) and
`p_n = ∑_{i=0}^n T_{n-i, i}`,
`p_n F_{kn + 2m} = ∑_{i=0}^n T_{n-i, i} L_{ki + m} F_{k(n-i) + m}`
for all `k, m, n ∈ ℕ`.

Source: Vladimir V. Kruchinin and Maria Y. Perminova,
"Identities and Hadamard Product of the Generalized
Fibonacci, Lucas, Catalan, and Harmonic Numbers",
Journal of Integer Sequences 28 (2025), Article 25.8.8, Theorem 2 (`jis-2025-25.8.8-thm-2`). `T` is
real as in
the paper; the paper's hypothesis `T_{i, n-i} = T_{n-i, i}`
for all `i ≤ n` is symmetry of `T`. -/
theorem_wanted sum_symm_mul_lucasU_eq_sum_mul_lucasV_mul_lucasU
    (params : MetaMathlibExt.LucasSequenceParams) (T : ℕ → ℕ → ℝ)
    (hT : ∀ i j, T i j = T j i) (k m n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), T (n - i) i) *
        (MetaMathlibExt.lucasU params (k * n + 2 * m) : ℝ) =
      ∑ i ∈ Finset.range (n + 1),
        T (n - i) i * (MetaMathlibExt.lucasV params (k * i + m) : ℝ) *
          (MetaMathlibExt.lucasU params (k * (n - i) + m) : ℝ)

/-- **Theorem 3** (integer specialization, sign corrected):
with `a = P`, `b = -Q` and `a ^ 2 + 4 b > 0`, near `0`,
`∑_n H_n F_n x ^ n = -U₅(x)`, where
`U₅(x) = ((2 - a x) / √(a² + 4b) · log((2 - √(a² + 4b) x - a x) /
(2 + √(a² + 4b) x - a x)) + x log(1 - a x - b x²)) /
(2 (1 - a x - b x²))`.

Source: Vladimir V. Kruchinin and Maria Y. Perminova,
"Identities and Hadamard Product of the Generalized
Fibonacci, Lucas, Catalan, and Harmonic Numbers",
Journal of Integer Sequences 28 (2025), Article 25.8.8, Theorem 3 (`jis-2025-25.8.8-thm-3`). As
printed the
left factor is `log(x - 1) / (1 - x)`; read as
`log(1 - x) / (1 - x) = -H(x)` the printed identity is
`F(x) * (-H(x)) = U₅(x)`, which is stated here. The paper's
proof claims `∑ H_n F_n x ^ n = U₅(x)`, which is off by the
sign (for `a = b = 1`, `x = 0.1`: series `0.11943`,
`U₅ = -0.11943`); the paper's own evaluation
`∑ H_n F_n / 2 ^ n = 6 log(1 + φ) / √5 + 2 log 2` equals
`-U₅(1/2)`. The radius `r` is left existential; `a² + 4b > 0`
keeps the square root real. -/
theorem_wanted hasSum_harmonic_mul_lucasU
    (params : MetaMathlibExt.LucasSequenceParams)
    (hdisc : 0 < params.p ^ 2 - 4 * params.q) :
    ∃ r > 0, ∀ x : ℝ, |x| < r →
      HasSum (fun n : ℕ => (harmonic n : ℝ) * (MetaMathlibExt.lucasU params n : ℝ) * x ^ n)
        (-(((2 - (params.p : ℝ) * x) / Real.sqrt ((params.p : ℝ) ^ 2 - 4 * params.q) *
              Real.log ((2 - Real.sqrt ((params.p : ℝ) ^ 2 - 4 * params.q) * x -
                  (params.p : ℝ) * x) /
                (2 + Real.sqrt ((params.p : ℝ) ^ 2 - 4 * params.q) * x -
                  (params.p : ℝ) * x)) +
            x * Real.log (1 - (params.p : ℝ) * x + (params.q : ℝ) * x ^ 2)) /
          (2 * (1 - (params.p : ℝ) * x + (params.q : ℝ) * x ^ 2))))

/-- **Corollary 4** (integer specialization): with `a = P`,
`b = -Q`, `V₂(x) = ∑_n C_n L_{n+1} x ^ n` satisfies
`V₂(x) = (1 - √((1 - 2 a x + √(1 - 4 a x - 16 b x²)) / 2)) / x`.

Source: Vladimir V. Kruchinin and Maria Y. Perminova,
"Identities and Hadamard Product of the Generalized
Fibonacci, Lucas, Catalan, and Harmonic Numbers",
Journal of Integer Sequences 28 (2025), Article 25.8.8, Corollary 4 (`jis-2025-25.8.8-cor-4`).
Stated over
`ℚ⟦X⟧` with `S` the square root of `1 - 4 a X - 16 b X²` with
constant term `1`; the outer square root is removed by
squaring `1 - X V₂` (both sides have constant term `1`). -/
theorem_wanted catalan_mul_lucasV_succ_powerSeries
    (params : MetaMathlibExt.LucasSequenceParams) (S : PowerSeries ℚ)
    (hS0 : PowerSeries.constantCoeff S = 1)
    (hS : S ^ 2 = 1 - PowerSeries.C (4 * (params.p : ℚ)) * PowerSeries.X +
      PowerSeries.C (16 * (params.q : ℚ)) * PowerSeries.X ^ 2) :
    2 * (1 - PowerSeries.X *
        PowerSeries.mk
            (fun n => ((catalan n : ℚ) * (MetaMathlibExt.lucasV params (n + 1) : ℚ)))) ^ 2 =
      1 - PowerSeries.C (2 * (params.p : ℚ)) * PowerSeries.X + S

/-- **Corollary 5** (integer specialization): with `a = P`,
`b = -Q`, `V₃(x) = ∑_n C_n F_n x ^ n` satisfies
`V₃(x) = (1 - √((2 b √(1 - 4 a x - 16 b x²) + 4 a b x + 2 b + a²) /
(4 b + a²))) / (2 b x)`.

Source: Vladimir V. Kruchinin and Maria Y. Perminova,
"Identities and Hadamard Product of the Generalized
Fibonacci, Lucas, Catalan, and Harmonic Numbers",
Journal of Integer Sequences 28 (2025), Article 25.8.8, Corollary 5 (`jis-2025-25.8.8-cor-5`).
Stated over
`ℚ⟦X⟧` with `S` the square root of `1 - 4 a X - 16 b X²` with
constant term `1`; the outer square root is removed by
squaring `1 - 2 b X V₃` and multiplying by `4 b + a²` (when
`4 b + a² = 0` both sides vanish). -/
theorem_wanted catalan_mul_lucasU_powerSeries
    (params : MetaMathlibExt.LucasSequenceParams) (S : PowerSeries ℚ)
    (hS0 : PowerSeries.constantCoeff S = 1)
    (hS : S ^ 2 = 1 - PowerSeries.C (4 * (params.p : ℚ)) * PowerSeries.X +
      PowerSeries.C (16 * (params.q : ℚ)) * PowerSeries.X ^ 2) :
    PowerSeries.C ((params.p : ℚ) ^ 2 - 4 * params.q) *
        (1 + PowerSeries.C (2 * (params.q : ℚ)) * PowerSeries.X *
          PowerSeries.mk (fun n => ((catalan n : ℚ) * (MetaMathlibExt.lucasU params n : ℚ)))) ^ 2 =
      PowerSeries.C (-2 * (params.q : ℚ)) * S -
        PowerSeries.C (4 * (params.p : ℚ) * params.q) * PowerSeries.X +
        PowerSeries.C ((params.p : ℚ) ^ 2 - 2 * params.q)

end MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted
