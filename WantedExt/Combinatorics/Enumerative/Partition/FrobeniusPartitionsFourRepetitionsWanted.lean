/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Congruences for generalized Frobenius partitions with 4 repetitions

Statements from Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17.

A generalized Frobenius partition (F-partition) of `n` is a two-rowed array of nonnegative
integers with `r` columns whose rows are nonincreasing and with `n = r + Σ aᵢ + Σ bᵢ`.
`φ_k(n)` counts those F-partitions of `n` in which no integer appears more than `k` times in
either row (Andrews); the paper studies `φ₄`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fintype.Pi
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- `φ_k(n)`, the number of generalized Frobenius partitions of `n` in which each integer
appears at most `k` times in each row. A row is recorded by its multiplicity function
`m : Fin (n + 1) → Fin (k + 1)` (`m i` copies of the entry `i`; entries of an F-partition of
`n` are at most `n`); the two rows have the same number `r = Σ mᵢ` of entries, and
`r + Σ aᵢ + Σ bᵢ = Σ (i + 1) m₁(i) + Σ i m₂(i) = n`.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Section 1 (definition of `φ_k(n)`, after
Andrews). -/
public def frobeniusPartitionRepCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin (n + 1) → Fin (k + 1)) × (Fin (n + 1) → Fin (k + 1)))).filter
    fun p => ∑ i : Fin (n + 1), (p.1 i : ℕ) = ∑ i : Fin (n + 1), (p.2 i : ℕ) ∧
      ∑ i : Fin (n + 1), (p.1 i : ℕ) * ((i : ℕ) + 1) +
        ∑ i : Fin (n + 1), (p.2 i : ℕ) * (i : ℕ) = n).card

/-- `φ₄(0) = 1` (the empty array) and `φ₄(1) = 1` (the single column `0 / 0`).

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Section 1 (definition of `φ_k(n)`). -/
public theorem frobeniusPartitionRepCount_four_zero_one :
    frobeniusPartitionRepCount 4 0 = 1 ∧ frobeniusPartitionRepCount 4 1 = 1 := by
  constructor <;> decide +kernel

/-- `φ₄(4n + 3) ≡ 0 (mod 2)` for all `n ≥ 0`.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 2 (`integers-2025-A17-thm-2`). -/
public theorem_wanted frobeniusPartitionRepCount_four_four_mul_add_three_mod_two (n : ℕ) :
    frobeniusPartitionRepCount 4 (4 * n + 3) ≡ 0 [MOD 2]

/-- If `N` is a positive integer not divisible by `5`, then `φ₄(2N + 1) ≡ 0 (mod 2)`.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 3 (`integers-2025-A17-thm-3`). -/
public theorem_wanted frobeniusPartitionRepCount_four_two_mul_add_one_mod_two {N : ℕ}
    (hN : 0 < N) (h5 : ¬ 5 ∣ N) :
    frobeniusPartitionRepCount 4 (2 * N + 1) ≡ 0 [MOD 2]

/-- `φ₄(4n + 1)` is odd exactly when `n = 5k(3k ± 1)/2` for some integer `k`; the two signs
are covered by `2n = 5k(3k + 1)` with `k ∈ ℤ` (replace `k` by `-k`).

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 4 (`integers-2025-A17-thm-4`). -/
public theorem_wanted frobeniusPartitionRepCount_four_four_mul_add_one_mod_two (n : ℕ) :
    frobeniusPartitionRepCount 4 (4 * n + 1) % 2 = 1 ↔
      ∃ k : ℤ, 2 * (n : ℤ) = 5 * k * (3 * k + 1)

/-- `φ₄(10n + 6) ≡ 0 (mod 5)` for all `n ≥ 0`.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 5 (`integers-2025-A17-thm-5`). -/
public theorem_wanted frobeniusPartitionRepCount_four_ten_mul_add_six_mod_five (n : ℕ) :
    frobeniusPartitionRepCount 4 (10 * n + 6) ≡ 0 [MOD 5]

/-- `φ₄(10n + 1) ≡ k + 1 (mod 5)` if `n = k(3k + 1)` for an integer `k`, and
`φ₄(10n + 1) ≡ 0 (mod 5)` otherwise.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 6 (`integers-2025-A17-thm-6`). -/
public theorem_wanted frobeniusPartitionRepCount_four_ten_mul_add_one_mod_five (n : ℕ) :
    (∀ k : ℤ, (n : ℤ) = k * (3 * k + 1) →
        (frobeniusPartitionRepCount 4 (10 * n + 1) : ℤ) ≡ k + 1 [ZMOD 5]) ∧
      ((¬ ∃ k : ℤ, (n : ℤ) = k * (3 * k + 1)) →
        frobeniusPartitionRepCount 4 (10 * n + 1) ≡ 0 [MOD 5])

/-- **Theorem 1**, the 2-dissection of `Φ₄(q) = ∑ φ₄(n) qⁿ`, with `f_k = (q^k; q^k)_∞`
(`qEulerProduct k`, written `𝔣 k`) and denominators cleared:
`∑ φ₄(2n) qⁿ = f₂¹⁰ f₅ / (f₁⁹ f₄² f₁₀) + 2q f₂¹⁵ f₂₀² / (f₁¹² f₄⁴ f₁₀²) - 8q f₄⁶ f₁₀ / (f₁⁷ f₅)`
(both sides multiplied by `f₁¹² f₄⁴ f₅ f₁₀²`) and
`∑ φ₄(2n+1) qⁿ = f₂⁷ f₁₀² / (f₁⁶ f₄² f₅²)` (both sides multiplied by `f₁⁶ f₄² f₅²`).

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 1, eqs. (3) and (4)
(`integers-2025-A17-thm-1`). -/
public theorem_wanted frobeniusPartitionRepCount_four_two_dissection :
    𝔣 1 ^ 12 * 𝔣 4 ^ 4 * 𝔣 5 * 𝔣 10 ^ 2 *
        PowerSeries.mk (fun n => (frobeniusPartitionRepCount 4 (2 * n) : ℤ)) =
      𝔣 1 ^ 3 * 𝔣 2 ^ 10 * 𝔣 4 ^ 2 * 𝔣 5 ^ 2 * 𝔣 10 + 2 * X * 𝔣 2 ^ 15 * 𝔣 5 * 𝔣 20 ^ 2
        - 8 * X * 𝔣 1 ^ 5 * 𝔣 4 ^ 10 * 𝔣 10 ^ 3 ∧
    𝔣 1 ^ 6 * 𝔣 4 ^ 2 * 𝔣 5 ^ 2 *
        PowerSeries.mk (fun n => (frobeniusPartitionRepCount 4 (2 * n + 1) : ℤ)) =
      𝔣 2 ^ 7 * 𝔣 10 ^ 2

/-- Ramanujan's theta-function identity: if `ab = cd` (with `|ab| < 1`, where `f(a, b)` is
defined, and `a ≠ 0` so that `c/a`, `d/a` make sense), then
`f(a,b) f(c,d) = f(ad,bc) f(ac,bd) + a f(c/a, a²bd) f(d/a, a²bc)`, with `f` Ramanujan's general
theta function `ramanujanThetaRaw` (all six theta arguments have product of modulus `< 1`).

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Lemma 1, eq. (12), quoting
Berndt, *Ramanujan's Notebooks, Part III*, p. 45, Entry 29 (`integers-2025-A17-lem-1`). -/
public theorem_wanted ramanujanTheta_mul_of_mul_eq {a b c d : ℂ} (ha : a ≠ 0)
    (hab : ‖a * b‖ < 1) (h : a * b = c * d) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d =
      ramanujanThetaRaw (a * d) (b * c) * ramanujanThetaRaw (a * c) (b * d) +
        a * ramanujanThetaRaw (c / a) (a ^ 2 * b * d) *
          ramanujanThetaRaw (d / a) (a ^ 2 * b * c)

/-- `1/(f₁³ f₅) = f₄⁴/(f₂⁷ f₁₀) - 2q f₄⁶ f₂₀²/(f₂⁹ f₁₀³) + 5q f₄³ f₂₀/f₂⁸
+ 2q² f₄⁹ f₄₀²/(f₂¹⁰ f₈² f₁₀² f₂₀)`, stated with denominators cleared (both sides multiplied by
`f₁³ f₅ f₂¹⁰ f₈² f₁₀³ f₂₀`).

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Lemma 4, eq. (15)
(`integers-2025-A17-lem-4`). -/
public theorem_wanted one_div_f1_cube_f5_two_dissection :
    𝔣 2 ^ 10 * 𝔣 8 ^ 2 * 𝔣 10 ^ 3 * 𝔣 20 =
      𝔣 1 ^ 3 * 𝔣 2 ^ 3 * 𝔣 4 ^ 4 * 𝔣 5 * 𝔣 8 ^ 2 * 𝔣 10 ^ 2 * 𝔣 20
        - 2 * X * 𝔣 1 ^ 3 * 𝔣 2 * 𝔣 4 ^ 6 * 𝔣 5 * 𝔣 8 ^ 2 * 𝔣 20 ^ 3
        + 5 * X * 𝔣 1 ^ 3 * 𝔣 2 ^ 2 * 𝔣 4 ^ 3 * 𝔣 5 * 𝔣 8 ^ 2 * 𝔣 10 ^ 3 * 𝔣 20 ^ 2
        + 2 * X ^ 2 * 𝔣 1 ^ 3 * 𝔣 4 ^ 9 * 𝔣 5 * 𝔣 10 * 𝔣 40 ^ 2

/-- `f₂³ f₅²/(f₁⁵ f₁₀²) = f₅/(f₂² f₁₀) + 5q f₁₀²/(f₁³ f₂)`, stated with denominators cleared (both
sides multiplied by `f₁⁵ f₂² f₁₀²`). The lemma's other identity (16) is the last conjunct of
`theta_level_five_identities`.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Lemma 5, eq. (17)
(`integers-2025-A17-lem-5`). -/
public theorem_wanted f2_cube_f5_sq_quotient_identity :
    𝔣 2 ^ 5 * 𝔣 5 ^ 2 = 𝔣 1 ^ 5 * 𝔣 5 * 𝔣 10 + 5 * X * 𝔣 1 ^ 2 * 𝔣 2 * 𝔣 10 ^ 4

end

end MetaMathlibExt
