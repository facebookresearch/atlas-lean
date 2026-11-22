/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace MetaMathlibExt

@[expose] public section

open Filter Topology

/-- The floor sequence parity count `𝓕_n`: the number of `k` with `1 ≤ k ≤ n`
for which `⌊n/k⌋` is odd (OEIS A059851). Natural-number division `n / k` is
`⌊n/k⌋`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 (definition of `𝓕_n`). -/
public def floorQuotientOddCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Odd (n / k))).card

/-- Characteristic value `𝓕_10 = 7` (the paper's introduction:
`10, 5, 3, 2, 2, 1, 1, 1, 1, 1` has seven odd terms).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 and Figure 1. -/
public theorem floorQuotientOddCount_ten : floorQuotientOddCount 10 = 7 := by
  decide

/-- The ceiling sequence parity count `𝓒_n`: the number of `k` with
`1 ≤ k ≤ n` for which `⌈n/k⌉` is odd (OEIS A330926).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 (definition of `𝓒_n`). -/
public def ceilQuotientOddCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k : ℕ => Odd ⌈(n : ℚ) / (k : ℚ)⌉)).card

/-- Characteristic value `𝓒_9 = 5` (Figure 1 of the paper).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Figure 1. -/
public theorem ceilQuotientOddCount_nine : ceilQuotientOddCount 9 = 5 := by
  decide +kernel

/-- The rounding sequence parity count `𝓡_n`: the number of `k` with
`1 ≤ k ≤ n` for which the nearest integer to `n/k` is odd, half-integers
rounded up. Mathlib's `round` rounds half-integers up (`round_eq`:
`round x = ⌊x + 1/2⌋`), which is the paper's convention for `nint`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 (definition of `𝓡_n` and the footnote on `nint`). -/
public def roundQuotientOddCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k : ℕ => Odd (round ((n : ℚ) / (k : ℚ))))).card

/-- Characteristic value `𝓡_10 = 7` (Figure 1 of the paper).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Figure 1. -/
public theorem roundQuotientOddCount_ten : roundQuotientOddCount 10 = 7 := by
  decide +kernel

/-- The count `𝓝_{n,α,ν,r,m}` of terms of the `α`-shifted, `ν`-offset floor
sequence `⌊(n-ν)/1 + α⌋, …, ⌊(n-ν)/n + α⌋` that are congruent to `r`
modulo `m`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 4 (definition of `𝓝_{n,α,ν,r,m}`). -/
public noncomputable def shiftedFloorResidueCount (n : ℕ) (α ν : ℝ) (r : ℤ)
    (m : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter
    (fun k : ℕ => ⌊((n : ℝ) - ν) / (k : ℝ) + α⌋ ≡ r [ZMOD m])).card

/-- Characteristic value: modulo `1` every term is counted, so
`𝓝_{n,α,ν,r,1} = n` (the paper's remark after equation (4.2)).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 4. -/
public theorem shiftedFloorResidueCount_modulus_one (n : ℕ) (α ν : ℝ)
    (r : ℤ) : shiftedFloorResidueCount n α ν r 1 = n := by
  unfold shiftedFloorResidueCount
  rw [Finset.filter_true_of_mem (fun k _ => by simp [Int.ModEq])]
  simp

/-- Lemma 1: for `k ≥ 1`, exactly `⌊n/k⌋` terms of the floor sequence
`⌊n/1⌋, …, ⌊n/n⌋` are at least `k`. Stated for every `n : ℕ` (the case
`n = 0` is the empty sequence).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 1 (`jis-2024-24.2.5-lem-1`). -/
public theorem_wanted floor_div_sequence_card_ge (n k : ℕ) (hk : 1 ≤ k) :
    ((Finset.Icc 1 n).filter (fun d : ℕ => k ≤ n / d)).card = n / k

/-- Proposition 2: `𝓕_n = ∑_{d=1}^n ⌊n/d⌋ (-1)^{d+1}`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 2 (`jis-2024-24.2.5-prop-2`). -/
public theorem_wanted floorQuotientOddCount_eq_alternating_sum (n : ℕ) :
    (floorQuotientOddCount n : ℤ) =
      ∑ d ∈ Finset.Icc 1 n, ((n / d : ℕ) : ℤ) * (-1) ^ (d + 1)

/-- Corollary 3: `𝓕_n = D(n) - 2 D(n/2)`, where `D(x) = ∑_{m ≤ x} τ(m)` is
the divisor summatory function; for integer `m`, `m ≤ n/2` means
`m ≤ ⌊n/2⌋ = n / 2`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 3 (`jis-2024-24.2.5-cor-3`). -/
public theorem_wanted floorQuotientOddCount_eq_divisor_summatory_sub (n : ℕ) :
    (floorQuotientOddCount n : ℤ) =
      ∑ m ∈ Finset.Icc 1 n, (m.divisors.card : ℤ) -
        2 * ∑ m ∈ Finset.Icc 1 (n / 2), (m.divisors.card : ℤ)

/-- Proposition 4: `𝓕_n` is the number of lattice points `(x, y)` with
`x, y ≥ 1` and `n/2 < xy ≤ n` (the region `H_{1,n}` without its boundary
curve `xy = n/2`) minus the number of lattice points with `x, y ≥ 1` and
`xy ≤ n/2` (the closed region `H_{2,n}`).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 4 (`jis-2024-24.2.5-prop-4`). -/
public theorem_wanted floorQuotientOddCount_eq_hyperbolic_lattice_difference
    (n : ℕ) :
    (floorQuotientOddCount n : ℤ) =
      (Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧
          (n : ℤ) < 2 * (p.1 * p.2) ∧ p.1 * p.2 ≤ n} : ℤ) -
        Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 2 * (p.1 * p.2) ≤ n}

/-- Theorem 6 (Dirichlet): for `x ≥ 1`,
`D(x) = x log x + (2γ - 1) x + O(√x)`, with `D(x) = ∑_{m ≤ x} τ(m)`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Theorem 6 (`jis-2024-24.2.5-thm-6`). -/
public theorem_wanted divisor_summatory_asymptotic :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (m.divisors.card : ℝ)) -
          (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)| ≤
        C * Real.sqrt x

/-- Proposition 7: `𝓕_n = n log 2 + O(√n)` and `𝓕_n / n → log 2`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 7 (`jis-2024-24.2.5-prop-7`). -/
public theorem_wanted floorQuotientOddCount_asymptotic :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(floorQuotientOddCount n : ℝ) - n * Real.log 2| ≤ C * Real.sqrt n) ∧
    Tendsto (fun n : ℕ => (floorQuotientOddCount n : ℝ) / n) atTop
      (𝓝 (Real.log 2))

/-- Proposition 9, first equality: `𝓒_n = n - 𝓕_{n-1}`, written for `n + 1`.
The printed second equality `= ∑_{d=2}^n ⌊n/d⌋ (-1)^d` is omitted (false:
at `n = 3`, `𝓒_3 = 2` while the sum is `1 - 1 = 0`).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 9 (`jis-2024-24.2.5-prop-9`). -/
public theorem_wanted ceilQuotientOddCount_succ_eq (n : ℕ) :
    (ceilQuotientOddCount (n + 1) : ℤ) = (n + 1 : ℤ) - floorQuotientOddCount n

/-- Corollary 10: `𝓒_n = (1 - log 2) n + O(√n)` and `𝓒_n / n → 1 - log 2`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 10 (`jis-2024-24.2.5-cor-10`). -/
public theorem_wanted ceilQuotientOddCount_asymptotic :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(ceilQuotientOddCount n : ℝ) - (1 - Real.log 2) * n| ≤
        C * Real.sqrt n) ∧
    Tendsto (fun n : ℕ => (ceilQuotientOddCount n : ℝ) / n) atTop
      (𝓝 (1 - Real.log 2))

/-- Lemma 12: `n` has at most `2√n` positive divisors.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 12 (`jis-2024-24.2.5-lem-12`). -/
public theorem_wanted card_divisors_le_two_mul_sqrt (n : ℕ) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt n

/-- Lemma 13: in the rounding sequence `⌊n/1 + 1/2⌋, …, ⌊n/n + 1/2⌋`, all
`n` terms are at least `1`, and for `k ≥ 2` exactly `⌊2n/(2k-1)⌋` terms are
at least `k`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 13 (`jis-2024-24.2.5-lem-13`). -/
public theorem_wanted round_div_sequence_card_ge (n : ℕ) :
    ((Finset.Icc 1 n).filter (fun d : ℕ => (1 : ℤ) ≤ ⌊(n : ℚ) / (d : ℚ) + 1 / 2⌋)).card
        = n ∧
      ∀ k : ℕ, 2 ≤ k →
        ((Finset.Icc 1 n).filter
            (fun d : ℕ => (k : ℤ) ≤ ⌊(n : ℚ) / (d : ℚ) + 1 / 2⌋)).card =
          2 * n / (2 * k - 1)

/-- Proposition 14: `𝓡_n = -n + ∑_{d=1}^n ⌊2n/(2d-1)⌋ (-1)^{d+1}`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 14 (`jis-2024-24.2.5-prop-14`). -/
public theorem_wanted roundQuotientOddCount_eq_alternating_sum (n : ℕ) :
    (roundQuotientOddCount n : ℤ) =
      -n + ∑ d ∈ Finset.Icc 1 n, ((2 * n / (2 * d - 1) : ℕ) : ℤ) * (-1) ^ (d + 1)

/-- Lemma 15: `𝓡_n = -n + ∑_{k=1}^{2n} (d_{1,4}(k) - d_{3,4}(k))`, where
`d_{r,4}(k)` counts the positive divisors of `k` congruent to `r` mod `4`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 15 (`jis-2024-24.2.5-lem-15`). -/
public theorem_wanted roundQuotientOddCount_eq_sum_divisor_difference (n : ℕ) :
    (roundQuotientOddCount n : ℤ) =
      -n + ∑ k ∈ Finset.Icc 1 (2 * n),
        (((k.divisors.filter (fun d : ℕ => d % 4 = 1)).card : ℤ) -
          (k.divisors.filter (fun d : ℕ => d % 4 = 3)).card)

/-- Theorem 16 (Jacobi's two-square theorem): for `n ≥ 1`, the number
`r_2(n)` of pairs `(a, b) ∈ ℤ²` with `a² + b² = n` is
`4 (d_{1,4}(n) - d_{3,4}(n))`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Theorem 16 (`jis-2024-24.2.5-thm-16`). -/
public theorem_wanted card_sq_add_sq_eq (n : ℕ) (hn : 0 < n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n} : ℤ) =
      4 * (((n.divisors.filter (fun d : ℕ => d % 4 = 1)).card : ℤ) -
        (n.divisors.filter (fun d : ℕ => d % 4 = 3)).card)

/-- Proposition 17: the closed disc of radius `√(2n)` about the origin
contains `4 𝓡_n + 4n + 1` lattice points, i.e. `C(2n) = 4 𝓡_n + 4n + 1`.
Stated for every `n : ℕ` (both sides are `1` at `n = 0`).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 17 (`jis-2024-24.2.5-prop-17`). -/
public theorem_wanted card_lattice_disc_two_mul (n : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * n} =
      4 * roundQuotientOddCount n + 4 * n + 1

/-- Corollary 19: `𝓡` decreases by at most `1` in any step.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 19 (`jis-2024-24.2.5-cor-19`). -/
public theorem_wanted roundQuotientOddCount_sub_one_le_succ (n : ℕ) :
    (roundQuotientOddCount n : ℤ) - 1 ≤ roundQuotientOddCount (n + 1)

/-- Theorem 20 (Gauss circle problem): for `x ≥ 1`, the closed disc of
radius `√x` about the origin contains `π x + O(√x)` lattice points.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Theorem 20 (`jis-2024-24.2.5-thm-20`). -/
public theorem_wanted gauss_circle_asymptotic :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(Nat.card {p : ℤ × ℤ // ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ x} : ℝ) -
          Real.pi * x| ≤ C * Real.sqrt x

/-- Proposition 21: `𝓡_n = (π/2 - 1) n + O(√n)` and `𝓡_n / n → π/2 - 1`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 21 (`jis-2024-24.2.5-prop-21`). -/
public theorem_wanted roundQuotientOddCount_asymptotic :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(roundQuotientOddCount n : ℝ) - (Real.pi / 2 - 1) * n| ≤
        C * Real.sqrt n) ∧
    Tendsto (fun n : ℕ => (roundQuotientOddCount n : ℝ) / n) atTop
      (𝓝 (Real.pi / 2 - 1))

/-- Lemma 24: for `α, ν ∈ [0, 1)` and `nα ≥ ν`, all `n` terms of the
`α`-shifted, `ν`-offset floor sequence of length `n` are at least `1`, and
for `k ≥ 2` exactly `⌊(n-ν)/(k-α)⌋` of them are at least `k`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 24 (`jis-2024-24.2.5-lem-24`). -/
public theorem_wanted shifted_floor_sequence_card_ge (n : ℕ) (α ν : ℝ)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν₀ : 0 ≤ ν) (hν₁ : ν < 1)
    (hnαν : ν ≤ n * α) :
    ((Finset.Icc 1 n).filter
        (fun d : ℕ => (1 : ℤ) ≤ ⌊((n : ℝ) - ν) / (d : ℝ) + α⌋)).card = n ∧
      ∀ k : ℕ, 2 ≤ k →
        (((Finset.Icc 1 n).filter
            (fun d : ℕ => (k : ℤ) ≤ ⌊((n : ℝ) - ν) / (d : ℝ) + α⌋)).card : ℤ) =
          ⌊((n : ℝ) - ν) / (k - α)⌋

/-- Proposition 25: for `m ≥ 2`, `α, ν ∈ [0, 1)` and `nα ≥ ν`,
`𝓝_{n,α,ν,1,m} = n - ⌊(n-ν)/(1-α)⌋ + ∑_{i ≥ 0} (⌊(n-ν)/(1+im-α)⌋ -
⌊(n-ν)/(2+im-α)⌋)` and, for `2 ≤ r ≤ m`,
`𝓝_{n,α,ν,r,m} = ∑_{i ≥ 0} (⌊(n-ν)/(r+im-α)⌋ - ⌊(n-ν)/(r+1+im-α)⌋)`.
The series over `i ≥ 0` is written as the sum over `i ≤ n`; every omitted
term vanishes since `r + im - α > n - ν` for `i > n`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 25 (`jis-2024-24.2.5-prop-25`). -/
public theorem_wanted shiftedFloorResidueCount_eq_sum_floor_sub (n m : ℕ)
    (hm : 2 ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν₀ : 0 ≤ ν)
    (hν₁ : ν < 1) (hnαν : ν ≤ n * α) :
    ((shiftedFloorResidueCount n α ν 1 m : ℤ) =
      n - ⌊((n : ℝ) - ν) / (1 - α)⌋ +
        ∑ i ∈ Finset.range (n + 1),
          (⌊((n : ℝ) - ν) / (1 + i * m - α)⌋ -
            ⌊((n : ℝ) - ν) / (2 + i * m - α)⌋)) ∧
    ∀ r : ℕ, 2 ≤ r → r ≤ m →
      (shiftedFloorResidueCount n α ν r m : ℤ) =
        ∑ i ∈ Finset.range (n + 1),
          (⌊((n : ℝ) - ν) / (r + i * m - α)⌋ -
            ⌊((n : ℝ) - ν) / (r + 1 + i * m - α)⌋)

/-- Proposition 32: for a strictly increasing sequence `b_0, b_1, …` of
reals with `b_k ≥ 1` and `b_k ≥ k`, and `ν ∈ [0, 1)`,
`∑_{k ≤ n-ν} ⌊(n-ν)/b_k⌋ (-1)^k = n ∑_{k ≤ n-ν} (-1)^k / b_k + O(√n)`;
the implied constant may depend on `b` and `ν`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 32 (`jis-2024-24.2.5-prop-32`). -/
public theorem_wanted alternating_sum_floor_div_eq_add_bigO (ν : ℝ)
    (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) (b : ℕ → ℝ) (hb : StrictMono b)
    (hb₁ : ∀ k, 1 ≤ b k) (hbk : ∀ k : ℕ, (k : ℝ) ≤ b k) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - ν),
            (⌊((n : ℝ) - ν) / b k⌋ : ℝ) * (-1) ^ k) -
          n * ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - ν),
            (-1) ^ k / b k| ≤ C * Real.sqrt n

/-- Corollary 34: for `2 ≤ r ≤ m` and `α, ν ∈ [0, 1)`, uniformly over `n`
with `nα ≥ ν`,
`𝓝_{n,α,ν,r,m} = n ∑_{i ≥ 0} (1/(r+im-α) - 1/(r+1+im-α)) + O(√n)`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 34 (`jis-2024-24.2.5-cor-34`). -/
public theorem_wanted shiftedFloorResidueCount_asymptotic_series (r m : ℕ)
    (hr : 2 ≤ r) (hrm : r ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ν ≤ n * α →
      |(shiftedFloorResidueCount n α ν r m : ℝ) -
          n * ∑' i : ℕ, (1 / ((r : ℝ) + i * m - α) - 1 / ((r : ℝ) + 1 + i * m - α))|
        ≤ C * Real.sqrt n

/-- Corollary 35: for `m ≥ 2` and `α, ν ∈ [0, 1)`, uniformly over `n` with
`nα ≥ ν`, `𝓝_{n,α,ν,1,m} = -αn/(1-α) +
n ∑_{i ≥ 0} (1/(1+im-α) - 1/(2+im-α)) + O(√n)`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 35 (`jis-2024-24.2.5-cor-35`). -/
public theorem_wanted shiftedFloorResidueCount_one_asymptotic_series (m : ℕ)
    (hm : 2 ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν₀ : 0 ≤ ν)
    (hν₁ : ν < 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ν ≤ n * α →
      |(shiftedFloorResidueCount n α ν 1 m : ℝ) -
          (-α * n / (1 - α) +
            n * ∑' i : ℕ, (1 / (1 + (i : ℝ) * m - α) - 1 / (2 + (i : ℝ) * m - α)))|
        ≤ C * Real.sqrt n

/-- Proposition 36: for integers `2 ≤ r ≤ m` and `α ∈ [0, 1)`,
`∑_{i ≥ 0} (1/(r+im-α) - 1/(r+1+im-α)) = ∫_0^1 (1-x) x^{r-1-α} / (1-x^m) dx`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 36 (`jis-2024-24.2.5-prop-36`). -/
public theorem_wanted tsum_alternating_inv_eq_integral (r m : ℕ) (hr : 2 ≤ r)
    (hrm : r ≤ m) (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    ∑' i : ℕ, (1 / ((r : ℝ) + i * m - α) - 1 / ((r : ℝ) + 1 + i * m - α)) =
      ∫ x in (0 : ℝ)..1, (1 - x) * x ^ ((r : ℝ) - 1 - α) / (1 - x ^ m)

/-- Theorem 37: for `m ≥ 1` and `α, ν ∈ [0, 1)`, uniformly over `n` with
`nα ≥ ν`, `𝓝_{n,α,ν,1,m} = -αn/(1-α) + n ∫_0^1 (1-x) x^{-α}/(1-x^m) dx +
O(√n)` and, for `2 ≤ r ≤ m`,
`𝓝_{n,α,ν,r,m} = n ∫_0^1 (1-x) x^{r-1-α}/(1-x^m) dx + O(√n)`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Theorem 37 (`jis-2024-24.2.5-thm-37`). -/
public theorem_wanted shiftedFloorResidueCount_asymptotic_integral (m : ℕ)
    (hm : 1 ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν₀ : 0 ≤ ν)
    (hν₁ : ν < 1) :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ν ≤ n * α →
      |(shiftedFloorResidueCount n α ν 1 m : ℝ) -
          (-α * n / (1 - α) +
            n * ∫ x in (0 : ℝ)..1, (1 - x) * x ^ (-α) / (1 - x ^ m))|
        ≤ C * Real.sqrt n) ∧
    ∀ r : ℕ, 2 ≤ r → r ≤ m →
      ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ν ≤ n * α →
        |(shiftedFloorResidueCount n α ν r m : ℝ) -
            n * ∫ x in (0 : ℝ)..1, (1 - x) * x ^ ((r : ℝ) - 1 - α) / (1 - x ^ m)|
          ≤ C * Real.sqrt n

/-- Corollary 38: for `α, ν ∈ [0, 1)` and `1 ≤ r ≤ m`, `𝓝_{n,α,ν,r,m} / n`
tends to `-α/(1-α) + ∫_0^1 (1-x) x^{-α}/(1-x^m) dx` if `r = 1` and to
`∫_0^1 (1-x) x^{r-1-α}/(1-x^m) dx` if `2 ≤ r ≤ m`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 38 (`jis-2024-24.2.5-cor-38`). -/
public theorem_wanted shiftedFloorResidueCount_div_tendsto (r m : ℕ)
    (hr : 1 ≤ r) (hrm : r ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) :
    Tendsto (fun n : ℕ => (shiftedFloorResidueCount n α ν r m : ℝ) / n) atTop
      (𝓝 (if r = 1 then
          -α / (1 - α) + ∫ x in (0 : ℝ)..1, (1 - x) * x ^ (-α) / (1 - x ^ m)
        else ∫ x in (0 : ℝ)..1, (1 - x) * x ^ ((r : ℝ) - 1 - α) / (1 - x ^ m)))

/-- Proposition 39: the closed disc of radius `√n` about the origin contains
`4 𝓝_{⌈n/2⌉,1/2,{n/2},1,2} + 4 ⌊n/2⌋ + 1` lattice points, where `{n/2}` is
the fractional part of `n/2`. Stated for every `n : ℕ` (both sides are `1`
at `n = 0`).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 39 (`jis-2024-24.2.5-prop-39`). -/
public theorem_wanted card_lattice_disc_eq_shiftedFloorResidueCount (n : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ n} =
      4 * shiftedFloorResidueCount ⌈(n : ℝ) / 2⌉₊ (1 / 2)
          (Int.fract ((n : ℝ) / 2)) 1 2 + 4 * (n / 2) + 1

/-- Proposition 42 (Dickson, Exercise XXII.2): for `n ≥ 1`, the number of
pairs `(x, y) ∈ ℤ²` with `x² + xy + y² = n` is `6 (d_{1,3}(n) - d_{2,3}(n))`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 42 (`jis-2024-24.2.5-prop-42`). -/
public theorem_wanted card_eisenstein_form_eq (n : ℕ) (hn : 0 < n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = n} : ℤ) =
      6 * (((n.divisors.filter (fun d : ℕ => d % 3 = 1)).card : ℤ) -
        (n.divisors.filter (fun d : ℕ => d % 3 = 2)).card)

/-- Corollary 43: the elliptical region `x² + xy + y² ≤ n` contains
`6 𝓝_{n,0,0,1,3} + 1` lattice points. Stated for every `n : ℕ` (both sides
are `1` at `n = 0`).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 43 (`jis-2024-24.2.5-cor-43`). -/
public theorem_wanted card_eisenstein_ellipse_eq (n : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 ≤ n} =
      6 * shiftedFloorResidueCount n 0 0 1 3 + 1

/-- Corollary 45: the elliptical region `x² + xy + y² ≤ n` contains
`(2/3)√3 π n + O(√n)` lattice points.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 45 (`jis-2024-24.2.5-cor-45`). -/
public theorem_wanted card_eisenstein_ellipse_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 ≤ n} : ℝ) -
          2 / 3 * Real.sqrt 3 * Real.pi * n| ≤ C * Real.sqrt n

/-- Corollary 47: in the hexagonal (triangular) lattice `ℤ + ℤω`,
`ω = e^{2πi/3}`, whose neighboring points are one unit apart, the closed
disc of radius `√n` centered at a lattice point contains
`1 + 6 𝓝_{n,0,0,1,3}` lattice points, and `𝓝_{n,0,0,1,3}` is the number of
terms of `⌊n/1⌋, …, ⌊n/n⌋` that are `1` modulo `3`. Every hexagonal lattice
with unit spacing is congruent to this one, and the disc is centered at the
lattice point `0`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 47 (`jis-2024-24.2.5-cor-47`). -/
public theorem_wanted card_hexagonal_lattice_disc_eq (n : ℕ) :
    Nat.card {p : ℤ × ℤ //
        ‖(p.1 : ℂ) + p.2 * Complex.exp (2 * Real.pi / 3 * Complex.I)‖ ≤
          Real.sqrt n} =
      1 + 6 * shiftedFloorResidueCount n 0 0 1 3 ∧
    shiftedFloorResidueCount n 0 0 1 3 =
      ((Finset.Icc 1 n).filter (fun k => n / k % 3 = 1)).card

/-- Proposition 48 (Dickson, Exercise XXII.1): for `n ≥ 1`, the number of
pairs `(x, y) ∈ ℤ²` with `x² + 2y² = n` is
`2 (d_{1,8}(n) + d_{3,8}(n) - d_{5,8}(n) - d_{7,8}(n))`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 48 (`jis-2024-24.2.5-prop-48`). -/
public theorem_wanted card_sq_add_two_mul_sq_eq (n : ℕ) (hn : 0 < n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = n} : ℤ) =
      2 * (((n.divisors.filter (fun d : ℕ => d % 8 = 1)).card : ℤ) +
        (n.divisors.filter (fun d : ℕ => d % 8 = 3)).card -
        (n.divisors.filter (fun d : ℕ => d % 8 = 5)).card -
        (n.divisors.filter (fun d : ℕ => d % 8 = 7)).card)

/-- Corollary 49: the number `F(n)` of lattice points in `x² + 2y² ≤ n`
satisfies `F(0) = 1`, `F(1) = 3`, `F(2) = 5`, `F(5) = 11`, and for
`n ∉ {1, 2, 5}`, `F(n) = 1 + 2 𝓝_{⌈n/4⌉,3/4,{-n/4},1,2} +
2 𝓝_{⌈n/4⌉,1/4,{-n/4},1,2} + 2n + 2 ⌊n/3⌋ - 4 ⌈n/4⌉`. The general formula
is stated for every `n : ℕ` outside `{1, 2, 5}`, including `n = 0` where
both sides are `1`.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 49 (`jis-2024-24.2.5-cor-49`). -/
public theorem_wanted card_sq_add_two_mul_sq_ellipse_eq :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 0} = 1 ∧
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 1} = 3 ∧
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 2} = 5 ∧
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 5} = 11 ∧
    ∀ n : ℕ, n ≠ 1 → n ≠ 2 → n ≠ 5 →
      (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ n} : ℤ) =
        1 + 2 * shiftedFloorResidueCount ⌈(n : ℝ) / 4⌉₊ (3 / 4)
            (Int.fract (-(n : ℝ) / 4)) 1 2 +
          2 * shiftedFloorResidueCount ⌈(n : ℝ) / 4⌉₊ (1 / 4)
            (Int.fract (-(n : ℝ) / 4)) 1 2 +
          2 * n + 2 * (n / 3 : ℕ) - 4 * ⌈(n : ℝ) / 4⌉₊

end

end MetaMathlibExt
