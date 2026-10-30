/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Arndt compositions: a generating functions approach

Statements from Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35 (arXiv:2311.15388).

An Arndt composition is a composition `(σ₁, …, σ_ℓ)` with `σ_{2i-1} > σ_{2i}` for every `i`
with `2i ≤ ℓ`; `a(n, m) = arndtCompositionCount (fun _ => True) n m` counts those of `n` with `m`
parts (`WantedExt/Combinatorics/Enumerative/ArndtCompositionsWanted.lean`). Bivariate generating
functions live in `ℤ[y][[x]]`, `x` marking the weight and `y` the second statistic, and rational
generating functions are stated multiplicatively (generating function times denominator equals
numerator).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.RingTheory.Binomial
public import WantedExt.Combinatorics.Enumerative.ArndtCompositionsWanted

namespace MetaMathlibExt

@[expose] public section

/-- The bivariate generating function `∑_{n, m} a(n, m) xⁿ yᵐ` of a two-index count `a` with
`a(n, m) = 0` for `m > n`, by weight (`x`) and second index (`y`), in `ℤ[y][[x]]`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2 (the series `A(x, y)`, `Ap(x, y)`,
`Bp(x, y)`, `B(x, y)`, `A_k(x, y)` and `A^{(k)}(x, y)`). -/
noncomputable def bivariateCountGF (a : ℕ → ℕ → ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.range (n + 1), (a n m : Polynomial ℤ) * Polynomial.X ^ m

/-- The `xⁿ` coefficient of `bivariateCountGF a` is `∑_{m ≤ n} a(n, m) yᵐ`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2. -/
theorem coeff_bivariateCountGF (a : ℕ → ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (bivariateCountGF a) =
      ∑ m ∈ Finset.range (n + 1), (a n m : Polynomial ℤ) * Polynomial.X ^ m := by
  simp [bivariateCountGF]

/-- The Arndt generating function `arndtGF S` is `bivariateCountGF` of the Arndt counts.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2 (definition of `A(x, y)`). -/
theorem arndtGF_eq_bivariateCountGF (S : ℕ → Prop) [DecidablePred S] :
    arndtGF S = bivariateCountGF (arndtCompositionCount S) :=
  rfl

/-- The number of anti-palindromic compositions of `n` with `m` parts: `m`-tuples `c` of positive
integers with `∑ c = n` and `c i ≠ c j` whenever `i + j + 1 = m` and `i ≠ j` (0-based form of
`σ_i ≠ σ_{ℓ+1-i}` for `i ≠ (ℓ+1)/2`).

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (definition of anti-palindromic
compositions, after Andrews, Just, and Simay). -/
def antiPalindromicCompositionCount (n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧ ∀ i j : Fin m, (i : ℕ) + j + 1 = m → i ≠ j → c i ≠ c j).card

/-- The number of reduced anti-palindromic compositions of `n` with `m` parts, that is, of
flip-equivalence classes of anti-palindromic compositions (switching any of the pairs `σ_i`,
`σ_{ℓ+1-i}`). Each class has exactly one representative with `σ_i > σ_{ℓ+1-i}` for every
`i < (ℓ+1)/2`, the representative the paper fixes; this counts those representatives, as
`m`-tuples `c` of positive integers with `∑ c = n` and `c j < c i` whenever `i + j + 1 = m` and
`i < j`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (reduced anti-palindromic compositions and
the choice of representative after Theorem 7). -/
def reducedAntiPalindromicCompositionCount (n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧ ∀ i j : Fin m, (i : ℕ) + j + 1 = m → i < j → c j < c i).card

/-- There are eight anti-palindromic compositions of `6` with three parts.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (each class has `2^{⌊ℓ/2⌋}` members). -/
theorem antiPalindromicCompositionCount_six_three : antiPalindromicCompositionCount 6 3 = 8 := by
  decide

/-- There are four reduced anti-palindromic compositions of `6` with three parts.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (each class has `2^{⌊ℓ/2⌋}` members). -/
theorem reducedAntiPalindromicCompositionCount_six_three :
    reducedAntiPalindromicCompositionCount 6 3 = 4 := by
  decide

/-- There are four anti-palindromic compositions of `6` with four parts and one flip class.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 2.1 (each class has `2^{⌊ℓ/2⌋}` members). -/
theorem antiPalindromicCompositionCount_six_four :
    antiPalindromicCompositionCount 6 4 = 4 ∧ reducedAntiPalindromicCompositionCount 6 4 = 1 := by
  decide

/-- The number `b(n, j)` of Arndt compositions of `n` (any number of parts) whose last part is
`j`; the empty composition of `0` has last part `0`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 3 (definition of `b(n, m)` and Table 2). -/
def arndtLastPartCount (n j : ℕ) : ℕ :=
  if n = 0 then (if j = 0 then 1 else 0) else
    ∑ m ∈ Finset.range n,
      ((Finset.Nat.antidiagonalTuple (m + 1) n).filter fun c =>
        (∀ i, 0 < c i) ∧
          (∀ i i' : Fin (m + 1), (i : ℕ) % 2 = 0 → (i' : ℕ) = i + 1 → c i' < c i) ∧
            c (Fin.last m) = j).card

/-- Row `n = 6` of Table 2: `b(6, 1) = 4`, `b(6, 2) = 2`, `b(6, 3) = 1`, `b(6, 6) = 1`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 3, Table 2. -/
theorem arndtLastPartCount_six :
    arndtLastPartCount 6 1 = 4 ∧ arndtLastPartCount 6 2 = 2 ∧ arndtLastPartCount 6 3 = 1 ∧
      arndtLastPartCount 6 6 = 1 := by
  decide +kernel

/-- The number `a_k(n, m)` of `k`-Arndt compositions of `n` with `m` parts: `m`-tuples `c` of
positive integers with `∑ c = n` and `c (2i) > c (2i + 1) + k` for each pair of consecutive
positions `2i, 2i + 1 < m` (0-based). The shift `k` is an integer; `k = 0` gives Arndt
compositions.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 4 (definition of `k`-Arndt compositions,
after Hopkins and Tangboonduangjit; Theorem 11 treats `k ≥ 0` and `k < 0`). -/
def kArndtCompositionCount (k : ℤ) (n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧
      ∀ i j : Fin m, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → (c j : ℤ) + k < c i).card

/-- Coefficients of the expansions of `A_3(x, y)` and `A_{-3}(x, y)`: `a_3(7, 2) = a_3(7, 3) = 1`
and `a_{-3}(4, 2) = 3`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 4 (series expansions after Theorem 11). -/
theorem kArndtCompositionCount_examples :
    kArndtCompositionCount 3 7 2 = 1 ∧ kArndtCompositionCount 3 7 3 = 1 ∧
      kArndtCompositionCount (-3) 4 2 = 3 := by
  decide

/-- The number `a^{(k)}(n, m)` of `k`-block Arndt compositions of `n` with `m` parts: `m`-tuples
`c` of positive integers with `∑ c = n` that strictly decrease inside each block of `k`
consecutive positions, `c (ki) > c (ki + 1) > ⋯ > c (ki + k - 1)` (0-based); meaningful for
`k ≥ 1`, and `k = 2` gives Arndt compositions.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 5 (definition of `k`-block Arndt
compositions). -/
def blockArndtCompositionCount (k n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧
      ∀ i j : Fin m, (i : ℕ) % k ≠ k - 1 → (j : ℕ) = i + 1 → c j < c i).card

/-- Seven of the eighteen `3`-block Arndt compositions of `10` listed in the paper have four
parts: `(6,2,1,1)`, `(5,3,1,1)`, `(5,2,1,2)`, `(4,3,2,1)`, `(4,3,1,2)`, `(4,2,1,3)`, `(3,2,1,4)`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 5 (list of the compositions counted by
`a^{(3)}(10) = 18`). -/
theorem blockArndtCompositionCount_three_ten_four : blockArndtCompositionCount 3 10 4 = 7 := by
  decide

/-- Closed sum and recurrence for `a(n, m)`: for all `n, m ≥ 0`,
`a(n, m) = ∑_{ℓ=0}^{n-m-⌊m/2⌋} C(m+ℓ-1, ℓ) C(n-m-ℓ-1, n-m-⌊m/2⌋-ℓ) (-1)^{n-m-⌊m/2⌋-ℓ}` (the sum
is empty, so `a(n, m) = 0`, when `n < m + ⌊m/2⌋`), and for `n ≥ 3`, `m ≥ 2`,
`a(n, m) = a(n-1, m) + a(n-2, m) - a(n-3, m) + a(n-3, m-2)`. Binomial coefficients with upper
index `-1` are the generalized ones (`Ring.choose` over `ℤ`, so `C(-1, 0) = 1`).

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 2 (`integers-2024-A35-thm-2`). -/
public theorem_wanted arndtCompositionCount_eq_alternating_sum_and_recurrence :
    (∀ n m : ℕ, (arndtCompositionCount (fun _ => True) n m : ℤ) =
      if m + m / 2 ≤ n then
        ∑ ℓ ∈ Finset.range (n - m - m / 2 + 1),
          Ring.choose ((m : ℤ) + ℓ - 1) ℓ * Ring.choose ((n : ℤ) - m - ℓ - 1) (n - m - m / 2 - ℓ) *
            (-1) ^ (n - m - m / 2 - ℓ)
      else 0) ∧
    ∀ n m : ℕ, 3 ≤ n → 2 ≤ m →
      (arndtCompositionCount (fun _ => True) n m : ℤ) =
        arndtCompositionCount (fun _ => True) (n - 1) m +
          arndtCompositionCount (fun _ => True) (n - 2) m -
            arndtCompositionCount (fun _ => True) (n - 3) m +
              arndtCompositionCount (fun _ => True) (n - 3) (m - 2)

/-- Positive sum for `a(n, m)`: for `m ≥ 1`,
`a(n, m) = ∑_{ℓ=0}^{⌊(n-m-⌊m/2⌋)/2⌋} C(⌊m/2⌋+ℓ-1, ℓ) C(n-2⌊m/2⌋-2ℓ-1, ⌊(m-1)/2⌋)`, the sum
being empty when `n < m + ⌊m/2⌋`. The paper states it for all `n, m ≥ 0`; at `n = m = 0` it
fails (`a(0, 0) = 1`, while the only term has lower index `⌊-1/2⌋ = -1` and vanishes), and the
case `m = 0` is omitted here.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 3 (`integers-2024-A35-thm-3`). -/
public theorem_wanted arndtCompositionCount_eq_positive_sum (n m : ℕ) (hm : 0 < m) :
    (arndtCompositionCount (fun _ => True) n m : ℤ) =
      if m + m / 2 ≤ n then
        ∑ ℓ ∈ Finset.range ((n - m - m / 2) / 2 + 1),
          Ring.choose (((m / 2 : ℕ) : ℤ) + ℓ - 1) ℓ *
            Ring.choose ((n : ℤ) - 2 * (m / 2 : ℕ) - 2 * ℓ - 1) ((m - 1) / 2)
      else 0

/-- Holonomic recurrence: for all `n, m ≥ 0`,
`(m - n - 2 + ⌊m/2⌋) a(n+2, m) + (m - ⌊m/2⌋) a(n+1, m) + n a(n, m) = 0`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 4 (`integers-2024-A35-thm-4`). -/
public theorem_wanted arndtCompositionCount_holonomic_recurrence (n m : ℕ) :
    ((m : ℤ) - n - 2 + (m / 2 : ℕ)) * arndtCompositionCount (fun _ => True) (n + 2) m +
        ((m : ℤ) - (m / 2 : ℕ)) * arndtCompositionCount (fun _ => True) (n + 1) m +
          (n : ℤ) * arndtCompositionCount (fun _ => True) n m = 0

/-- For a fixed positive integer `m`, `a(n, m) ∼ n^{m-1} / (2^{⌊m/2⌋} (m-1)!)` as `n → ∞`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 1 (`integers-2024-A35-cor-1`). -/
public theorem_wanted arndtCompositionCount_isEquivalent (m : ℕ) (hm : 0 < m) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (arndtCompositionCount (fun _ => True) n m : ℝ))
      (fun n : ℕ => (n : ℝ) ^ (m - 1) / (2 ^ (m / 2) * (Nat.factorial (m - 1) : ℝ)))

/-- The number `a(n) = ∑_m a(n, m)` of Arndt compositions has generating function
`A(x, 1) = (1 - x²)/(1 - x - x²)`, and `a(n) = F_n` for all `n ≥ 1`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 2 (`integers-2024-A35-cor-2`). -/
public theorem_wanted arndtComposition_total_eq_fib :
    (PowerSeries.mk fun n =>
        ((∑ m ∈ Finset.range (n + 1), arndtCompositionCount (fun _ => True) n m : ℕ) : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2) = 1 - PowerSeries.X ^ 2 ∧
      ∀ n : ℕ, 1 ≤ n →
        ∑ m ∈ Finset.range (n + 1), arndtCompositionCount (fun _ => True) n m = Nat.fib n

/-- The expected number of parts of a uniformly random Arndt composition of `n`,
`p(n)/a(n) = (∑_m m a(n, m)) / F_n`, is asymptotically `(3/√5 - 1) n`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 5 (`integers-2024-A35-thm-5`). -/
public theorem_wanted arndtComposition_expected_parts_isEquivalent :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ =>
        (∑ m ∈ Finset.range (n + 1), (m * arndtCompositionCount (fun _ => True) n m : ℝ)) /
          (Nat.fib n : ℝ))
      (fun n : ℕ => (3 / Real.sqrt 5 - 1) * n)

/-- The generating function of anti-palindromic compositions by weight and number of parts is
`Ap(x, y) = (1 - x - x² + x³ + xy - x³y)/(1 - x - x² + x³ - 2x³y²)`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 6 (`integers-2024-A35-thm-6`). -/
public theorem_wanted bivariateCountGF_antiPalindromic :
    bivariateCountGF antiPalindromicCompositionCount *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 -
          PowerSeries.C (2 * Polynomial.X ^ 2) * PowerSeries.X ^ 3) =
      1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
        PowerSeries.C Polynomial.X * PowerSeries.X -
          PowerSeries.C Polynomial.X * PowerSeries.X ^ 3

/-- The generating function of reduced anti-palindromic compositions by weight and number of
parts is `Bp(x, y) = (1 - x - x² + x³ + xy - x³y)/(1 - x - x² + x³ - x³y²)`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 3 (`integers-2024-A35-cor-3`). -/
public theorem_wanted bivariateCountGF_reducedAntiPalindromic :
    bivariateCountGF reducedAntiPalindromicCompositionCount *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 -
          PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ 3) =
      1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
        PowerSeries.C Polynomial.X * PowerSeries.X -
          PowerSeries.C Polynomial.X * PowerSeries.X ^ 3

/-- The number of Arndt compositions of `n` with `m` parts equals the number of reduced
anti-palindromic compositions of `n` with `m` parts.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 7 (`integers-2024-A35-thm-7`). -/
public theorem_wanted reducedAntiPalindromicCompositionCount_eq_arndtCompositionCount (n m : ℕ) :
    reducedAntiPalindromicCompositionCount n m = arndtCompositionCount (fun _ => True) n m

/-- The generating function of Arndt compositions by weight (`x`) and last part (`y`) is
`B(x, y) = (1 - x - x² - x²y + 2x³y + 2x⁴y - x⁵y - x⁴y²)/((1 - x - x²)(1 - xy)(1 - x²y))`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 8 (`integers-2024-A35-thm-8`). -/
public theorem_wanted bivariateCountGF_arndtLastPart :
    bivariateCountGF arndtLastPartCount *
        ((1 - PowerSeries.X - PowerSeries.X ^ 2) *
          (1 - PowerSeries.C Polynomial.X * PowerSeries.X) *
            (1 - PowerSeries.C Polynomial.X * PowerSeries.X ^ 2)) =
      1 - PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.C Polynomial.X * PowerSeries.X ^ 2 +
        PowerSeries.C (2 * Polynomial.X) * PowerSeries.X ^ 3 +
          PowerSeries.C (2 * Polynomial.X) * PowerSeries.X ^ 4 -
            PowerSeries.C Polynomial.X * PowerSeries.X ^ 5 -
              PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ 4

/-- For `n ≥ 1` and a last part `m ≥ 1`: `b(n, m) = t₁(n - m)` if `m ≤ n < 2m`,
`b(n, m) = t₁(n - m) + t₂(n - 2m)` if `2m ≤ n`, and `b(n, m) = 0` otherwise, where
`t₁(0) = 1`, `t₁(1) = 0`, `t₁(r) = F_{r-2}` and `t₂(0) = 0`, `t₂(1) = 1`, `t₂(r) = F_{r-1}` for
`r ≥ 2`. The paper leaves the range of `m` implicit; at `m = 0` the printed formula fails
(`b(1, 0) = 0`, formula `t₁(1) + t₂(1) = 1`), so `m ≥ 1` (a last part) is assumed.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 9 (`integers-2024-A35-thm-9`). -/
public theorem_wanted arndtLastPartCount_eq (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    let t₁ : ℕ → ℕ := fun r => if r = 0 then 1 else if r = 1 then 0 else Nat.fib (r - 2)
    let t₂ : ℕ → ℕ := fun r => if r = 0 then 0 else if r = 1 then 1 else Nat.fib (r - 1)
    arndtLastPartCount n m =
      if n < m then 0 else if n < 2 * m then t₁ (n - m) else t₁ (n - m) + t₂ (n - 2 * m)

/-- For a fixed positive integer `m`,
`b(n, m) ∼ (φ^{n-m-2}/√5)(1 + 1/φ^{m-1})` as `n → ∞`, with `φ` the golden ratio.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 10 (`integers-2024-A35-thm-10`). -/
public theorem_wanted arndtLastPartCount_isEquivalent (m : ℕ) (hm : 0 < m) :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (arndtLastPartCount n m : ℝ))
      (fun n : ℕ => Real.goldenRatio ^ ((n : ℤ) - m - 2) / Real.sqrt 5 *
        (1 + 1 / Real.goldenRatio ^ ((m : ℤ) - 1)))

/-- For `k ≥ 1` and `n ≥ 2k + 2`, the number `b^{(≤k)}(n)` of Arndt compositions of `n` with last
part at most `k` is `F_n - F_{n-k-1} - F_{n-2k-2}`, and the number `b^{(≥k)}(n)` with last part at
least `k` is `F_{n-k} + F_{n-2k}`. The paper prints the second as `F_{n-k} - F_{n-2k}`, which is
false (`k = 1`, `n = 4`: all `F_4 = 3` Arndt compositions of `4` have last part `≥ 1`, printed
value `F_3 - F_2 = 1`); the sign `+` is the one the paper's own consequence uses
(`F_{n-2} + F_{n-4}` compositions with last part greater than `1`) and is what
`b^{(≥k)}(n) = F_n - b^{(≤k-1)}(n)` gives.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 4 (`integers-2024-A35-cor-4`). -/
public theorem_wanted arndtLastPart_atMost_atLeast (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k + 2 ≤ n) :
    ((∑ j ∈ Finset.Icc 1 k, arndtLastPartCount n j : ℕ) : ℤ) =
        Nat.fib n - Nat.fib (n - k - 1) - Nat.fib (n - 2 * k - 2) ∧
      ∑ j ∈ Finset.Icc k n, arndtLastPartCount n j = Nat.fib (n - k) + Nat.fib (n - 2 * k)

/-- For `k ≥ 0` the generating function of `k`-Arndt compositions by weight and number of parts
is `A_k(x, y) = (1 - x²)(1 - x(1 - y))/(1 - x - x² + x³ - x^{3+k}y²)`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 11, case `k ≥ 0`
(`integers-2024-A35-thm-11`). -/
public theorem_wanted bivariateCountGF_kArndt_nonneg (k : ℕ) :
    bivariateCountGF (kArndtCompositionCount k) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 -
          PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ (3 + k)) =
      (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X + PowerSeries.C Polynomial.X * PowerSeries.X)

/-- For `k < 0`, written `k = -k'` with `k' ≥ 1`, the generating function of `k`-Arndt
compositions by weight and number of parts is
`A_k(x, y) = (1 - x²)(1 - x(1 - y))/(1 - x - x²(1 + y²) + x³(1 - y²) + y²x^{2-k})`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 11, case `k < 0`
(`integers-2024-A35-thm-11`). -/
public theorem_wanted bivariateCountGF_kArndt_neg (k' : ℕ) (hk' : 0 < k') :
    bivariateCountGF (kArndtCompositionCount (-(k' : ℤ))) *
        (1 - PowerSeries.X - PowerSeries.C (1 + Polynomial.X ^ 2) * PowerSeries.X ^ 2 +
          PowerSeries.C (1 - Polynomial.X ^ 2) * PowerSeries.X ^ 3 +
            PowerSeries.C (Polynomial.X ^ 2) * PowerSeries.X ^ (2 + k')) =
      (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X + PowerSeries.C Polynomial.X * PowerSeries.X)

/-- For `k ≥ 0` the number `a_k(n) = ∑_m a_k(n, m)` of `k`-Arndt compositions has generating
function `A_k(x) = (1 - x²)/(1 - x - x² + x³ - x^{k+3})`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 6, case `k ≥ 0`
(`integers-2024-A35-cor-6`). -/
public theorem_wanted kArndtComposition_total_gf_nonneg (k : ℕ) :
    (PowerSeries.mk fun n =>
        ((∑ m ∈ Finset.range (n + 1), kArndtCompositionCount k n m : ℕ) : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 - PowerSeries.X ^ (k + 3)) =
      1 - PowerSeries.X ^ 2

/-- For `k < 0`, written `k = -k'` with `k' ≥ 1`, the number `a_k(n)` of `k`-Arndt compositions
has generating function `A_k(x) = (1 - x²)/(1 - x - 2x² + x^{2-k})`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 6, case `k < 0`
(`integers-2024-A35-cor-6`). -/
public theorem_wanted kArndtComposition_total_gf_neg (k' : ℕ) (hk' : 0 < k') :
    (PowerSeries.mk fun n =>
        ((∑ m ∈ Finset.range (n + 1), kArndtCompositionCount (-(k' : ℤ)) n m : ℕ) : ℤ)) *
        (1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ (2 + k')) =
      1 - PowerSeries.X ^ 2

/-- For `k ≥ 1` the generating function of `k`-block Arndt compositions by weight and number of
parts is `A^{(k)}(x, y) = (∑_{j=0}^{k-1} J_j(x, y))/(1 - J_k(x, y))` with
`J_j(x, y) = x^{C(j+1, 2)} yʲ ∏_{ℓ=1}^{j} 1/(1 - x^ℓ)`; stated after multiplying through by
`∏_{ℓ=1}^{k} (1 - x^ℓ)`:
`A^{(k)} · (∏_{ℓ=1}^{k} (1 - x^ℓ) - x^{C(k+1, 2)} yᵏ) = ∑_{j<k} x^{C(j+1, 2)} yʲ ∏_{ℓ=j+1}^{k} (1 - x^ℓ)`.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Theorem 12 (`integers-2024-A35-thm-12`). -/
public theorem_wanted bivariateCountGF_blockArndt (k : ℕ) (hk : 1 ≤ k) :
    bivariateCountGF (blockArndtCompositionCount k) *
        ((∏ ℓ ∈ Finset.Icc 1 k, (1 - PowerSeries.X ^ ℓ)) -
          PowerSeries.C (Polynomial.X ^ k) * PowerSeries.X ^ Nat.choose (k + 1) 2) =
      ∑ j ∈ Finset.range k,
        PowerSeries.C (Polynomial.X ^ j) * PowerSeries.X ^ Nat.choose (j + 1) 2 *
          ∏ ℓ ∈ Finset.Ioc j k, (1 - PowerSeries.X ^ ℓ)

end

end MetaMathlibExt
