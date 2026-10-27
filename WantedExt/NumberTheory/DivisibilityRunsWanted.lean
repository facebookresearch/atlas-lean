/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.NumberTheory.GeneralizedTribonacci
public import MathlibExt.NumberTheory.GibonacciNumber

namespace MetaMathlibExt

@[expose] public section

/-- A divisibility run of length at least `L`: at each of the first `L`
indices the generalized Fibonacci term is nonzero and divides the
corresponding generalized Tribonacci term. This is the relation `L' ≥ L`
for the run length `L = L(x, y; a, b, c)` of the paper's Equation (1), which
is not displayed in the extracted statements; its values at `L = 1, 2, 3`
are determined by Proposition 3 below.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (1) and
Proposition 3. -/
public def IsDivRunUpTo (x y a b c : ℤ) (L : ℕ) : Prop :=
  ∀ i : ℕ, i < L → gibonacciNumber x y i ≠ 0 ∧ gibonacciNumber x y i ∣ generalizedTribonacci a b c i

/-- Characteristic example: the empty run `L = 0` always holds.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (1). -/
public theorem isDivRunUpTo_zero (x y a b c : ℤ) : IsDivRunUpTo x y a b c 0 :=
  fun i hi => (Nat.not_lt_zero i hi).elim

/-- With `d = gcd(x, y)`, one has `gcd(P_n, P_{n-2}) = d` for all `n ≥ 3`
(paper indexing; `n ≥ 2` in the 0-based indexing used here).

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 2
(`integers-2026-A122-lem-2`). -/
public theorem_wanted int_gcd_gibonacciNumber_sub_two (x y : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    Int.gcd (gibonacciNumber x y n) (gibonacciNumber x y (n - 2)) = Int.gcd x y

/-- The backward recurrence identities `P_{n-1} = P_n - P_{n-2}` and
`P_{n-3} = P_n - 2 * P_{n-2}` for `n ≥ 4` (paper indexing; `n ≥ 3` here).

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 3
(`integers-2026-A122-lem-3`). -/
public theorem_wanted gibonacciNumber_backward (x y : ℤ) (n : ℕ) (hn : 3 ≤ n) :
    gibonacciNumber x y (n - 1) = gibonacciNumber x y n - gibonacciNumber x y (n - 2) ∧
    gibonacciNumber x y (n - 3) = gibonacciNumber x y n - 2 * gibonacciNumber x y (n - 2)

/-- The closed form `P_n = F_{n-2} * x + F_{n-1} * y` for `n ≥ 2`, where `F`
is the standard Fibonacci sequence (in the 0-based indexing used here:
`gibonacciNumber x y n = F_{n-1} * x + F_n * y` for `n ≥ 1`).

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 1
(`integers-2026-A122-prop-1`). -/
public theorem_wanted gibonacciNumber_eq_fib (x y : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    gibonacciNumber x y n = (Nat.fib (n - 1) : ℤ) * x + (Nat.fib n : ℤ) * y

/-- There are Tribonacci basis sequences `u, v, w` with initial conditions
`(1, 0, 0)`, `(0, 1, 0)`, `(0, 0, 1)` such that `Q_n = u_n * a + v_n * b +
w_n * c` for every generalized Tribonacci sequence.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 2
(`integers-2026-A122-prop-2`). -/
public theorem_wanted exists_generalizedTribonacci_basis :
    ∃ u v w : ℕ → ℤ,
      (∀ n, u (n + 3) = u (n + 2) + u (n + 1) + u n) ∧
      (∀ n, v (n + 3) = v (n + 2) + v (n + 1) + v n) ∧
      (∀ n, w (n + 3) = w (n + 2) + w (n + 1) + w n) ∧
      u 0 = 1 ∧ u 1 = 0 ∧ u 2 = 0 ∧
      v 0 = 0 ∧ v 1 = 1 ∧ v 2 = 0 ∧
      w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 1 ∧
      ∀ a b c : ℤ, ∀ n : ℕ,
        generalizedTribonacci a b c n = u n * a + v n * b + w n * c

/-- The first three run-length thresholds: a run of length `≥ 1` holds iff
`x ≠ 0` and `x ∣ a`; of length `≥ 2` iff in addition `y ≠ 0` and `y ∣ b`;
of length `≥ 3` iff in addition `x + y ≠ 0` and `x + y ∣ c`.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 3
(`integers-2026-A122-prop-3`). -/
public theorem_wanted isDivRunUpTo_small (x y a b c : ℤ) :
    (IsDivRunUpTo x y a b c 1 ↔ x ≠ 0 ∧ x ∣ a) ∧
    (IsDivRunUpTo x y a b c 2 ↔ (x ≠ 0 ∧ x ∣ a) ∧ y ≠ 0 ∧ y ∣ b) ∧
    (IsDivRunUpTo x y a b c 3 ↔
      (x ≠ 0 ∧ x ∣ a) ∧ (y ≠ 0 ∧ y ∣ b) ∧ x + y ≠ 0 ∧ x + y ∣ c)

/-- Main theorem: if a generalized Fibonacci sequence with all terms nonzero
divides a generalized Tribonacci sequence term-by-term, then the Tribonacci
sequence is identically zero.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Theorem 1
(`integers-2026-A122-thm-1`). -/
public theorem_wanted generalizedTribonacci_eq_zero_of_dvd (x y a b c : ℤ)
    (hP : ∀ n : ℕ, gibonacciNumber x y n ≠ 0)
    (hdiv : ∀ n : ℕ, gibonacciNumber x y n ∣ generalizedTribonacci a b c n) :
    ∀ n : ℕ, generalizedTribonacci a b c n = 0


/-- Lemma 1: growth bounds. With `φ` the golden ratio and `τ` the real root of
`t³ = t² + t + 1` (the paper's dominant Tribonacci root), (i) `|P_n| ≤ (|x| + |y|) φ^(n-1)` for
`n ≥ 1`; (ii) there are absolute constants `c₀, c₁ > 0` such that, for `(x, y) ≠ (0, 0)` and all
`n ≥ c₁ (log (|x| + |y|) + 1)`, `|P_n| ≥ c₀ φⁿ / (|x| + |y|)`; (iii)
`|Q_n| ≤ (|a| + |b| + |c|) τ^(n-1)` for `n ≥ 1`. Paper index `n` is `n - 1` here (`P_n` is
`gibonacciNumber x y (n - 1)`, `Q_n` is `generalizedTribonacci a b c (n - 1)`).

Lemma 1(ii) is printed with the threshold "n large enough depending on `|x| + |y|`"; the
logarithmic form of the threshold stated here is the one the paper uses, in the proof of
Theorem 2: "for `n ≥ c₁ log B` (where `c₁` absorbs the `log(|x| + |y|) ≤ log(2B)` from
Lemma 1(ii))", with the range later taken as `N = max{4, ⌈c₁ log B⌉, ⌈c₅ log B⌉}` (the `+1`
inside the threshold here absorbs that absolute small-index cutoff).

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 1
(`integers-2026-A122-lem-1`), with the threshold as used in the proof of Theorem 2. -/
public theorem_wanted gibonacci_generalizedTribonacci_growth_bounds :
    (∀ (x y : ℤ) (n : ℕ),
      |(gibonacciNumber x y n : ℝ)| ≤ (|(x : ℝ)| + |(y : ℝ)|) * Real.goldenRatio ^ n) ∧
    (∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∀ x y : ℤ, (x, y) ≠ (0, 0) →
      ∀ n : ℕ, c₁ * (Real.log (|(x : ℝ)| + |(y : ℝ)|) + 1) ≤ (n : ℝ) →
        c₀ * Real.goldenRatio ^ (n + 1) / (|(x : ℝ)| + |(y : ℝ)|)
          ≤ |(gibonacciNumber x y n : ℝ)|) ∧
    (∀ τ : ℝ, τ ^ 3 = τ ^ 2 + τ + 1 → ∀ (a b c : ℤ) (n : ℕ),
      |(generalizedTribonacci a b c n : ℝ)| ≤ (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ n)

/-- Run-length conditions are decidable (finitely many indices, integer divisibility).

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (1). -/
public instance (x y a b c : ℤ) (L : ℕ) : Decidable (IsDivRunUpTo x y a b c L) := by
  unfold IsDivRunUpTo
  infer_instance

/-- `A_B(r)`: the number of configurations `(x, y, a, b, c) ∈ [-B, B]⁵` with `(x, y) ≠ (0, 0)`
and `(a, b, c) ≠ (0, 0, 0)` (the set `𝒞_B`) whose divisibility run length is at least `r`.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (2). -/
public def divRunCount (B r : ℕ) : ℕ :=
  ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
      Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).filter fun t =>
    (t.1, t.2.1) ≠ (0, 0) ∧ (t.2.2.1, t.2.2.2.1, t.2.2.2.2) ≠ (0, 0, 0) ∧
      IsDivRunUpTo t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 r).card

/-- `A_1(1) = 156`.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4 (`integers-2026-A122-prop-4`). -/
public theorem divRunCount_one_one : divRunCount 1 1 = 156 := by
  decide +kernel

/-- Theorem 2: there is an absolute constant `C > 0` with `E(B) ≤ C log B` for all `B ≥ 2`,
stated as: every configuration in `𝒞_B` has all its divisibility runs of length at most
`C log B` (`E(B)` is the maximum run length over `𝒞_B`).

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Theorem 2
(`integers-2026-A122-thm-2`). -/
public theorem_wanted divRun_length_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 2 ≤ B → ∀ x y a b c : ℤ,
      x ∈ Set.Icc (-(B : ℤ)) B → y ∈ Set.Icc (-(B : ℤ)) B → a ∈ Set.Icc (-(B : ℤ)) B →
      b ∈ Set.Icc (-(B : ℤ)) B → c ∈ Set.Icc (-(B : ℤ)) B →
      (x, y) ≠ (0, 0) → (a, b, c) ≠ (0, 0, 0) →
      ∀ L : ℕ, IsDivRunUpTo x y a b c L → (L : ℝ) ≤ C * Real.log B

/-- Proposition 4: `A_B(1) = 4(2B+1)³ D(B) + 2B(2B+1)((2B+1)² - 1)` with
`D(B) = ∑_{m=1}^B ⌊B/m⌋`, and `A_B(1) = 32 B⁴ log B + O(B⁴)` (the `O` stated with an
explicit constant for `B ≥ 2`).

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4
(`integers-2026-A122-prop-4`). -/
public theorem_wanted divRunCount_one (B : ℕ) :
    divRunCount B 1 = 4 * (2 * B + 1) ^ 3 * ∑ m ∈ Finset.Icc 1 B, B / m
      + 2 * B * (2 * B + 1) * ((2 * B + 1) ^ 2 - 1)

/-- Proposition 4 (asymptotic): `A_B(1) = 32 B⁴ log B + O(B⁴)`.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4
(`integers-2026-A122-prop-4`). -/
public theorem_wanted divRunCount_one_asymptotic :
    ∃ K : ℝ, ∀ B : ℕ, 2 ≤ B →
      |(divRunCount B 1 : ℝ) - 32 * (B : ℝ) ^ 4 * Real.log B| ≤ K * (B : ℝ) ^ 4

/-- Proposition 5: with `d_B(m) = 2⌊B/m⌋ + 1` and `S(B) = ∑_{m=1}^B d_B(m) = 2D(B) + B`,
`A_B(2) = 4(2B+1) S(B)² - 4B²`.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 5
(`integers-2026-A122-prop-5`). -/
public theorem_wanted divRunCount_two (B : ℕ) :
    ∑ m ∈ Finset.Icc 1 B, (2 * (B / m) + 1) = 2 * ∑ m ∈ Finset.Icc 1 B, B / m + B ∧
      (divRunCount B 2 : ℤ)
        = 4 * (2 * B + 1) * (∑ m ∈ Finset.Icc 1 B, (2 * (B / m) + 1) : ℕ) ^ 2 - 4 * B ^ 2

/-- Proposition 5 (asymptotic): `A_B(2) = 32 B³ (log B)² + O(B³ log B)`, with an explicit
constant for `B ≥ 2`.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 5
(`integers-2026-A122-prop-5`). -/
public theorem_wanted divRunCount_two_asymptotic :
    ∃ K : ℝ, ∀ B : ℕ, 2 ≤ B →
      |(divRunCount B 2 : ℝ) - 32 * (B : ℝ) ^ 3 * Real.log B ^ 2|
        ≤ K * (B : ℝ) ^ 3 * Real.log B

/-- Proposition 6: with `d_B(m) = 2⌊B/m⌋ + 1`,
`A_B(3) = ∑_{x, y ∈ [-B, B], x, y, x+y ≠ 0} (d_B(|x|) d_B(|y|) d_B(|x+y|) - 1)
  = 2∑_{m,n=1}^B d_B(m)d_B(n)d_B(m+n) + 4∑_{1 ≤ n < m ≤ B} d_B(m)d_B(n)d_B(m-n)
    - (4B² - 2B)`.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 6
(`integers-2026-A122-prop-6`). -/
public theorem_wanted divRunCount_three (B : ℕ) :
    ((divRunCount B 3 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1)
                * (2 * (B / (x + y).natAbs) + 1) - 1 : ℕ)
            else 0) ∧
    (divRunCount B 3 : ℤ)
        = 2 * ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m + n)) + 1) : ℕ)
          + 4 * ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Ico 1 m,
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m - n)) + 1) : ℕ)
          - (4 * B ^ 2 - 2 * B)

/-- Proposition 7: `A_B(4) = ∑_{x, y ≠ 0, x + y ≠ 0, x + 2y ≠ 0} (T_B(x, y) - 1)`, with
`T_B(x, y) = #{(a, b, c) ∈ [-B, B]³ : x ∣ a, y ∣ b, x + y ∣ c, x + 2y ∣ a + b + c}`, and
equivalently, writing `a = xα, b = yβ, c = (x+y)γ`, `T_B(x, y)` is the number of
`(α, β, γ)` with `|α| ≤ ⌊B/|x|⌋, |β| ≤ ⌊B/|y|⌋, |γ| ≤ ⌊B/|x+y|⌋` and
`x + 2y ∣ xα + yβ + (x+y)γ` (the paper's `∑ χ_{x,y}(α, β, γ)`). The sums run over
`x, y ∈ [-B, B]`.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 7
(`integers-2026-A122-prop-7`). -/
public theorem_wanted divRunCount_four (B : ℕ) :
    ((divRunCount B 4 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0 then
              (((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
                  Finset.Icc (-(B : ℤ)) B).filter fun t =>
                    x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 ∧
                      x + 2 * y ∣ t.1 + t.2.1 + t.2.2).card : ℤ) - 1
            else 0) ∧
    (divRunCount B 4 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0 then
              (((Finset.Icc (-((B / x.natAbs : ℕ) : ℤ)) (B / x.natAbs : ℕ) ×ˢ
                  Finset.Icc (-((B / y.natAbs : ℕ) : ℤ)) (B / y.natAbs : ℕ) ×ˢ
                  Finset.Icc (-((B / (x + y).natAbs : ℕ) : ℤ)) (B / (x + y).natAbs : ℕ)).filter
                    fun t => x + 2 * y ∣ x * t.1 + y * t.2.1 + (x + y) * t.2.2).card : ℤ) - 1
            else 0

end

end MetaMathlibExt
