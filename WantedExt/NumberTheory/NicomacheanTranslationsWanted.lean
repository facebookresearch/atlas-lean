/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Translations and extensions of the Nicomachean identity

Statements from Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the
Nicomachean Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3.

For a finite sequence `σ = (a_1, …, a_n)` the paper's operator is
`ν(σ) = (∑ a_i)^2 - ∑ a_i^3`, here `nicomacheanNu` on lists over a commutative ring; the
classical identity is `ν(1, 2, …, n) = 0`. Sequences are lists (repetitions allowed; `ν` does not
depend on the order).
-/

open Filter Topology PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- The Nicomachean defect `ν(a_1, …, a_n) = (∑ a_i)^2 - ∑ a_i^3`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 1. -/
def nicomacheanNu {R : Type*} [CommRing R] (σ : List R) : R :=
  σ.sum ^ 2 - (σ.map (· ^ 3)).sum

/-- `ν(1, 2, 3, 4) = 0`, `ν(1, 2) = 0`, `ν(3, 3, 3) = 0`, and the paper's
`ν(1, 2, 2, 3, 4, x, 6, 8) = (5 - x)(x - 4)(8 + x)` at `x = 5` (value `0`) and `x = 6`
(value `-28`).

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 1. -/
theorem nicomacheanNu_examples :
    nicomacheanNu ([1, 2, 3, 4] : List ℤ) = 0 ∧ nicomacheanNu ([1, 2] : List ℤ) = 0 ∧
      nicomacheanNu ([3, 3, 3] : List ℤ) = 0 ∧
      nicomacheanNu ([1, 2, 2, 3, 4, 5, 6, 8] : List ℤ) = 0 ∧
      nicomacheanNu ([1, 2, 2, 3, 4, 6, 6, 8] : List ℤ) = -28 := by
  decide

/-- The second factor `α(n, s, a) = 2n^2 + na - a^2 + n(n-1)(s - s^2)/2 - (n-1)as` of
`ν(S_m)` in the paper's (`nusm`), where `S_m` joins `n` copies of `n` with the arithmetic
progressions `S, S + n, …, S + mn`, `S = (a, a + s, …, a + (n-1)s)`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 6, equation (nusm). -/
def nicomacheanAlpha (n s a : ℚ) : ℚ :=
  2 * n ^ 2 + n * a - a ^ 2 + n * (n - 1) * (s - s ^ 2) / 2 - (n - 1) * a * s

/-- The paper's specializations: `α(n, 1, a) = 2n^2 + a - a^2`,
`α(n, 2, a) = n^2 + (1 - a)n - a^2 + 2a`, and `α(n, 3, a) = -(a + n - 3)(a + n)`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 6. -/
theorem nicomacheanAlpha_one_two_three (n a : ℚ) :
    nicomacheanAlpha n 1 a = 2 * n ^ 2 + a - a ^ 2 ∧
      nicomacheanAlpha n 2 a = n ^ 2 + (1 - a) * n - a ^ 2 + 2 * a ∧
      nicomacheanAlpha n 3 a = -(a + n - 3) * (a + n) := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold nicomacheanAlpha; ring

/-- Let `t(2, m) = (3(m^2 - 6m - 3) + √(3(m-1)^2(35m^2 + 34m + 11)))/24` and let `s(2, m)` be the
other root (minus sign before the square root). The second differences of `t(2, m)` converge to
`(3 + √105)/12`, those of `s(2, m)` converge to its conjugate `(3 - √105)/12`, and for
`A = (1, 2, …, m)` the second differences of the right-most real root of `t ↦ ν(A^2 + t)` converge
to `(3 + √105)/12`. Here `A^2 = (ij : 1 ≤ i, j ≤ m)` is the paper's sequential (bag) product and
`A^2 + t` translates every entry by `t`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 1
(`jis-2024-24.6.3-prop-1`). -/
public theorem_wanted nicomachean_bagSquare_root_secondDifference_tendsto :
    let t : ℕ → ℝ := fun m => (3 * ((m : ℝ) ^ 2 - 6 * m - 3) +
      Real.sqrt (3 * ((m : ℝ) - 1) ^ 2 * (35 * (m : ℝ) ^ 2 + 34 * m + 11))) / 24
    let s : ℕ → ℝ := fun m => (3 * ((m : ℝ) ^ 2 - 6 * m - 3) -
      Real.sqrt (3 * ((m : ℝ) - 1) ^ 2 * (35 * (m : ℝ) ^ 2 + 34 * m + 11))) / 24
    let ρ : ℕ → ℝ := fun m => sSup {x : ℝ | nicomacheanNu
      (((List.range' 1 m).flatMap fun i => (List.range' 1 m).map fun j => ((i * j : ℕ) : ℝ)).map
        (· + x)) = 0}
    Tendsto (fun m => t (m + 2) - 2 * t (m + 1) + t m) atTop (𝓝 ((3 + Real.sqrt 105) / 12)) ∧
      Tendsto (fun m => s (m + 2) - 2 * s (m + 1) + s m) atTop
        (𝓝 ((3 - Real.sqrt 105) / 12)) ∧
      Tendsto (fun m => ρ (m + 2) - 2 * ρ (m + 1) + ρ m) atTop (𝓝 ((3 + Real.sqrt 105) / 12))

/-- There are sequences `σ` of positive rationals with `ν(σ) = 0` containing non-integers `p/q` in
lowest terms with `q` arbitrarily large: for every `Q` some entry has denominator `> Q`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 3
(`jis-2024-24.6.3-prop-3`). -/
public theorem_wanted exists_pos_rat_nicomacheanNu_eq_zero_large_den (Q : ℕ) :
    ∃ σ : List ℚ, (∀ x ∈ σ, 0 < x) ∧ nicomacheanNu σ = 0 ∧ ∃ x ∈ σ, Q < x.den

/-- For every `ε > 0` there are sequences of positive integers with `ν = 0` having exactly two
distinct entries `a < b` such that the largest gap `b - a` divided by the length exceeds `1 - ε`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 4
(`jis-2024-24.6.3-prop-4`). -/
public theorem_wanted exists_two_valued_nicomachean_large_gap {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℤ, 0 < a ∧ a < b ∧ ∃ σ : List ℤ, (∀ x ∈ σ, x = a ∨ x = b) ∧ a ∈ σ ∧ b ∈ σ ∧
      nicomacheanNu σ = 0 ∧ 1 - ε < ((b - a : ℤ) : ℝ) / σ.length

/-- The sequences `(1, 2, …, j, j + 1, m, m, …, m)` (`m` repeated `2j` times) with `j, m ≥ 1` and
`ν = 0`: the `j`'s, in increasing order, have generating function
`(x^4 + x^3 - 19x^2 - 5x - 2)/((x - 1)(1 - 6x + x^2)(1 + 6x + x^2))`, and the corresponding
`m = j + √(2j^2 + 3j + 2)` (the positive root of `ν = 0` in `m`) have generating function
`6(1 + x)^2/((1 - x)(1 - 6x + x^2)(1 + 6x + x^2))`; both stated with denominators cleared.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 5
(`jis-2024-24.6.3-prop-5`). -/
public theorem_wanted nicomachean_run_repeat_generatingFunctions :
    let P : ℕ → Prop := fun j => 0 < j ∧ ∃ m : ℤ, 0 < m ∧
      nicomacheanNu ((List.range' 1 (j + 1)).map (fun i : ℕ => (i : ℤ)) ++
        List.replicate (2 * j) m) = 0
    let J : ℕ → ℕ := Nat.nth P
    let M : ℕ → ℕ := fun k => J k + Nat.sqrt (2 * J k ^ 2 + 3 * J k + 2)
    (∀ k, nicomacheanNu ((List.range' 1 (J k + 1)).map (fun i : ℕ => (i : ℤ)) ++
        List.replicate (2 * J k) (M k : ℤ)) = 0) ∧
      (X - 1) * (1 - 6 * X + X ^ 2) * (1 + 6 * X + X ^ 2) * PowerSeries.mk (fun k => (J k : ℤ)) =
        X ^ 4 + X ^ 3 - 19 * X ^ 2 - 5 * X - 2 ∧
      (1 - X) * (1 - 6 * X + X ^ 2) * (1 + 6 * X + X ^ 2) * PowerSeries.mk (fun k => (M k : ℤ)) =
        6 * (1 + X) ^ 2

/-- There are sequences of positive integers with `ν = 0` in which the gap between the two
largest entries is arbitrarily large: the maximum `b` occurs once and exceeds every other entry by
more than `G`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 6
(`jis-2024-24.6.3-prop-6`). -/
public theorem_wanted exists_nicomachean_large_top_gap (G : ℕ) :
    ∃ σ : List ℤ, (∀ x ∈ σ, 0 < x) ∧ nicomacheanNu σ = 0 ∧ ∃ a ∈ σ, ∃ b ∈ σ,
      σ.count b = 1 ∧ (∀ x ∈ σ, x ≤ b) ∧ a < b ∧ (∀ x ∈ σ, x ≠ b → x ≤ a) ∧ (G : ℤ) < b - a

/-- For every `N` there is a sequence `σ` of positive algebraic integers of `ℚ(√5)` (the ring
`ℤ[φ]`, numbers `p + qφ`, `p, q ∈ ℤ`) with `ν(σ) = 0`, more than half of whose entries are
irrational, containing `(1/φ)^n` for `1 ≤ n ≤ N`. "More than half irrational" is stated as a
sublist of irrational entries longer than half of `σ`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 7
(`jis-2024-24.6.3-prop-7`). -/
public theorem_wanted exists_goldenRatio_nicomachean_sequence (N : ℕ) :
    ∃ σ : List ℝ, (∀ x ∈ σ, 0 < x ∧ ∃ p q : ℤ, x = p + q * Real.goldenRatio) ∧
      (∃ τ : List ℝ, τ.Sublist σ ∧ σ.length < 2 * τ.length ∧ ∀ x ∈ τ, Irrational x) ∧
      nicomacheanNu σ = 0 ∧ ∀ n ∈ Finset.Icc 1 N, Real.goldenRatio⁻¹ ^ n ∈ σ

/-- Adjoin nonzero reals `x_1, x_2, …` (here `x 0, x 1, …`) to a finite real sequence
`(a_1, …, a_n)`, with `x_j ≠ -x_{j-1}`, so that every resulting sequence
`(a_1, …, a_n, x_1, …, x_l)`, `l ≥ 1`, has `ν = 0`. Then `x_2, x_3, …` is an arithmetic
progression with difference `1`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 8
(`jis-2024-24.6.3-prop-8`). -/
public theorem_wanted nicomachean_adjoined_arithmeticProgression (a : List ℝ) (x : ℕ → ℝ)
    (hx : ∀ j, x j ≠ 0) (hneg : ∀ j, x (j + 1) ≠ -x j)
    (hν : ∀ l, nicomacheanNu (a ++ (List.range (l + 1)).map x) = 0) :
    ∀ j, 1 ≤ j → x (j + 1) = x j + 1

/-- For `n ≥ 1`: (`s = 1`) `α(n, 1, a)` is divisible by `a - h` for some positive integer `h`
(i.e. `α(n, 1, h) = 0`) if and only if `n^2` is a triangular number `k(k+1)/2`; (`s = 2`)
`α(n, 2, a)` has a positive integer root `h` if and only if `n = F_{2k}` with `k ≥ 1`, and then
`h = F_{2k-1} + 1`. Divisibility by `a - h` is read through the factor theorem. The case `n = 0`
(no progression) is excluded: `α(0, 2, a)` has the root `2`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 9
(`jis-2024-24.6.3-prop-9`). -/
public theorem_wanted nicomacheanAlpha_posIntRoot_iff {n : ℕ} (hn : 1 ≤ n) :
    ((∃ h : ℕ, 0 < h ∧ nicomacheanAlpha n 1 h = 0) ↔ ∃ k : ℕ, 2 * n ^ 2 = k * (k + 1)) ∧
      ((∃ h : ℕ, 0 < h ∧ nicomacheanAlpha n 2 h = 0) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = Nat.fib (2 * k)) ∧
      ∀ k h : ℕ, 1 ≤ k → n = Nat.fib (2 * k) → 0 < h → nicomacheanAlpha n 2 h = 0 →
        h = Nat.fib (2 * k - 1) + 1

/-- For every `N` there are `N` distinct sequences (as multisets) of positive integers with
`ν(σ) = 0` whose adjoined polynomials `ν(σ; a, b)` share the same quadratic factor: for a common
`c` (the sum of the entries) every `ν(σ; a, b) = -(a + b)(a^2 - ab + b^2 - a - b - 2c)`.
Positivity of the entries, the paper's setting, excludes trivial families such as `(k, -k, 1)`.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 12
(`jis-2024-24.6.3-prop-12`). -/
public theorem_wanted exists_nicomachean_family_same_quadratic_factor (N : ℕ) :
    ∃ σ : Fin N → List ℤ, Function.Injective (fun i => (σ i : Multiset ℤ)) ∧ ∃ c : ℤ, ∀ i,
      (∀ x ∈ σ i, 0 < x) ∧ nicomacheanNu (σ i) = 0 ∧
        ∀ a b : ℤ, nicomacheanNu (σ i ++ [a, b]) = -(a + b) * (a ^ 2 - a * b + b ^ 2 - a - b - 2 * c)

end

end MetaMathlibExt
