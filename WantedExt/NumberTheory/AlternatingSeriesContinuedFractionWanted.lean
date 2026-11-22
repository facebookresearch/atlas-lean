/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

namespace MetaMathlibExt

@[expose] public section

/-- Alternating series whose continued fractions follow a two-step partial-quotient pattern (the
quotients follow the pattern; they need not repeat): let `(x_i)` be positive integers with
`x_0 = 1` and let `x = ∑_{i ≥ 0} (-1)^i / x_i` be irrational with continued fraction
`[0; a_1, a_2, …]` and convergents `p_n / q_n`. If `∑_{i=0}^{n} (-1)^i / x_i = p_{n+1} / q_{n+1}`,
`x_{2n+1} ∣ x_{2n+2}` and
`x_{2n+3} = (x_{2n+2}/x_{2n+1} · x_{2n}/x_{2n-1} ⋯ x_2/x_1)^2 + x_{2n+2}` for all `n ≥ 0`, then
(i) `x_n = q_n q_{n+1}`, (ii) `q_{2n+1} ∣ a_{2n+3}`, and (iii) `a_{2n+2} = 1` for `n ≥ 1`.

`q_n` is `(GenContFract.of x).dens n`, `p_n` is `nums n`, and `a_k` is `partDens.get? (k - 1)`.
Deviation: part (iii) is stated for `n ≥ 1`. At `n = 0` it fails: the continued fraction
`[0; 1, 2, 1, 1, 4, 1, 32, 1, 1280, …]` (continued by `a_{2n+4} = 1`, `a_{2n+3} = q_{2n+1}`) with
`x_n = q_n q_{n+1}` (`q = 1, 1, 3, 4, 7, 32, 39, 1280, …`) satisfies every hypothesis and has
`a_2 = 2`.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Theorem 4 (`jis-2025-25.1.4-thm-4`). -/
public theorem_wanted alternatingSeries_contFract_twoStepPattern (x : ℝ) (hirr : Irrational x)
    (u : ℕ → ℕ) (hu : ∀ i, 0 < u i) (hu₀ : u 0 = 1)
    (hsum : HasSum (fun i : ℕ => (-1 : ℝ) ^ i / u i) x)
    (hconv : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i / u i =
      (GenContFract.of x).nums (n + 1) / (GenContFract.of x).dens (n + 1))
    (hdvd : ∀ n : ℕ, u (2 * n + 1) ∣ u (2 * n + 2))
    (hrec : ∀ n : ℕ, (u (2 * n + 3) : ℚ) =
      (∏ j ∈ Finset.range (n + 1), (u (2 * j + 2) : ℚ) / u (2 * j + 1)) ^ 2 + u (2 * n + 2)) :
    (∀ n : ℕ, (u n : ℝ) = (GenContFract.of x).dens n * (GenContFract.of x).dens (n + 1)) ∧
      (∀ n : ℕ, ∃ m : ℕ, (GenContFract.of x).partDens.get? (2 * n + 2) =
        some ((GenContFract.of x).dens (2 * n + 1) * m)) ∧
      ∀ n : ℕ, 1 ≤ n → (GenContFract.of x).partDens.get? (2 * n + 1) = some 1

/-- Alternating series whose continued fractions follow a three-step partial-quotient pattern:
let `(x_i)` be positive integers with `x_0 = 1` and let
`x = ∑_{i ≥ 0} (-1)^i / x_i` be irrational with continued fraction
`[0; a_1, a_2, …]` and convergents `p_n / q_n`. If `∑_{i=0}^{n} (-1)^i / x_i = p_{n+1} / q_{n+1}`,
`x_{3n+2} ∣ x_{3n+3}`,
`x_{3n+2} - x_{3n+1} = (x_{3n+1}/x_{3n} · x_{3n-1}/x_{3n-2} · x_{3n-3}/x_{3n-4} ⋯)^2` and
`x_{3n+4} - x_{3n+3} = (x_{3n+3}/x_{3n+2})^2 (x_{3n+2} - x_{3n+1})` for all `n ≥ 0`, then
(i) `x_n = q_n q_{n+1}`, (ii) `q_{3n+2} ∣ a_{3n+4}`, (iii) `a_{3n+3} = 1`, and `a_{3n+2} = 1` for
`n ≥ 1`.

The product is read as `∏ x_{k+1}/x_k` over `k = 3n, 3n - 2, 3n - 4, …, k ≥ 0` (it ends with
`x_2/x_1` for odd `n` as printed, and with `x_1/x_0` for even `n`). `q_n`, `p_n`, `a_k` are as in
`alternatingSeries_contFract_twoStepPattern`. Deviation: `a_{3n+2} = 1` is stated for `n ≥ 1`. At
`n = 0` it fails: `[0; 1, 2, 1, 3, 1, 1, 19, 1, 1, 699, …]` with `x_n = q_n q_{n+1}` satisfies every
hypothesis and has `a_2 = 2`.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Theorem 10 (`jis-2025-25.1.4-thm-10`). -/
public theorem_wanted alternatingSeries_contFract_threeStepPattern (x : ℝ) (hirr : Irrational x)
    (u : ℕ → ℕ) (hu : ∀ i, 0 < u i) (hu₀ : u 0 = 1)
    (hsum : HasSum (fun i : ℕ => (-1 : ℝ) ^ i / u i) x)
    (hconv : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i / u i =
      (GenContFract.of x).nums (n + 1) / (GenContFract.of x).dens (n + 1))
    (hdvd : ∀ n : ℕ, u (3 * n + 2) ∣ u (3 * n + 3))
    (hrec₁ : ∀ n : ℕ, (u (3 * n + 2) : ℚ) - u (3 * n + 1) =
      (∏ j ∈ Finset.range (3 * n / 2 + 1), (u (3 * n - 2 * j + 1) : ℚ) / u (3 * n - 2 * j)) ^ 2)
    (hrec₂ : ∀ n : ℕ, (u (3 * n + 4) : ℚ) - u (3 * n + 3) =
      ((u (3 * n + 3) : ℚ) / u (3 * n + 2)) ^ 2 * (u (3 * n + 2) - u (3 * n + 1))) :
    (∀ n : ℕ, (u n : ℝ) = (GenContFract.of x).dens n * (GenContFract.of x).dens (n + 1)) ∧
      (∀ n : ℕ, ∃ m : ℕ, (GenContFract.of x).partDens.get? (3 * n + 3) =
        some ((GenContFract.of x).dens (3 * n + 2) * m)) ∧
      (∀ n : ℕ, (GenContFract.of x).partDens.get? (3 * n + 2) = some 1) ∧
      ∀ n : ℕ, 1 ≤ n → (GenContFract.of x).partDens.get? (3 * n + 1) = some 1

/-- The convergent denominators `q_n` of the two-step pattern
`[0; ω₀, 1, ω₁ q₁^β, 1, ω₂ q₃^β, 1, …]` (display (e2)): `q₀ = 1`, `q₁ = ω₀`,
`q_{2n+2} = q_{2n+1} + q_{2n}` and `q_{2n+3} = ω_{n+1} q_{2n+1}^β q_{2n+2} + q_{2n+1}`
(display (e22)).

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.1, displays (e2) and (e22). -/
public def twoStepPatternDen (β : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => ω 0
  | n + 2 => if n % 2 = 0 then twoStepPatternDen β ω (n + 1) + twoStepPatternDen β ω n
      else ω (n / 2 + 1) * twoStepPatternDen β ω n ^ β * twoStepPatternDen β ω (n + 1) +
        twoStepPatternDen β ω n

/-- Small values: for `ω ≡ 1` and `β = 1` (the paper's first example),
`q = 1, 1, 2, 3, 5, 18, 23, 432, …`.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.1, first example. -/
public theorem twoStepPatternDen_one_one :
    (List.range 8).map (twoStepPatternDen 1 fun _ => 1) = [1, 1, 2, 3, 5, 18, 23, 432] := by
  decide

/-- The convergent denominators `q_n` of the three-step pattern
`[0; ω₀, 1, 1, ω₁ q₂^β, 1, 1, ω₂ q₅^β, …]` (display (e3)): `q₀ = 1`, `q₁ = ω₀`,
`q_{3n+2} = q_{3n+1} + q_{3n}`, `q_{3n+3} = q_{3n+2} + q_{3n+1}` and
`q_{3n+4} = ω_{n+1} q_{3n+3} q_{3n+2}^β + q_{3n+2}` (display (e33)).

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.2, displays (e3) and (e33). -/
public def threeStepPatternDen (β : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => ω 0
  | n + 2 => if n % 3 = 2 then
        ω (n / 3 + 1) * threeStepPatternDen β ω (n + 1) * threeStepPatternDen β ω n ^ β +
          threeStepPatternDen β ω n
      else threeStepPatternDen β ω (n + 1) + threeStepPatternDen β ω n

/-- Small values: for `ω ≡ 1` and `β = 1`, `q = 1, 1, 2, 3, 8, 11, 19, 220, …`.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Section 2.2, display (e33). -/
public theorem threeStepPatternDen_one_one :
    (List.range 8).map (threeStepPatternDen 1 fun _ => 1) = [1, 1, 2, 3, 8, 11, 19, 220] := by
  decide

/-- **Two-step pattern as an alternating series**: for `β ≥ 0` and positive integers `ω_n`,
with `q_n = twoStepPatternDen β ω n`, the series `x = ∑_{i ≥ 0} (-1)^i/(q_i q_{i+1})`
converges and `x = [0; ω₀, 1, ω₁ q₁^β, 1, ω₂ q₃^β, 1, …]`, i.e. `a₀ = 0`, `a₁ = ω₀`,
`a_{2n+2} = 1` and `a_{2n+3} = ω_{n+1} q_{2n+1}^β`. The paper's `β ∈ ℤ_{>0}` is relaxed to
`β ≥ 0`; `a_k` is `(GenContFract.of x).partDens.get? (k - 1)` and `a₀` is `.h`.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Proposition 2, under the hypotheses (e2) of Section 2.1. -/
public theorem_wanted twoStepPattern_alternatingSeries_contFract (β : ℕ) (ω : ℕ → ℕ)
    (hω : ∀ n, 0 < ω n) :
    let q := twoStepPatternDen β ω
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    Summable (fun i : ℕ => (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))) ∧
      (GenContFract.of x).h = 0 ∧ (GenContFract.of x).partDens.get? 0 = some (ω 0 : ℝ) ∧
      ∀ n : ℕ, (GenContFract.of x).partDens.get? (2 * n + 1) = some 1 ∧
        (GenContFract.of x).partDens.get? (2 * n + 2) = some ((ω (n + 1) : ℝ) * q (2 * n + 1) ^ β)

/-- **Irrationality exponent of the two-step pattern**: for `β ≥ 1` and positive integers
`ω_n`, the number `x` of `twoStepPattern_alternatingSeries_contFract` has
`μ(x) ≥ 2 + β + limsup_n ln ω_n / ln q_{2n} ≥ 2 + β ≥ 3`, and `x` is transcendental.
`μ(x) ≥ M` is stated as `LiouvilleWith p x` for every real `p < M` (with the limsup in
`EReal`, possibly `+∞`); the final `2 + β ≥ 3` is immediate from `β ≥ 1`.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Theorem 3. -/
public theorem_wanted twoStepPattern_irrationalityExponent (β : ℕ) (hβ : 1 ≤ β) (ω : ℕ → ℕ)
    (hω : ∀ n, 0 < ω n) :
    let q := twoStepPatternDen β ω
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    let L : EReal := Filter.limsup (fun n : ℕ =>
      ((Real.log (ω n) / Real.log (q (2 * n)) : ℝ) : EReal)) Filter.atTop
    (∀ p : ℝ, (p : EReal) < 2 + β + L → LiouvilleWith p x) ∧
      (2 + β : EReal) ≤ 2 + β + L ∧ Transcendental ℤ x

/-- **Three-step pattern as an alternating series**: for `β ≥ 0` and positive integers
`ω_n`, with `q_n = threeStepPatternDen β ω n`, the series
`x = ∑_{i ≥ 0} (-1)^i/(q_i q_{i+1})` converges and
`x = [0; ω₀, 1, 1, ω₁ q₂^β, 1, 1, ω₂ q₅^β, …]`, i.e. `a₀ = 0`, `a₁ = ω₀`,
`a_{3n+2} = a_{3n+3} = 1` and `a_{3n+4} = ω_{n+1} q_{3n+2}^β`. The paper's `β ∈ ℤ_{>0}` is
relaxed to `β ≥ 0`; `a_k` is `(GenContFract.of x).partDens.get? (k - 1)`.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Proposition 8, under the hypotheses (e3) of Section 2.2. -/
public theorem_wanted threeStepPattern_alternatingSeries_contFract (β : ℕ) (ω : ℕ → ℕ)
    (hω : ∀ n, 0 < ω n) :
    let q := threeStepPatternDen β ω
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    Summable (fun i : ℕ => (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))) ∧
      (GenContFract.of x).h = 0 ∧ (GenContFract.of x).partDens.get? 0 = some (ω 0 : ℝ) ∧
      ∀ n : ℕ, (GenContFract.of x).partDens.get? (3 * n + 1) = some 1 ∧
        (GenContFract.of x).partDens.get? (3 * n + 2) = some 1 ∧
        (GenContFract.of x).partDens.get? (3 * n + 3) = some ((ω (n + 1) : ℝ) * q (3 * n + 2) ^ β)

/-- **Irrationality exponent of the three-step pattern**: for `β ≥ 1` and positive integers
`ω_n`, the number `x` of `threeStepPattern_alternatingSeries_contFract` has
`μ(x) ≥ 2 + β + limsup_n ln ω_n / ln q_{3n} ≥ 2 + β ≥ 3`, and `x` is transcendental, with
`μ(x) ≥ M` encoded as in `twoStepPattern_irrationalityExponent`.

Source: Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with
Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025),
Article 25.1.4, Theorem 9. -/
public theorem_wanted threeStepPattern_irrationalityExponent (β : ℕ) (hβ : 1 ≤ β) (ω : ℕ → ℕ)
    (hω : ∀ n, 0 < ω n) :
    let q := threeStepPatternDen β ω
    let x := ∑' i : ℕ, (-1 : ℝ) ^ i / ((q i : ℝ) * q (i + 1))
    let L : EReal := Filter.limsup (fun n : ℕ =>
      ((Real.log (ω n) / Real.log (q (3 * n)) : ℝ) : EReal)) Filter.atTop
    (∀ p : ℝ, (p : EReal) < 2 + β + L → LiouvilleWith p x) ∧
      (2 + β : EReal) ≤ 2 + β + L ∧ Transcendental ℤ x

end

end MetaMathlibExt
