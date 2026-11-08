/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Square roots of cubic polynomials modulo one

Statement-only requests from Dong, Saettone, Song and Zaharescu's equidistribution paper on
square pyramidal numbers: the Kuipers–Niederreiter second-derivative exponential-sum bound they
quote, and their uniform distribution modulo one of `√q(n)` for a cubic `q` with positive leading
coefficient. Weyl's criterion (their Lemma 5) is `MetaMathlibExt.weyl_criterion` in
`MathlibExt/NumberTheory/DiophantineApproximation/WeylCriterion.lean`.

The main theorems concern `a_n = |P_n - y_n²|` (OEIS A351830), the distance from the square
pyramidal number `P_n = 1² + ⋯ + n²` to the nearest square; the definitions of `a_n`, `A(x)` and
`M_k(x)` were read from the arXiv version (arXiv:2412.10097v2), whose error terms
(`O(x^{17/12})`, `O_k(x^{3k/2 + 11/12})`) are weaker than the journal statements given here.
Proposition 9 and Lemmas 10 and 11 (`d_n = ‖√P_n‖`, the Fourier expansion of `‖u‖^k` and the
unweighted sum `G_k`) exist only in the journal version and were read from its TeX source.
-/

open Filter

namespace MetaMathlibExt

@[expose] public section

/-- Second-derivative test for exponential sums: let `a < b` be integers and `f` a real `C²`
function with `f'' ≥ ρ` on `[a, b]` or `f'' ≤ -ρ` on `[a, b]` for some `ρ > 0`. Then
`|∑_{n=a}^{b} e(f(n))| ≤ (|f'(b) - f'(a)| + 2) (4/√ρ + 3)`, where `e(x) = exp(2πix)`. Here `f`
is `C²` on all of `ℝ`; every `C²` function on `[a, b]` extends to one, so this loses nothing.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Lemma 4 (`jis-2026-26.5.5-lem-4`), quoted there from Kuipers and
Niederreiter, *Uniform Distribution of Sequences*, Thm. 2.7. -/
public theorem_wanted norm_sum_exp_two_pi_I_le_of_iteratedDeriv_two {a b : ℤ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {ρ : ℝ} (hρ : 0 < ρ)
    (hf'' : (∀ t ∈ Set.Icc (a : ℝ) b, ρ ≤ deriv (deriv f) t) ∨
      (∀ t ∈ Set.Icc (a : ℝ) b, deriv (deriv f) t ≤ -ρ)) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (f n : ℂ))‖ ≤
      (|deriv f b - deriv f a| + 2) * (4 / Real.sqrt ρ + 3)

/-- Let `q(t) = a t³ + b t² + c t + d` with real coefficients and `a > 0`. There is an integer
`T ≥ 1` such that `q(t) > 0` for real `t ≥ T`, the sequence `(√q(n))_{n ≥ T}` is uniformly
distributed modulo one (each interval `[α, β) ⊆ [0, 1]` receives asymptotic proportion `β - α`
of the fractional parts of `√q(T + n)`, `n = 0, 1, …`), and, with a constant `C` depending only on
`q`, for every integer `N ≥ T` and every nonzero integer `γ`,
`|∑_{n=T}^{N} e(γ √q(n))| ≤ C (|γ|^{1/2} N^{3/4} + |γ| N^{1/2} + |γ|^{-1/2} N^{1/4} + 1)`.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Proposition 6 (`jis-2026-26.5.5-prop-6`). -/
public theorem_wanted exists_sqrt_cubic_equidistributed_mod_one {a b c d : ℝ} (ha : 0 < a) :
    ∃ T : ℕ, 1 ≤ T ∧ (∀ t : ℝ, (T : ℝ) ≤ t → 0 < a * t ^ 3 + b * t ^ 2 + c * t + d) ∧
      (∀ α β : ℝ, 0 ≤ α → α < β → β ≤ 1 →
        Tendsto (fun N : ℕ =>
          ((Finset.filter (fun n : ℕ =>
              α ≤ Int.fract (Real.sqrt (a * ((T + n : ℕ) : ℝ) ^ 3 + b * ((T + n : ℕ) : ℝ) ^ 2 +
                c * ((T + n : ℕ) : ℝ) + d)) ∧
              Int.fract (Real.sqrt (a * ((T + n : ℕ) : ℝ) ^ 3 + b * ((T + n : ℕ) : ℝ) ^ 2 +
                c * ((T + n : ℕ) : ℝ) + d)) < β)
            (Finset.range N)).card : ℝ) / (N : ℝ))
          atTop (nhds (β - α))) ∧
      ∃ C : ℝ, ∀ N : ℕ, T ≤ N → ∀ γ : ℤ, γ ≠ 0 →
        ‖∑ n ∈ Finset.Icc T N, Complex.exp (2 * Real.pi * Complex.I *
            ((γ * Real.sqrt (a * (n : ℝ) ^ 3 + b * (n : ℝ) ^ 2 + c * n + d) : ℝ) : ℂ))‖ ≤
          C * (|(γ : ℝ)| ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) + |(γ : ℝ)| * (N : ℝ) ^ (1 / 2 : ℝ) +
            |(γ : ℝ)| ^ (-(1 / 2) : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) + 1)


/-- The square pyramidal number `P_n = 1² + 2² + ⋯ + n²`.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, equation (defn: square pyramidal number) of arXiv:2412.10097v2. -/
def squarePyramidalNumber (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, i ^ 2

/-- `a_n = |P_n - y_n²|`, the distance from `P_n` to the nearest square `y_n²` (no ties occur,
since `m² + m + 1/2` is never an integer), computed from `s = ⌊√P_n⌋` as
`min (P_n - s²) ((s + 1)² - P_n)`.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, equation (a_n first definition) of arXiv:2412.10097v2 (OEIS A351830). -/
def squarePyramidalSquareDistance (n : ℕ) : ℕ :=
  min (squarePyramidalNumber n - Nat.sqrt (squarePyramidalNumber n) ^ 2)
    ((Nat.sqrt (squarePyramidalNumber n) + 1) ^ 2 - squarePyramidalNumber n)

/-- `P_1, …, P_4 = 1, 5, 14, 30`, `a_2 = 1` (`P_2 = 5`, nearest square `4`), and
`P_24 = 4900 = 70²`, so `a_24 = 0` (the cannonball solution).

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Introduction. -/
theorem squarePyramidalSquareDistance_examples :
    (List.range 4).map (fun i => squarePyramidalNumber (i + 1)) = [1, 5, 14, 30] ∧
      squarePyramidalSquareDistance 2 = 1 ∧ squarePyramidalNumber 24 = 4900 ∧
      squarePyramidalSquareDistance 24 = 0 := by
  have h2 : squarePyramidalNumber 2 = 5 := by decide
  have h24 : squarePyramidalNumber 24 = 4900 := by decide
  have s2 : Nat.sqrt 5 = 2 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have s24 : Nat.sqrt 4900 = 70 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  refine ⟨by decide, ?_, h24, ?_⟩ <;> simp [squarePyramidalSquareDistance, h2, h24, s2, s24]

/-- The average `A(x) = (1/x) ∑_{1 ≤ n ≤ x} a_n` of the distance from a square pyramidal number
to the nearest square satisfies `A(x) = x^{3/2} / (5√3) + O(x^{5/4})` for real `x ≥ 1`, with an
absolute implied constant.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Theorem 1 (`jis-2026-26.5.5-thm-1`); arXiv:2412.10097v2 states the error
`O(x^{17/12})`. -/
public theorem_wanted squarePyramidalSquareDistance_average_asymptotic :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(1 / x) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (squarePyramidalSquareDistance n : ℝ) -
          x ^ (3 / 2 : ℝ) / (5 * Real.sqrt 3)| ≤ C * x ^ (5 / 4 : ℝ)

/-- For each positive integer `k`, the `k`-th moment `M_k(x) = ∑_{1 ≤ n ≤ x} a_n^k` satisfies
`M_k(x) = x^{3k/2 + 1} / (3^{k/2} (3k/2 + 1)(k + 1)) + O_k(x^{3k/2 + 3/4})` for real `x ≥ 1`.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Theorem 3 (`jis-2026-26.5.5-thm-3`); arXiv:2412.10097v2 states the error
`O_k(x^{3k/2 + 11/12})`. -/
public theorem_wanted squarePyramidalSquareDistance_moment_asymptotic (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (squarePyramidalSquareDistance n : ℝ) ^ k -
          x ^ (3 / 2 * (k : ℝ) + 1) /
            ((3 : ℝ) ^ ((k : ℝ) / 2) * (3 / 2 * (k : ℝ) + 1) * ((k : ℝ) + 1))| ≤
        C * x ^ (3 / 2 * (k : ℝ) + 3 / 4)

/-- Let `y n` be a nonnegative integer whose square is a closest square to `P_n` and
`d_n = |√P_n - y_n|`. Then `d_n = ‖√P_n‖ ≤ 1/2`, where `‖x‖ = |x - round x|` is the distance to
the nearest integer, and `(d_n)_{n ≥ 1}` is uniformly distributed in `[0, 1/2]`: for
`0 ≤ α < β ≤ 1/2` the proportion of `n ≤ N` with `d_n ∈ [α, β]` tends to `2(β - α)`.

`y` is any choice of closest-square roots (the source shows the choice is unique); the limit over
real `x → ∞` is taken along integers `N`, which is equivalent.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Proposition 9 (`jis-2026-26.5.5-prop-9`). -/
public theorem_wanted squarePyramidal_dist_nearest_square_root_equidistributed (y : ℕ → ℕ)
    (hy : ∀ n z : ℕ, |(squarePyramidalNumber n : ℤ) - (y n : ℤ) ^ 2| ≤
      |(squarePyramidalNumber n : ℤ) - (z : ℤ) ^ 2|) :
    (∀ n : ℕ, |Real.sqrt (squarePyramidalNumber n) - y n| =
        |Real.sqrt (squarePyramidalNumber n) - round (Real.sqrt (squarePyramidalNumber n))| ∧
      |Real.sqrt (squarePyramidalNumber n) - y n| ≤ 1 / 2) ∧
    ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ 1 / 2 →
      Tendsto (fun N : ℕ =>
        ((Finset.filter (fun n : ℕ => |Real.sqrt (squarePyramidalNumber n) - y n| ∈ Set.Icc α β)
          (Finset.Icc 1 N)).card : ℝ) / (N : ℝ)) atTop (nhds (2 * (β - α)))

/-- Fourier expansion of `g_k(u) = ‖u‖^k = |u - round u|^k` for a positive integer `k`: with
`c_k(m) = ∫_0^1 g_k(u) e(-mu) du` and `e(x) = exp(2πix)`, one has
`c_k(0) = μ_k = 1/(2^k (k+1))`, `|c_k(m)| ≤ C_k / m²` for `m ≠ 0`, the Fourier series converges
absolutely (`∑ |c_k(m)| < ∞`) and uniformly to `g_k` (symmetric partial sums over `|m| ≤ H`),
and for every integer `H ≥ 1`, uniformly in real `u`,
`g_k(u) = μ_k + ∑_{0 < |m| ≤ H} c_k(m) e(mu) + O_k(1/H)`.

`μ_k` is written as its value `1/(2^k (k+1))` from the source's equation (periodicmean).

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Lemma 10 (`jis-2026-26.5.5-lem-10`). -/
public theorem_wanted dist_round_pow_fourier_expansion (k : ℕ) (hk : 1 ≤ k) :
    let g : ℝ → ℝ := fun u => |u - round u| ^ k
    let c : ℤ → ℂ := fun m => ∫ u in (0 : ℝ)..1,
      (g u : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
    c 0 = ((1 / (2 ^ k * ((k : ℝ) + 1)) : ℝ) : ℂ) ∧
      (∃ C : ℝ, ∀ m : ℤ, m ≠ 0 → ‖c m‖ ≤ C / (m : ℝ) ^ 2) ∧
      Summable (fun m : ℤ => ‖c m‖) ∧
      TendstoUniformly (fun (H : ℕ) (u : ℝ) => ∑ m ∈ Finset.Icc (-(H : ℤ)) H,
          c m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
        (fun u => (g u : ℂ)) atTop ∧
      ∃ C : ℝ, ∀ H : ℕ, 1 ≤ H → ∀ u : ℝ,
        ‖(g u : ℂ) - c 0 - ∑ m ∈ (Finset.Icc (-(H : ℤ)) H).erase 0,
            c m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ))‖ ≤ C / H

/-- For every positive integer `k` and real `t ≥ 1`,
`G_k(t) = ∑_{1 ≤ n ≤ t} ‖√P_n‖^k = μ_k t + O_k(t^{3/4})`, where `‖x‖ = |x - round x|` and
`μ_k = 1/(2^k (k+1))`.

The source's `h(n) = √(n(n+1)(2n+1)/6)` is `√P_n`; `μ_k` is written as its value.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Lemma 11 (`jis-2026-26.5.5-lem-11`). -/
public theorem_wanted sum_dist_round_sqrt_squarePyramidal_pow (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |∑ n ∈ Finset.Icc 1 ⌊t⌋₊, |Real.sqrt (squarePyramidalNumber n) -
            round (Real.sqrt (squarePyramidalNumber n))| ^ k -
          t / (2 ^ k * ((k : ℝ) + 1))| ≤ C * t ^ (3 / 4 : ℝ)

end

end MetaMathlibExt
