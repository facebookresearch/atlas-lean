/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Explicit estimates for incomplete exponential sums (statements)

Statement-only targets from Todd Cochrane, *Explicit Estimates for Incomplete Exponential
Sums*. The incomplete sum `S_p(f, B) = ∑_{x=1}^{B} e_p(f(x))`, with `e_p(t) = e^{2πit/p}`, is
written out inline: `∑ x ∈ Finset.Icc 1 B, Complex.exp (2 * π * I * f(x) / p)`. The maximum
`Φ(f, p) = max_{0 ≤ y ≤ p-1} |∑_{x=1}^{p} e_p(f(x) + y x)|` of (1.1) is written inline as a
`Finset.sup` of `‖·‖₊` over `Finset.range p`, and `d_p(f)` as the `natDegree` of the image of
`f` in `(ZMod p)[X]`.
-/

namespace MetaMathlibExt

open Complex Finset

@[expose] public section

/-- For `0 < x < 1`, `1 / sin(πx) < (1/π) (1/x + 2x / (1 - x²))`: the first two terms of the
partial-fraction expansion of `π / sin(πx)` bound it from above.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.1 (quoted from [3, Lemma 2.2]) (`integers-2025-A48-lem-3-1`). -/
public theorem_wanted one_div_sin_pi_lt (x : ℝ) (hx₀ : 0 < x) (hx₁ : x < 1) :
    1 / Real.sin (Real.pi * x) < (1 / Real.pi) * (1 / x + 2 * x / (1 - x ^ 2))

/-- For a prime `p`, an integer `a` with `p ∤ a`, and `1 ≤ B < p/2`,
`∑_{h=1}^{B} 1 / |sin(π a h / p)| < (p/π)(log B + γ + 1/(2B)) + p B (B + 1) / (π (p² - B²))`,
with `γ` the Euler–Mascheroni constant.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.2 (`integers-2025-A48-lem-3-2`). -/
public theorem_wanted sum_one_div_abs_sin_lt (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : 1 ≤ B) (hB : (B : ℝ) < p / 2) :
    ∑ h ∈ Icc 1 B, 1 / |Real.sin (Real.pi * a * h / p)| <
      (p / Real.pi) * (Real.log B + Real.eulerMascheroniConstant + 1 / (2 * B)) +
        p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2))

/-- For every positive integer `K` and real `ξ`,
`∑_{y=1}^{K} |sin(yξ)| / y < (2/π)(log(K + 1) + γ + log 2) + 3 / (π (K + 1))`, and, in the
form (3.1) obtained from `log(K + 1) < log K + 1/K`,
`∑_{y=1}^{K} |sin(yξ)| / y < (2/π) log K + (2/π)(γ + log 2) + 5 / (π K)`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.4 (quoted from [3, Lemma 2.1]) and inequality (3.1)
(`integers-2025-A48-lem-3-4`). -/
public theorem_wanted sum_abs_sin_mul_div_lt (K : ℕ) (hK : 1 ≤ K) (ξ : ℝ) :
    ∑ y ∈ Icc 1 K, |Real.sin (y * ξ)| / y <
        (2 / Real.pi) * (Real.log (K + 1) + Real.eulerMascheroniConstant + Real.log 2) +
          3 / (Real.pi * (K + 1)) ∧
      ∑ y ∈ Icc 1 K, |Real.sin (y * ξ)| / y <
        (2 / Real.pi) * Real.log K +
          (2 / Real.pi) * (Real.eulerMascheroniConstant + Real.log 2) + 5 / (Real.pi * K)

/-- Selberg-type majorant and minorant: for an interval `J = [a, b]` of the circle
`𝕋 = ℝ/ℤ` of length `b - a < 1` and a positive integer `K`, there are trigonometric polynomials
`S_±(x) = ∑_{k=-K}^{K} α_±(k) e^{2πikx}` with `α_±(0) = b - a ± 1/(K+1)` and
`S_-(x) ≤ 1_J(x) ≤ S_+(x)` for all `x`. Here `S_±` are real-valued (stated as vanishing
imaginary part) and `1_J(x) = 1` exactly when `x - n ∈ [a, b]` for some integer `n`; the
hypothesis `a ≤ b` makes `J` an interval. Partial statement: only the zero coefficients and the
pointwise sandwich, as in the extracted record; bounds on the nonzero coefficients `α_±(k)`
(as in the classical Selberg–Vaaler construction) are not part of the record and are not stated.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 4.1 (`integers-2025-A48-lem-4-1`). -/
public theorem_wanted exists_trigPoly_minorant_majorant (a b : ℝ) (hab : a ≤ b)
    (hlen : b - a < 1) (K : ℕ) (hK : 1 ≤ K) :
    ∃ αm αp : ℤ → ℂ,
      αm 0 = ((b - a - 1 / (K + 1) : ℝ) : ℂ) ∧ αp 0 = ((b - a + 1 / (K + 1) : ℝ) : ℂ) ∧
      ∀ x : ℝ,
        let Sm := ∑ k ∈ Icc (-(K : ℤ)) K, αm k * exp (2 * Real.pi * I * k * x)
        let Sp := ∑ k ∈ Icc (-(K : ℤ)) K, αp k * exp (2 * Real.pi * I * k * x)
        let ind : ℝ := Set.indicator {y : ℝ | ∃ n : ℤ, a ≤ y - n ∧ y - n ≤ b} 1 x
        Sm.im = 0 ∧ Sp.im = 0 ∧ Sm.re ≤ ind ∧ ind ≤ Sp.re

/-- Theorem 1.2: for a prime `p`, a quadratic `f(x) = a x² + b x + c` with `p ∤ a`, and a
positive integer `B` with `√p < B < p/2`,
`|S_p(f, B)| < √((2/π) p log(16.6 B² / p))`.
The hypothesis that `p` is prime is the paper's standing assumption on `S_p`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Theorem 1.2 (`integers-2025-A48-thm-1-2`). -/
public theorem_wanted norm_incomplete_quadratic_sum_lt (p : ℕ) (hp : p.Prime) (a b c : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : Real.sqrt p < B) (hB₂ : (B : ℝ) < p / 2) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 2 + b * x + c : ℤ) : ℂ) / p)‖ <
      Real.sqrt ((2 / Real.pi) * p * Real.log (16.6 * B ^ 2 / p))

/-- Theorem 1.4: for a prime `p`, a monic cubic `f(x) = x³ + b x² + c x`, and a positive
integer `B` with `4 p^{1/3} < B < √(p/12)`,
`|S_p(f, B)| < (Bp)^{1/4} log^{1/4}(B³/p) log^{1/4}(Bp)`, and in particular
`|S_p(f, B)| < (Bp)^{1/4} log^{1/2} p`. The "in particular" bound is stated on the same range
`4 p^{1/3} < B < √(p/12)` (the paper's sentence says only `B < √(p/12)`).

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Theorem 1.4 (`integers-2025-A48-thm-1-4`). -/
public theorem_wanted norm_incomplete_monic_cubic_sum_lt (p : ℕ) (hp : p.Prime) (b c : ℤ)
    (B : ℕ) (hB₁ : 4 * (p : ℝ) ^ ((1 : ℝ) / 3) < B) (hB₂ : (B : ℝ) < Real.sqrt (p / 12)) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((x ^ 3 + b * x ^ 2 + c * x : ℤ) : ℂ) / p)‖ <
        ((B : ℝ) * p) ^ ((1 : ℝ) / 4) * Real.log ((B : ℝ) ^ 3 / p) ^ ((1 : ℝ) / 4) *
          Real.log ((B : ℝ) * p) ^ ((1 : ℝ) / 4) ∧
      ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((x ^ 3 + b * x ^ 2 + c * x : ℤ) : ℂ) / p)‖ <
        ((B : ℝ) * p) ^ ((1 : ℝ) / 4) * Real.log p ^ ((1 : ℝ) / 2)

/-- Lemma 2.1 (completing the sum): for a prime `p`, a polynomial `f` over `ℤ`, and
`1 ≤ B ≤ p`, there is a complex `θ` with `|θ| ≤ 1` and
`S_p(f, B) = (B/p) ∑_{x=1}^{p} e_p(f(x)) + θ T_p(B) max_{1 ≤ y ≤ p-1} |∑_{x=1}^{p} e_p(f(x) + y x)|`,
where `T_p(B) = (1/p) ∑_{y=1}^{p-1} |sin(πBy/p) / sin(πy/p)|`. The maximum is written as a
`Finset.sup` of `‖·‖₊` over `Icc 1 (p - 1)`; `θ` is complex since the sums are.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 2.1 (`integers-2025-A48-lem-2-1`). -/
public theorem_wanted exists_incompleteSum_eq_completeSum_add (p : ℕ) (hp : p.Prime)
    (f : Polynomial ℤ) (B : ℕ) (hB₁ : 1 ≤ B) (hB₂ : B ≤ p) :
    ∃ θ : ℂ, ‖θ‖ ≤ 1 ∧
      ∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p) =
        ((B : ℂ) / p) * ∑ x ∈ Icc 1 p, exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p) +
          θ * (((1 / p : ℝ) * ∑ y ∈ Icc 1 (p - 1),
              |Real.sin (Real.pi * B * y / p) / Real.sin (Real.pi * y / p)| : ℝ) : ℂ) *
            ((((Icc 1 (p - 1)).sup fun y : ℕ =>
              ‖∑ x ∈ Icc 1 p,
                exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ) : ℂ)

/-- Lemma 2.2: for a prime `p` and a polynomial `f` over `ℤ`,
`Φ(f, p) = max_{0 ≤ y ≤ p-1} |∑_{x=1}^{p} e_p(f(x) + y x)| ≥ √p`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 2.2 (`integers-2025-A48-lem-2-2`). -/
public theorem_wanted sqrt_le_sup_norm_completeSum (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) :
    Real.sqrt p ≤
      (((range p).sup fun y : ℕ =>
        ‖∑ x ∈ Icc 1 p,
          exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ)

/-- Theorem 1.1: for a prime `p`, a polynomial `f` over `ℤ` whose reduction mod `p` has degree
`d_p(f) ≥ 2`, and `1 ≤ B ≤ p`,
`|S_p(f, B)| ≤ min{(2/π²) log p + 3.29 + B/p, (4/π²) log p + B/p + 0.35} Φ(f, p)`, with
`Φ(f, p) = max_{0 ≤ y ≤ p-1} |∑_{x=1}^{p} e_p(f(x) + y x)|`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Theorem 1.1 (`integers-2025-A48-thm-1-1`). -/
public theorem_wanted norm_incompleteSum_le_min_mul_sup (p : ℕ) (hp : p.Prime)
    (f : Polynomial ℤ) (hf : 2 ≤ (f.map (Int.castRingHom (ZMod p))).natDegree) (B : ℕ)
    (hB₁ : 1 ≤ B) (hB₂ : B ≤ p) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p)‖ ≤
      min (2 / Real.pi ^ 2 * Real.log p + 3.29 + B / p)
          (4 / Real.pi ^ 2 * Real.log p + B / p + 0.35) *
        (((range p).sup fun y : ℕ =>
          ‖∑ x ∈ Icc 1 p,
            exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ)

/-- Corollary 1.1: for a prime `p ≥ 5`, a polynomial `f` over `ℤ` with `d_p(f) ≥ 2`, and
`1 ≤ B ≤ p`, `|S_p(f, B)| < Φ(f, p) log p`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Corollary 1.1 (`integers-2025-A48-cor-1-1`). -/
public theorem_wanted norm_incompleteSum_lt_sup_mul_log (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (f : Polynomial ℤ) (hf : 2 ≤ (f.map (Int.castRingHom (ZMod p))).natDegree) (B : ℕ)
    (hB₁ : 1 ≤ B) (hB₂ : B ≤ p) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((f.eval (x : ℤ) : ℤ) : ℂ) / p)‖ <
      (((range p).sup fun y : ℕ =>
          ‖∑ x ∈ Icc 1 p,
            exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ) *
        Real.log p

/-- Lemma 3.3: for a prime `p`, an integer `a` with `p ∤ a`, and `√(p/π) < B < p/2`,
`∑_{h=1}^{B} min{B, 1/|sin(π a h / p)|} < (p/π)(log(πB²/p) + 1 + πB/p) + pB(B+1)/(π(p² - B²))`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.3 (`integers-2025-A48-lem-3-3`). -/
public theorem_wanted sum_min_one_div_abs_sin_lt (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : Real.sqrt (p / Real.pi) < B) (hB₂ : (B : ℝ) < p / 2) :
    ∑ h ∈ Icc 1 B, min (B : ℝ) (1 / |Real.sin (Real.pi * a * h / p)|) <
      (p / Real.pi) * (Real.log (Real.pi * B ^ 2 / p) + 1 + Real.pi * B / p) +
        p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2))

/-- Lemma 3.5: for positive integers `q, K, B` with `K < q`,
`∑_{k=1}^{K} |sin(πBk/q)| / |sin(πk/q)| <
(2/π²) q log K + (2q/π²)(γ + log 2) + (q/π) K/(q - K) + 5q/(π²K)`, with `γ` the
Euler–Mascheroni constant. Positivity of `q` follows from `1 ≤ K < q` and is not a separate
hypothesis.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.5 (`integers-2025-A48-lem-3-5`). -/
public theorem_wanted sum_abs_sin_div_abs_sin_lt (q K B : ℕ) (hK : 1 ≤ K) (hKq : K < q)
    (hB : 1 ≤ B) :
    ∑ k ∈ Icc 1 K, |Real.sin (Real.pi * B * k / q)| / |Real.sin (Real.pi * k / q)| <
      2 / Real.pi ^ 2 * q * Real.log K +
          2 * q / Real.pi ^ 2 * (Real.eulerMascheroniConstant + Real.log 2) +
        q / Real.pi * (K / ((q : ℝ) - K)) + 5 * q / (Real.pi ^ 2 * K)

/-- Proposition 6.1: for a prime `p`, a quadratic `f(x) = a x² + b x + c` with `p ∤ a`, and a
positive integer `B` with `√p < B < p/2`,
`|S_p(f, B)|² ≤ min{(2p/π) log(B²/p) + 1.366 p + 3B + R, (2p/π) log B + 0.368 p + B + p/(πB) + R}`,
where `R = 2pB(B+1)/(π(p² - B²))`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Proposition 6.1 (`integers-2025-A48-prop-6-1`). -/
public theorem_wanted norm_sq_incomplete_quadratic_sum_le (p : ℕ) (hp : p.Prime) (a b c : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : Real.sqrt p < B) (hB₂ : (B : ℝ) < p / 2) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 2 + b * x + c : ℤ) : ℂ) / p)‖ ^ 2 ≤
      min (2 * p / Real.pi * Real.log ((B : ℝ) ^ 2 / p) + 1.366 * p + 3 * B +
            2 * p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)))
        (2 * p / Real.pi * Real.log B + 0.368 * p + B + p / (Real.pi * B) +
            2 * p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)))

/-- Corollary 6.1: for a prime `p`, a quadratic `f(x) = a x² + b x + c` with `p ∤ a`, and
`1 ≤ B ≤ p`, `|S_p(f, B)| < √p + √((2/π) p log p + p/2)`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Corollary 6.1 (`integers-2025-A48-cor-6-1`). -/
public theorem_wanted norm_incomplete_quadratic_sum_lt_sqrt_add_sqrt (p : ℕ) (hp : p.Prime)
    (a b c : ℤ) (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : 1 ≤ B) (hB₂ : B ≤ p) :
    ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 2 + b * x + c : ℤ) : ℂ) / p)‖ <
      Real.sqrt p + Real.sqrt (2 / Real.pi * p * Real.log p + p / 2)

/-- Theorem 1.3: for a prime `p ≥ 3`, a cubic `f(x) = a x³ + b x² + c x` with `p ∤ a`, and a
positive integer `B`, with `δ_p = 1.0661 / log log p`,
`|S_p(f, B)| ≤ 1.1 B^{1/4} p^{1/4 + δ_p/4} log^{1/4} p` for `B < √(p/2)`, and
`|S_p(f, B)| ≤ 1.38 (1 + p/B²)^{1/4} B^{3/4} p^{δ_p/2} log^{1/4} p` for `√(p/2) < B ≤ p`.
The hypothesis `p ≥ 3` (so that `log log p > 0`) is added: for `p = 2`, `δ_2 < 0` and
`f(x) = x³ + x`, `B = 2` give `|S_2(f, 2)| = 2` against a right-hand side below `0.86`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Theorem 1.3 (`integers-2025-A48-thm-1-3`). -/
public theorem_wanted norm_incomplete_cubic_sum_le (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (a b c : ℤ) (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB : 1 ≤ B) :
    ((B : ℝ) < Real.sqrt (p / 2) →
      ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 3 + b * x ^ 2 + c * x : ℤ) : ℂ) / p)‖ ≤
        1.1 * (B : ℝ) ^ ((1 : ℝ) / 4) *
            (p : ℝ) ^ ((1 : ℝ) / 4 + 1.0661 / Real.log (Real.log p) / 4) *
          Real.log p ^ ((1 : ℝ) / 4)) ∧
    (Real.sqrt (p / 2) < B → B ≤ p →
      ‖∑ x ∈ Icc 1 B, exp (2 * Real.pi * I * ((a * x ^ 3 + b * x ^ 2 + c * x : ℤ) : ℂ) / p)‖ ≤
        1.38 * (1 + p / (B : ℝ) ^ 2) ^ ((1 : ℝ) / 4) * (B : ℝ) ^ ((3 : ℝ) / 4) *
            (p : ℝ) ^ (1.0661 / Real.log (Real.log p) / 2) *
          Real.log p ^ ((1 : ℝ) / 4))

/-- Lemma 7.1: for real `x ≥ 2`,
`∑_{n ≤ x} τ(n)/n = (1/2) log² x + 2γ log x + C + O*(2.1 log x / x^{2/3})`, where `O*` means
the implied constant is `1`, `γ` is the Euler–Mascheroni constant, and `C = γ² - 2γ₁` with `γ₁`
the first Stieltjes constant. Mathlib has no Stieltjes constants, so `γ₁` enters through its
limit definition `γ₁ = lim_{N→∞} (∑_{k=1}^{N} log k / k - (log N)²/2)`, i.e. the constant `C`
is characterised by that limit being `(γ² - C)/2`. `τ(n)` is `n.divisors.card`.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 7.1 (`integers-2025-A48-lem-7-1`). -/
public theorem_wanted exists_sum_card_divisors_div_sub_le :
    ∃ C : ℝ,
      Filter.Tendsto
          (fun N : ℕ => ∑ k ∈ Icc 1 N, Real.log k / k - Real.log N ^ 2 / 2)
          Filter.atTop (nhds ((Real.eulerMascheroniConstant ^ 2 - C) / 2)) ∧
        ∀ x : ℝ, 2 ≤ x →
          |∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ) / n -
              (Real.log x ^ 2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log x + C)| ≤
            2.1 * Real.log x / x ^ ((2 : ℝ) / 3)

end

end MetaMathlibExt
