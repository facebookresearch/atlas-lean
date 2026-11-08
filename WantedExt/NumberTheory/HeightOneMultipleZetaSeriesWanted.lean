/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import WantedExt.NumberTheory.BernoulliStirlingHarmonicWanted
public import WantedExt.NumberTheory.HyperharmonicEulerSumsWanted

/-! # Series of height one multiple zeta functions

Statement-only requests from Paul Thomas Young, *Series of Height One Multiple Zeta
Functions*, INTEGERS 24 (2024), Article A43. The height one multiple zeta function
`ζ(s, {1}^j) = ∑_{n₁ > n₂ > ⋯ > n_{j+1} ≥ 1} n₁^{-s} (n₂ ⋯ n_{j+1})^{-1}` is
`heightOneMultipleZeta s j`: the largest index is `n + 1`, and the remaining `j` indices form a
`j`-element subset `T` of `{1, …, n}`, contributing `∏_{m ∈ T} 1/m`. The multiple Hurwitz zeta
function `ζ_r(s) = ζ_r(s, 1)` of (2.2) is `multipleHurwitzZeta r s`, with
`binom(m + r - 1, m) = r (r + 1) ⋯ (r + m - 1) / m!` written through `ascPochhammer`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The height one multiple zeta function
`ζ(s, {1}^j) = ∑_{n₁ > ⋯ > n_{j+1} ≥ 1} n₁^{-s} (n₂ ⋯ n_{j+1})^{-1}`, convergent for
`Re s > 1`.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 1. -/
public noncomputable def heightOneMultipleZeta (s : ℂ) (j : ℕ) : ℂ :=
  ∑' n : ℕ, ((n : ℂ) + 1) ^ (-s) *
    ∑ T ∈ (Finset.Icc 1 n).powersetCard j, ∏ m ∈ T, (1 / (m : ℂ))

/-- Depth one: `ζ(s, {1}^0) = ∑_{n ≥ 0} (n + 1)^{-s}`, the Riemann zeta series.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 1. -/
public theorem heightOneMultipleZeta_zero (s : ℂ) :
    heightOneMultipleZeta s 0 = ∑' n : ℕ, ((n : ℂ) + 1) ^ (-s) := by
  simp [heightOneMultipleZeta]

/-- The multiple Hurwitz zeta function of order `r` at `a = 1`, by the Dirichlet series (2.2):
`ζ_r(s) = ∑_{m ≥ 0} binom(m + r - 1, m) (m + 1)^{-s}`, convergent for `Re r < Re s`.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 2, Equation (2.2). -/
public noncomputable def multipleHurwitzZeta (r s : ℂ) : ℂ :=
  ∑' m : ℕ, (ascPochhammer ℂ m).eval r / (m.factorial : ℂ) * ((m : ℂ) + 1) ^ (-s)

/-- Order zero: `ζ_0(s) = 1`.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Section 2, Equation (2.2). -/
public theorem multipleHurwitzZeta_zero (s : ℂ) : multipleHurwitzZeta 0 s = 1 := by
  rw [multipleHurwitzZeta, tsum_eq_single 0]
  · simp
  · intro m hm
    simp [hm]

/-- For `Re s > 1`, `|r - 1| < |s - 1|` and `Re r < Re s` (where (2.2) converges),
`ζ_r(s) = ∑_{j ≥ 0} ζ(s, {1}^j) (r - 1)^j`.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Theorem 1 (`integers-2024-A43-thm-1`). -/
public theorem_wanted hasSum_heightOneMultipleZeta_mul_pow {s r : ℂ} (hs : 1 < s.re)
    (hr : ‖r - 1‖ < ‖s - 1‖) (hrs : r.re < s.re) :
    HasSum (fun j : ℕ => heightOneMultipleZeta s j * (r - 1) ^ j) (multipleHurwitzZeta r s)

/-- For a nonnegative integer `n` and `Re s > n + 1`,
`∑_j ζ(s, {1}^j) n^j = (1/n!) ∑_{m=0}^n [n, m] ζ(s - m)` with unsigned Stirling numbers of
the first kind; and for `Re s > 1`, `ζ(s) = ∑_j C_j^{(-n)} ζ(s + n, {1}^j)`, where
`C_j^{(k)} = B_j^{(k)}(1)` and the paper's poly-Bernoulli polynomial (2.6) carries `e^{-xt}`,
so `C_j^{(k)} = polyBernoulliPoly j k (-1)`.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Corollary 1 (`integers-2024-A43-cor-1`). -/
public theorem_wanted hasSum_heightOneMultipleZeta_mul_nat_pow (n : ℕ) :
    (∀ s : ℂ, (n : ℝ) + 1 < s.re →
      HasSum (fun j : ℕ => heightOneMultipleZeta s j * (n : ℂ) ^ j)
        (1 / (n.factorial : ℂ) *
          ∑ m ∈ Finset.range (n + 1), (n.stirlingFirst m : ℂ) * riemannZeta (s - m))) ∧
    ∀ s : ℂ, 1 < s.re →
      HasSum (fun j : ℕ => (polyBernoulliPoly j (-(n : ℤ)) (-1) : ℂ) *
        heightOneMultipleZeta (s + n) j) (riemannZeta s)

/-- For a positive integer `r` and `Re s > r + 1`,
`∑_{j ≥ 0} ζ(s, {1}^j) (-r)^j = ∑_{m=0}^{r-1} C(r-1, m) (-1)^m (m+1)^{-s}`; in particular, for an
integer `k > r + 1` the sum `∑_{j ≥ 0} ζ(k, {1}^j) (-r)^j` is the rational number `H_{r,k-1} / r`,
with the Roman harmonic number `H_{r,k-1} = ∑_{i=1}^r (-1)^{i-1} C(r, i) i^{-(k-1)}`
(Equation (2.18)).

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Corollary 2 (`integers-2024-A43-cor-2`). -/
public theorem_wanted tsum_heightOneMultipleZeta_mul_neg_nat_pow
    (r : ℕ) (hr : 1 ≤ r) :
    (∀ s : ℂ, (r : ℝ) + 1 < s.re →
      ∑' j : ℕ, heightOneMultipleZeta s j * (-(r : ℂ)) ^ j =
        ∑ m ∈ Finset.range r, ((r - 1).choose m : ℂ) * (-1) ^ m * ((m : ℂ) + 1) ^ (-s)) ∧
    ∀ k : ℕ, r + 1 < k →
      ∑' j : ℕ, heightOneMultipleZeta k j * (-(r : ℂ)) ^ j =
        (((∑ i ∈ Finset.Icc 1 r, (-1 : ℚ) ^ (i - 1) * (r.choose i : ℚ) / (i : ℚ) ^ (k - 1)) /
          r : ℚ) : ℂ)

/-- Generalized Goldbach series: for a positive integer `k`,
`∑_j (k^j ζ(k + 1, {1}^j) - 1/(k! k)) = (1/k!) (∑_{m=0}^{k-1} [k, m] ζ(k + 1 - m) + H_k)`, and
`∑_j (-1)^j (k^j ζ(k + 1, {1}^j) - 1/(k! k)) = H_{k,k}/k - 1/(2 k! k)`, with the Roman harmonic
number `H_{k,k} = ∑_{i=1}^k (-1)^{i-1} C(k, i) i^{-k}` (Equation (2.18)).

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Theorem 2 (`integers-2024-A43-thm-2`). -/
public theorem_wanted hasSum_heightOneMultipleZeta_goldbach (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun j : ℕ => (k : ℂ) ^ j * heightOneMultipleZeta ((k : ℂ) + 1) j -
        1 / ((k.factorial : ℂ) * k))
      (1 / (k.factorial : ℂ) *
        (∑ m ∈ Finset.range k, (k.stirlingFirst m : ℂ) * riemannZeta ((k : ℂ) + 1 - m) +
          (harmonic k : ℂ))) ∧
    HasSum (fun j : ℕ => (-1) ^ j * ((k : ℂ) ^ j * heightOneMultipleZeta ((k : ℂ) + 1) j -
        1 / ((k.factorial : ℂ) * k)))
      (((∑ i ∈ Finset.Icc 1 k, (-1 : ℚ) ^ (i - 1) * (k.choose i : ℚ) / (i : ℚ) ^ k) / k -
        1 / (2 * (k.factorial : ℚ) * k) : ℚ) : ℂ)

/-- The hyperharmonic zeta function `σ(r, s) = ∑_{m ≥ 1} H_m^{[r]} m^{-s}` has the expansion
`σ(r, s) = ∑_{j ≥ 0} (j + 1) ζ(s + 1, {1}^j) r^j` for `Re s > 0`, `|r| < |s|` and `Re r < Re s`
(where the series for `σ` converges). `H_m^{[r]} = D_r binom(m + r - 1, m)` (3.2) is
`generalizedHyperharmonic m 1 r`.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Theorem 3, second equality (`integers-2024-A43-thm-3`). -/
public theorem_wanted hasSum_succ_mul_heightOneMultipleZeta_mul_pow {r s : ℂ} (hs : 0 < s.re)
    (hr : ‖r‖ < ‖s‖) (hrs : r.re < s.re) :
    HasSum (fun j : ℕ => ((j : ℂ) + 1) * heightOneMultipleZeta (s + 1) j * r ^ j)
      (∑' m : ℕ, generalizedHyperharmonic (m + 1) 1 r * ((m : ℂ) + 1) ^ (-s))

/-- For integers `k ≥ -1` and `p ≥ 0`, the shifted alternating series
`ν_{k,p} = ∑_{n ≥ 2} (-1)^n ζ(n, {1}^p) / (n + k)` (as the limit of its partial sums) equals
`∫_0^1 (1 - r)^{k+1} ζ_r(p + 2) dr`.

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Theorem 4 (`integers-2024-A43-thm-4`). -/
public theorem_wanted tendsto_alternating_heightOneMultipleZeta_integral (k : ℤ) (hk : -1 ≤ k)
    (p : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Ico 2 N,
        (-1 : ℂ) ^ n / ((n : ℂ) + k) * heightOneMultipleZeta n p)
      Filter.atTop
      (nhds (∫ r in (0 : ℝ)..1,
        (1 - (r : ℂ)) ^ (k + 1).toNat * multipleHurwitzZeta r ((p : ℂ) + 2)))

/-- For a positive integer `j`, the linear coefficient `γ_1^{[j]}` of the Laurent expansion of
`ζ(s, {1}^{j-1})` at `s = 1` is
`∫_0^1 ((1 - r) ζ_r(j + 2) - ζ_r(j + 1)) dr - [s^{j+1}] (Γ(s + 1)^{-1})`. The Laurent expansion is
encoded on the half-plane `Re s > 1` as a principal part of order `j` plus a function `F`
analytic at `1`; the Taylor coefficient is an iterated derivative. `γ_1^{[j]}` is normalized like
the usual first Stieltjes constant `γ₁` (the paper's (4.4) is this formula for `γ₁`), so the linear
coefficient is `F'(1) = -γ_1^{[j]}`: the paper's parenthetical "the linear coefficient" drops this
sign (`ζ(s) = 1/(s - 1) + γ - γ₁ (s - 1) + ⋯` with `γ₁ ≈ -0.0728`).

Source: Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24
(2024), Article A43, Corollary 3 (`integers-2024-A43-cor-3`). -/
public theorem_wanted heightOneMultipleZeta_laurent_linear_coeff (j : ℕ) (hj : 1 ≤ j) :
    ∃ c : ℕ → ℂ, ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧
      (∀ᶠ s in nhdsWithin (1 : ℂ) {s | 1 < s.re},
        heightOneMultipleZeta s (j - 1) =
          ∑ i ∈ Finset.range j, c i / (s - 1) ^ (i + 1) + F s) ∧
      -deriv F 1 =
        (∫ r in (0 : ℝ)..1, ((1 - (r : ℂ)) * multipleHurwitzZeta r ((j : ℂ) + 2) -
          multipleHurwitzZeta r ((j : ℂ) + 1))) -
        iteratedDeriv (j + 1) (fun s : ℂ => (Complex.Gamma (s + 1))⁻¹) 0 /
          ((j + 1).factorial : ℂ)

end

end MetaMathlibExt
