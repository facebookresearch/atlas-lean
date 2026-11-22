/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Series associated with Nörlund's digamma identity

Statements from Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18 (primary text: arXiv:2410.22343).

Harmonic numbers of complex argument enter through `H_α = ψ(α + 1) + γ` (the paper's relation
(4)), written with `Complex.digamma`. Where a statement uses only differences of harmonic
numbers, `γ` cancels; Lemma 1 and Theorems 4, 6 and 7 contain standalone `H_{k-1/2}`, `H_{n+z}`
or `H_z` terms, and there `γ` appears explicitly as `Real.eulerMascheroniConstant`. The
binomial coefficient `C(n + z, n)` of complex `z` is `∏_{j=1}^n (z + j)/j`.
Differences of second-order harmonic numbers of complex argument are written through
`H^{(2)}_α = Σ_{j≥1} (1/j² - 1/(j + α)²)` (the paper's relation `H^{(2)}_α = ζ(2) - ψ'(α + 1)`),
and the odd harmonic numbers `O^{(r)}_n = Σ_{j=1}^n 1/(2j - 1)^r` of natural index as finite sums.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 1: for each integer `k ≥ 2`,
`(k - 2)(1 + Σ_{n≥1} (1/(n+1)) ∏_{j=1}^n (kj - (k-2))/(kj + 1)) = π cot(π/k)`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 1 (`integers-2025-A18-thm-1`). -/
public theorem_wanted sub_two_mul_one_add_tsum_prod_eq_pi_mul_cot {k : ℕ} (hk : 2 ≤ k) :
    ((k : ℝ) - 2) * (1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) *
        ∏ j ∈ Finset.Icc 1 (n + 1), ((k : ℝ) * j - (k - 2)) / (k * j + 1)) =
      Real.pi * Real.cot (Real.pi / k)

/-- Theorem 2: for `z ∈ ℂ` with `-1/2 < Re z < 1/2`,
`Σ_{n≥0} (2^{n+1}/(n+1)) ∏_{j=0}^n (2z - j)/(2z - (2j + 1)) = -π tan(πz)`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 2 (`integers-2025-A18-thm-2`). -/
public theorem_wanted tsum_two_pow_prod_eq_neg_pi_mul_tan {z : ℂ} (hz₁ : -1 / 2 < z.re)
    (hz₂ : z.re < 1 / 2) :
    ∑' n : ℕ, (2 : ℂ) ^ (n + 1) / ((n : ℂ) + 1) *
        ∏ j ∈ Finset.range (n + 1), (2 * z - j) / (2 * z - (2 * j + 1)) =
      -(Real.pi : ℂ) * Complex.tan (Real.pi * z)

/-- Lemma 1, for `k ∈ ℕ`: `H_{k-1/2} = 2O_k - 2 ln 2`; `H^{(2)}_{k-1/2} = -2ζ(2) + 4O^{(2)}_k`;
`H^{(3)}_{-1/2} = -6ζ(3)`; and `H^{(m+1)}_{k-1/2} - H^{(m+1)}_{-1/2} = 2^{m+1} O^{(m+1)}_k` for
`m ∈ ℕ`. Here
`H_α = ψ(α + 1) + γ` and `H^{(r)}_α = Σ_{j≥1} (1/j^r - 1/(j + α)^r)`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Lemma 1 (`integers-2025-A18-lem-1`). -/
public theorem_wanted harmonic_nat_sub_half_values (k : ℕ) :
    Complex.digamma (k + 1 / 2) + Real.eulerMascheroniConstant =
        2 * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℂ) + 1) - 2 * Complex.log 2 ∧
      ∑' j : ℕ, (1 / ((j : ℂ) + 1) ^ 2 - 1 / ((j : ℂ) + k + 1 / 2) ^ 2) =
        -2 * riemannZeta 2 + 4 * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℂ) + 1) ^ 2 ∧
      ∑' j : ℕ, (1 / ((j : ℂ) + 1) ^ 3 - 1 / ((j : ℂ) + 1 / 2) ^ 3) = -6 * riemannZeta 3 ∧
      ∀ m : ℕ, ∑' j : ℕ, (1 / ((j : ℂ) + 1 / 2) ^ (m + 1) - 1 / ((j : ℂ) + k + 1 / 2) ^ (m + 1)) =
        2 ^ (m + 1) * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℂ) + 1) ^ (m + 1)

/-- Lemma 2: `(r - 1/2)! = (√π/2^{2r}) C(2r, r) r!` for `r ∈ ℂ` off the negative integers, with
`w! = Γ(w + 1)` and `C(2r, r) r! = Γ(2r + 1)/Γ(r + 1)`; and
`(-r - 1/2)! = √π (-1)^r 2^{2r}/(r! C(2r, r))` for `r ∈ ℕ`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Lemma 2 (`integers-2025-A18-lem-2`). -/
public theorem_wanted Gamma_add_half_and_Gamma_half_sub_nat :
    (∀ r : ℂ, (∀ m : ℕ, r ≠ -((m : ℂ) + 1)) →
      Complex.Gamma (r + 1 / 2) =
        (Real.sqrt Real.pi : ℂ) / (2 : ℂ) ^ (2 * r) *
          (Complex.Gamma (2 * r + 1) / Complex.Gamma (r + 1))) ∧
    ∀ r : ℕ, Complex.Gamma (1 / 2 - r) =
      (Real.sqrt Real.pi : ℂ) * (-1) ^ r / r.factorial * 2 ^ (2 * r) / (2 * r).choose r

/-- Theorem 3 (general identity): for `Re z > 0`,
`Σ_{n≥0} C_n/(2^{2n} C(n + z, n)) = -2z(H_{z-1} - H_{z-1/2}) = -2z(ψ(z) - ψ(z + 1/2))`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 3, identity (7) (`integers-2025-A18-thm-3`). -/
public theorem_wanted tsum_catalan_div_four_pow_mul_binom {z : ℂ} (hz : 0 < z.re) :
    ∑' n : ℕ, (catalan n : ℂ) / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      -2 * z * (Complex.digamma z - Complex.digamma (z + 1 / 2))

/-- Theorem 3 (special values): `Σ_{n≥0} C_n/(2^{2n}(n+1)) = 4(1 - ln 2)` and
`Σ_{n≥0} C_n/(2^{2n}(n+1)(n+2)) = 10/3 - 4 ln 2`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 3, first two identities
(`integers-2025-A18-thm-3`). -/
public theorem_wanted tsum_catalan_div_four_pow_special :
    ∑' n : ℕ, (catalan n : ℝ) / (4 ^ n * ((n : ℝ) + 1)) = 4 * (1 - Real.log 2) ∧
      ∑' n : ℕ, (catalan n : ℝ) / (4 ^ n * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
        10 / 3 - 4 * Real.log 2

/-- Theorem 4 (special values): `Σ_{n≥0} O_{n+1}/((n + 1)(2n + 1)) = π²/6` and
`Σ_{n≥0} (C_n/2^{2n}) H_{n+1}/(n + 1) = 8 - 2π²/3`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 4, identities (8) and (9)
(`integers-2025-A18-thm-4`). -/
public theorem_wanted tsum_odd_harmonic_div_and_catalan_mul_harmonic_special :
    ∑' n : ℕ, (∑ j ∈ Finset.range (n + 1), 1 / (2 * (j : ℝ) + 1)) / (((n : ℝ) + 1) * (2 * n + 1)) =
        Real.pi ^ 2 / 6 ∧
      ∑' n : ℕ, (catalan n : ℝ) / 4 ^ n * (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) =
        8 - 2 * Real.pi ^ 2 / 3

/-- Theorem 4 (general identity): for `Re z > 0`,
`Σ_{n≥0} (C_n/2^{2n}) H_{n+z}/C(n + z, n)
  = 2(H_{z-1} - H_{z-1/2})(1 - zH_z) + 2z(H^{(2)}_{z-1/2} - H^{(2)}_{z-1})`,
with `H_α = ψ(α + 1) + γ` and
`H^{(2)}_{z-1/2} - H^{(2)}_{z-1} = Σ_{j≥0} (1/(j + z)² - 1/(j + z + 1/2)²)`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 4, identity (10)
(`integers-2025-A18-thm-4`). -/
public theorem_wanted tsum_catalan_mul_harmonic_div_four_pow_mul_binom {z : ℂ} (hz : 0 < z.re) :
    ∑' n : ℕ, (catalan n : ℂ) * (Complex.digamma (n + z + 1) + Real.eulerMascheroniConstant) /
        (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      2 * (Complex.digamma z - Complex.digamma (z + 1 / 2)) *
          (1 - z * (Complex.digamma (z + 1) + Real.eulerMascheroniConstant)) +
        2 * z * ∑' j : ℕ, (1 / ((j : ℂ) + z) ^ 2 - 1 / ((j : ℂ) + z + 1 / 2) ^ 2)

/-- Theorem 5 (general identity): for `Re z > 1/2`,
`Σ_{n≥0} (2n + 1) C_n/(2^{2n} C(n + z, n)) = 2z(H_{z-1} - H_{z-3/2}) = 2z(ψ(z) - ψ(z - 1/2))`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 5, identity (11) (`integers-2025-A18-thm-5`). -/
public theorem_wanted tsum_odd_mul_catalan_div_four_pow_mul_binom {z : ℂ} (hz : 1 / 2 < z.re) :
    ∑' n : ℕ, (2 * (n : ℂ) + 1) * catalan n / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      2 * z * (Complex.digamma z - Complex.digamma (z - 1 / 2))

/-- Theorem 5 (special values): `Σ_{n≥0} ((2n + 1)/(n + 1)) C_n/2^{2n} = 4 ln 2` and
`Σ_{n≥0} ((2n + 1)/((n + 1)(n + 2))) C_n/2^{2n} = 4 ln 2 - 2`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 5, first two identities
(`integers-2025-A18-thm-5`). -/
public theorem_wanted tsum_odd_mul_catalan_div_four_pow_special :
    ∑' n : ℕ, (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * catalan n / 4 ^ n = 4 * Real.log 2 ∧
      ∑' n : ℕ, (2 * (n : ℝ) + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) * catalan n / 4 ^ n =
        4 * Real.log 2 - 2

/-- Corollary 1: for `Re z > 1/2`,
`Σ_{n≥0} n C_n/(2^{2n} C(n + z, n)) = 2z H_{z-1} - z(H_{z-1/2} + H_{z-3/2})
  = 2zψ(z) - z(ψ(z + 1/2) + ψ(z - 1/2))`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Corollary 1 (`integers-2025-A18-cor-1`). -/
public theorem_wanted tsum_nat_mul_catalan_div_four_pow_mul_binom {z : ℂ} (hz : 1 / 2 < z.re) :
    ∑' n : ℕ, (n : ℂ) * catalan n / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      2 * z * Complex.digamma z - z * (Complex.digamma (z + 1 / 2) + Complex.digamma (z - 1 / 2))

/-- Theorem 6 (general identity): for `Re z > 1/2`,
`Σ_{n≥0} ((2n + 1)/2^{2n}) C_n H_{n+z}/C(n + z, n)
  = 2(zH_z - 1)(H_{z-1} - H_{z-3/2}) + 2z(H^{(2)}_{z-1} - H^{(2)}_{z-3/2})`,
with `H_α = ψ(α + 1) + γ` and
`H^{(2)}_{z-1} - H^{(2)}_{z-3/2} = Σ_{j≥0} (1/(j + z - 1/2)² - 1/(j + z)²)`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 6, identity (13)
(`integers-2025-A18-thm-6`). -/
public theorem_wanted tsum_odd_mul_catalan_mul_harmonic_div_four_pow_mul_binom {z : ℂ}
    (hz : 1 / 2 < z.re) :
    ∑' n : ℕ, (2 * (n : ℂ) + 1) * catalan n *
        (Complex.digamma (n + z + 1) + Real.eulerMascheroniConstant) /
        (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      2 * (z * (Complex.digamma (z + 1) + Real.eulerMascheroniConstant) - 1) *
          (Complex.digamma z - Complex.digamma (z - 1 / 2)) +
        2 * z * ∑' j : ℕ, (1 / ((j : ℂ) + z - 1 / 2) ^ 2 - 1 / ((j : ℂ) + z) ^ 2)

/-- Theorem 6 (special values): `Σ_{n≥0} ((2n + 1)/(n + 1)) C_n H_{n+1}/2^{2n} = 2π²/3`,
`Σ_{n≥0} ((2n + 1)/((n + 2)(n + 1))) C_n H_{n+2}/2^{2n} = 2π²/3 + 4 ln 2 - 8`, and
`Σ_{n≥0} O_{n+2}/((n + 1)(2n + 3)) = 4 - 2 ln 2 - π²/6`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 6, particular cases and identity (14)
(`integers-2025-A18-thm-6`). -/
public theorem_wanted tsum_odd_mul_catalan_mul_harmonic_special :
    ∑' n : ℕ, (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * catalan n * (harmonic (n + 1) : ℝ) / 4 ^ n =
        2 * Real.pi ^ 2 / 3 ∧
      ∑' n : ℕ, (2 * (n : ℝ) + 1) / (((n : ℝ) + 2) * ((n : ℝ) + 1)) * catalan n *
          (harmonic (n + 2) : ℝ) / 4 ^ n =
        2 * Real.pi ^ 2 / 3 + 4 * Real.log 2 - 8 ∧
      ∑' n : ℕ, (∑ j ∈ Finset.range (n + 2), 1 / (2 * (j : ℝ) + 1)) /
          (((n : ℝ) + 1) * (2 * n + 3)) =
        4 - 2 * Real.log 2 - Real.pi ^ 2 / 6

/-- Theorem 7 (general identity): for `Re z > 1/2`,
`Σ_{n≥0} (n/2^{2n}) C_n H_{n+z}/C(n + z, n)
  = (zH_z - 1)(2H_{z-1} - H_{z-1/2} - H_{z-3/2})
    + z(2H^{(2)}_{z-1} - H^{(2)}_{z-1/2} - H^{(2)}_{z-3/2})`,
with `H_α = ψ(α + 1) + γ` and
`2H^{(2)}_{z-1} - H^{(2)}_{z-1/2} - H^{(2)}_{z-3/2}
  = Σ_{j≥0} (1/(j + z + 1/2)² + 1/(j + z - 1/2)² - 2/(j + z)²)`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 7, identity (15)
(`integers-2025-A18-thm-7`). -/
public theorem_wanted tsum_nat_mul_catalan_mul_harmonic_div_four_pow_mul_binom {z : ℂ}
    (hz : 1 / 2 < z.re) :
    ∑' n : ℕ, (n : ℂ) * catalan n * (Complex.digamma (n + z + 1) + Real.eulerMascheroniConstant) /
        (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      (z * (Complex.digamma (z + 1) + Real.eulerMascheroniConstant) - 1) *
          (2 * Complex.digamma z - Complex.digamma (z + 1 / 2) - Complex.digamma (z - 1 / 2)) +
        z * ∑' j : ℕ, (1 / ((j : ℂ) + z + 1 / 2) ^ 2 + 1 / ((j : ℂ) + z - 1 / 2) ^ 2 -
          2 / ((j : ℂ) + z) ^ 2)

/-- Theorem 7 (special values, `z = 1` and `z = 3/2`):
`Σ_{n≥1} (n C_n/2^{2n}) H_{n+1}/(n + 1) = 2π²/3 - 4` and
`Σ_{n≥1} n O_{n+2}/((n + 1)(2n + 1)(2n + 3)) = 13/4 - 2 ln 2 - π²/6` (the `n = 0` terms vanish).

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 7, particular cases and identity (16)
(`integers-2025-A18-thm-7`). -/
public theorem_wanted tsum_nat_mul_catalan_mul_harmonic_special :
    ∑' n : ℕ, (n : ℝ) * catalan n / 4 ^ n * (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) =
        2 * Real.pi ^ 2 / 3 - 4 ∧
      ∑' n : ℕ, (n : ℝ) * (∑ j ∈ Finset.range (n + 2), 1 / (2 * (j : ℝ) + 1)) /
          (((n : ℝ) + 1) * (2 * n + 1) * (2 * n + 3)) =
        13 / 4 - 2 * Real.log 2 - Real.pi ^ 2 / 6

/-- Theorem 8 (special values): `Σ_{n≥0} 2^{2n}/(C(2(n + 1), n + 1)(n + 1)²) = π²/8` and
`Σ_{n≥0} 1/((2n + 1)(n + 1)) = 2 ln 2`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 8, identities (17) and (18)
(`integers-2025-A18-thm-8`). -/
public theorem_wanted tsum_four_pow_div_centralBinom_mul_sq_special :
    ∑' n : ℕ, (4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 8 ∧
      ∑' n : ℕ, 1 / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) = 2 * Real.log 2

/-- Theorem 8 (general identity): for `h ∈ ℂ` with `Re h > -1/2` and `h ∉ ℕ`,
`Σ_{n≥0} 2^{2n}/(C(n, h) C(2(n + 1), n + 1)(n + 1)²) = (π/4)(H_{h-1/2} - H_{-1/2})/sin(πh)`, where
`1/C(n, h) = Γ(h + 1)Γ(n - h + 1)/n!` and `H_{h-1/2} - H_{-1/2} = ψ(h + 1/2) - ψ(1/2)`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 8, identity (19)
(`integers-2025-A18-thm-8`). -/
public theorem_wanted tsum_four_pow_div_binom_mul_centralBinom_mul_sq {h : ℂ}
    (hh : ∀ m : ℕ, h ≠ m) (hre : -1 / 2 < h.re) :
    ∑' n : ℕ, (4 : ℂ) ^ n * (Complex.Gamma (h + 1) * Complex.Gamma (n - h + 1) / n.factorial) /
        (((n + 1).centralBinom : ℂ) * ((n : ℂ) + 1) ^ 2) =
      Real.pi / 4 * (Complex.digamma (h + 1 / 2) - Complex.digamma (1 / 2)) /
        Complex.sin (Real.pi * h)

/-- Corollary 2: for `h ∈ ℕ`,
`Σ_{n≥h} C(2(n - h), n - h)/(C(n, h) C(2(n + 1), n + 1)(n + 1)²)
  = (-1)^h (H_h + 2 ln 2)/((h + 1) C(2(h + 1), h + 1))
    - Σ_{n=0}^{h-1} (-1)^{n-h} C(h, n)/(C(2(h - n), h - n) C(2(n + 1), n + 1)(n + 1)²)`,
with the summation index shifted by `h`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Corollary 2, identity (20)
(`integers-2025-A18-cor-2`). -/
public theorem_wanted tsum_centralBinom_div_choose_mul_centralBinom_mul_sq (h : ℕ) :
    ∑' n : ℕ, (n.centralBinom : ℝ) /
        (((n + h).choose h : ℝ) * ((n + h + 1).centralBinom : ℝ) * ((n : ℝ) + h + 1) ^ 2) =
      (-1) ^ h * ((harmonic h : ℝ) + 2 * Real.log 2) /
          (((h : ℝ) + 1) * ((h + 1).centralBinom : ℝ)) -
        ∑ n ∈ Finset.range h, (-1) ^ (h - n) * (h.choose n : ℝ) /
          (((h - n).centralBinom : ℝ) * ((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2)

/-- Theorem 9: for `h ∈ ℕ`,
`Σ_{n≥h} C(2(n - h), n - h) O_{n-h}/(C(n, h) C(2(n + 1), n + 1)(n + 1)²)
  = -(-1)^h (ζ(2) - H^{(2)}_h)/(2(h + 1) C(2(h + 1), h + 1))
    + (-1)^h (H_h + 2 ln 2) O_{h+1}/((h + 1) C(2(h + 1), h + 1))
    - Σ_{n=0}^{h-1} (-1)^{n-h} C(h, n) O_{h-n}/(C(2(h - n), h - n) C(2(n + 1), n + 1)(n + 1)²)`,
with the summation index shifted by `h` and `ζ(2) = π²/6`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 9, identity (22)
(`integers-2025-A18-thm-9`). -/
public theorem_wanted tsum_centralBinom_mul_odd_harmonic_div_choose_mul_centralBinom_mul_sq
    (h : ℕ) :
    ∑' n : ℕ, (n.centralBinom : ℝ) * (∑ j ∈ Finset.range n, 1 / (2 * (j : ℝ) + 1)) /
        (((n + h).choose h : ℝ) * ((n + h + 1).centralBinom : ℝ) * ((n : ℝ) + h + 1) ^ 2) =
      -((-1) ^ h * (Real.pi ^ 2 / 6 - ∑ j ∈ Finset.range h, 1 / ((j : ℝ) + 1) ^ 2) /
          (2 * ((h : ℝ) + 1) * ((h + 1).centralBinom : ℝ))) +
        (-1) ^ h * ((harmonic h : ℝ) + 2 * Real.log 2) /
            (((h : ℝ) + 1) * ((h + 1).centralBinom : ℝ)) *
          ∑ j ∈ Finset.range (h + 1), 1 / (2 * (j : ℝ) + 1) -
        ∑ n ∈ Finset.range h, (-1) ^ (h - n) * (h.choose n : ℝ) /
            (((h - n).centralBinom : ℝ) * ((n + 1).centralBinom : ℝ)) *
          (∑ j ∈ Finset.range (h - n), 1 / (2 * (j : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2

/-- Theorem 10: for a positive integer `m`,
`Σ_{n≥0} 2^{2n}/((n + 1) C(n + m, m) C(2(n + m), n + m))
  = (m/4)(3ζ(2) - 4O^{(2)}_{m-1})/C(2(m - 1), m - 1)`,
with `ζ(2) = π²/6`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 10, identity (23)
(`integers-2025-A18-thm-10`). -/
public theorem_wanted tsum_four_pow_div_succ_mul_choose_mul_centralBinom {m : ℕ} (hm : 0 < m) :
    ∑' n : ℕ, (4 : ℝ) ^ n /
        (((n : ℝ) + 1) * ((n + m).choose m : ℝ) * ((n + m).centralBinom : ℝ)) =
      (m : ℝ) / 4 *
          (3 * (Real.pi ^ 2 / 6) - 4 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1) ^ 2) /
        ((m - 1).centralBinom : ℝ)

/-- Theorem 11: for a positive integer `m`,
`Σ_{n≥0} 2^{2n} O_{n+m}/((n + 1) C(n + m, m) C(2(n + m), n + m))
  = (m/4) C(2(m - 1), m - 1)^{-1} (7ζ(3) - 8O^{(3)}_{m-1} + O_{m-1}(3ζ(2) - 4O^{(2)}_{m-1}))`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 11, identity (27)
(`integers-2025-A18-thm-11`). -/
public theorem_wanted tsum_four_pow_mul_odd_harmonic_div_succ_mul_choose_mul_centralBinom {m : ℕ}
    (hm : 0 < m) :
    ∑' n : ℕ, (4 : ℂ) ^ n * (∑ j ∈ Finset.range (n + m), 1 / (2 * (j : ℂ) + 1)) /
        (((n : ℂ) + 1) * ((n + m).choose m : ℂ) * ((n + m).centralBinom : ℂ)) =
      (m : ℂ) / 4 / ((m - 1).centralBinom : ℂ) *
        (7 * riemannZeta 3 - 8 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℂ) + 1) ^ 3 +
          (∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℂ) + 1)) *
            (3 * riemannZeta 2 - 4 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℂ) + 1) ^ 2))

/-- Theorem 12: for a positive integer `m`,
`Σ_{n≥0} C_n/(C(n + m, n) C(2(n + m), n + m))
  = (m/2)(H_{m-1} - 2O_{m-1} + 2 ln 2)/C(2(m - 1), m - 1)`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 12, identity (28)
(`integers-2025-A18-thm-12`). -/
public theorem_wanted tsum_catalan_div_choose_mul_centralBinom {m : ℕ} (hm : 0 < m) :
    ∑' n : ℕ, (catalan n : ℝ) / (((n + m).choose n : ℝ) * ((n + m).centralBinom : ℝ)) =
      (m : ℝ) / 2 *
          ((harmonic (m - 1) : ℝ) - 2 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1) +
            2 * Real.log 2) /
        ((m - 1).centralBinom : ℝ)

/-- Theorem 13: for a positive integer `m`,
`Σ_{n≥0} C_n O_{n+m}/(C(n + m, m) C(2(n + m), n + m)) = (m/4) C(2(m - 1), m - 1)^{-1}
  (H^{(2)}_{m-1} + 2ζ(2) - 4O^{(2)}_{m-1} + 2O_{m-1}(H_{m-1} - 2O_{m-1} + 2 ln 2))`, with
`ζ(2) = π²/6`.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 13, identity (30)
(`integers-2025-A18-thm-13`). -/
public theorem_wanted tsum_catalan_mul_odd_harmonic_div_choose_mul_centralBinom {m : ℕ}
    (hm : 0 < m) :
    ∑' n : ℕ, (catalan n : ℝ) * (∑ j ∈ Finset.range (n + m), 1 / (2 * (j : ℝ) + 1)) /
        (((n + m).choose m : ℝ) * ((n + m).centralBinom : ℝ)) =
      (m : ℝ) / 4 / ((m - 1).centralBinom : ℝ) *
        (∑ j ∈ Finset.range (m - 1), 1 / ((j : ℝ) + 1) ^ 2 + 2 * (Real.pi ^ 2 / 6) -
          4 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1) ^ 2 +
          2 * (∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1)) *
            ((harmonic (m - 1) : ℝ) - 2 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1) +
              2 * Real.log 2))

end

end MetaMathlibExt
