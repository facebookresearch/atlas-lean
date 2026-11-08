/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

namespace MetaMathlibExt

@[expose] public section

open MetaMathlibExt.QPochhammer

/-! Notation of the source, on the open unit disk `‖q‖ < 1`: `(a; q)_∞` is
`qPochhammerInfRaw a q`, `(a, b, …; q)_∞` is the product of the single symbols, and the
Lambert series `∑_{n ≥ 1}` are written as `∑' n : ℕ` over the shifted index `n + 1`. All
sums and products converge on the disk, where the raw product equals the canonical
`qPochhammerInf`. -/

/-- Lambert series attached to Ramanujan's continued fraction of order sixteen: for `‖q‖ < 1`,
`∑_{n ≥ 1} n (qⁿ - q⁷ⁿ - q⁹ⁿ + q¹⁵ⁿ)/(1 - q¹⁶ⁿ)
  = q (q¹⁶; q¹⁶)²_∞ (q⁸; q⁸)²_∞ (q⁶, q¹⁰; q¹⁶)_∞ / (q, q⁷, q⁹, q¹⁵; q¹⁶)²_∞` (62) and
`∑_{n ≥ 1} n (q³ⁿ - q⁵ⁿ - q¹¹ⁿ + q¹³ⁿ)/(1 - q¹⁶ⁿ)
  = q³ (q¹⁶; q¹⁶)²_∞ (q⁸; q⁸)²_∞ (q², q¹⁴; q¹⁶)_∞ / (q³, q⁵, q¹¹, q¹³; q¹⁶)²_∞` (63).
The source's hypothesis `|q| < 1` is `‖q‖ < 1`.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Theorem 3, Equations (62)-(63) (`integers-2025-A16-thm-3`). -/
public theorem_wanted lambert_order_sixteen_weight_n (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, ((n : ℂ) + 1) *
        (q ^ (n + 1) - q ^ (7 * (n + 1)) - q ^ (9 * (n + 1)) + q ^ (15 * (n + 1))) /
          (1 - q ^ (16 * (n + 1)))) =
      q * qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2 * qPochhammerInfRaw (q ^ 8) (q ^ 8) ^ 2 *
          (qPochhammerInfRaw (q ^ 6) (q ^ 16) * qPochhammerInfRaw (q ^ 10) (q ^ 16)) /
        (qPochhammerInfRaw q (q ^ 16) * qPochhammerInfRaw (q ^ 7) (q ^ 16) *
            qPochhammerInfRaw (q ^ 9) (q ^ 16) * qPochhammerInfRaw (q ^ 15) (q ^ 16)) ^ 2 ∧
    (∑' n : ℕ, ((n : ℂ) + 1) *
        (q ^ (3 * (n + 1)) - q ^ (5 * (n + 1)) - q ^ (11 * (n + 1)) + q ^ (13 * (n + 1))) /
          (1 - q ^ (16 * (n + 1)))) =
      q ^ 3 * qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2 * qPochhammerInfRaw (q ^ 8) (q ^ 8) ^ 2 *
          (qPochhammerInfRaw (q ^ 2) (q ^ 16) * qPochhammerInfRaw (q ^ 14) (q ^ 16)) /
        (qPochhammerInfRaw (q ^ 3) (q ^ 16) * qPochhammerInfRaw (q ^ 5) (q ^ 16) *
            qPochhammerInfRaw (q ^ 11) (q ^ 16) * qPochhammerInfRaw (q ^ 13) (q ^ 16)) ^ 2

/-- Lambert series twisted by the Legendre symbol `(n/3)`: for `‖q‖ < 1`,
`∑_{n ≥ 1} (n/3) (qⁿ - q⁷ⁿ - q⁹ⁿ + q¹⁵ⁿ)/(1 - q¹⁶ⁿ)
  = q (q⁸; q⁸)²_∞ (q⁴⁸; q⁴⁸)_∞ (q⁶, q¹⁰; q¹⁶)_∞ (q, q⁷, q⁹, q¹⁵; q¹⁶)_∞
    / ((q¹⁶; q¹⁶)_∞ (q³, q²¹, q²⁷, q⁴⁵; q⁴⁸)_∞)` (64) and
`∑_{n ≥ 1} (n/3) (q³ⁿ - q⁵ⁿ - q¹¹ⁿ + q¹³ⁿ)/(1 - q¹⁶ⁿ)
  = q³ (q⁸; q⁸)²_∞ (q⁴⁸; q⁴⁸)_∞ (q², q¹⁴; q¹⁶)_∞ (q³, q⁵, q¹¹, q¹³; q¹⁶)_∞
    / ((q¹⁶; q¹⁶)_∞ (q⁹, q¹⁵, q³³, q³⁹; q⁴⁸)_∞)` (65).
The source's `(n/3)` is the Legendre symbol modulo `3`, here `jacobiSym n 3` (equal to the
Legendre symbol since `3` is prime); the source's `|q| < 1` is `‖q‖ < 1`.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Theorem 4, Equations (64)-(65) (`integers-2025-A16-thm-4`). -/
public theorem_wanted lambert_order_sixteen_legendre_three (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (jacobiSym ((n : ℤ) + 1) 3 : ℂ) *
        (q ^ (n + 1) - q ^ (7 * (n + 1)) - q ^ (9 * (n + 1)) + q ^ (15 * (n + 1))) /
          (1 - q ^ (16 * (n + 1)))) =
      q * qPochhammerInfRaw (q ^ 8) (q ^ 8) ^ 2 * qPochhammerInfRaw (q ^ 48) (q ^ 48) *
          (qPochhammerInfRaw (q ^ 6) (q ^ 16) * qPochhammerInfRaw (q ^ 10) (q ^ 16)) *
          (qPochhammerInfRaw q (q ^ 16) * qPochhammerInfRaw (q ^ 7) (q ^ 16) *
            qPochhammerInfRaw (q ^ 9) (q ^ 16) * qPochhammerInfRaw (q ^ 15) (q ^ 16)) /
        (qPochhammerInfRaw (q ^ 16) (q ^ 16) *
          (qPochhammerInfRaw (q ^ 3) (q ^ 48) * qPochhammerInfRaw (q ^ 21) (q ^ 48) *
            qPochhammerInfRaw (q ^ 27) (q ^ 48) * qPochhammerInfRaw (q ^ 45) (q ^ 48))) ∧
    (∑' n : ℕ, (jacobiSym ((n : ℤ) + 1) 3 : ℂ) *
        (q ^ (3 * (n + 1)) - q ^ (5 * (n + 1)) - q ^ (11 * (n + 1)) + q ^ (13 * (n + 1))) /
          (1 - q ^ (16 * (n + 1)))) =
      q ^ 3 * qPochhammerInfRaw (q ^ 8) (q ^ 8) ^ 2 * qPochhammerInfRaw (q ^ 48) (q ^ 48) *
          (qPochhammerInfRaw (q ^ 2) (q ^ 16) * qPochhammerInfRaw (q ^ 14) (q ^ 16)) *
          (qPochhammerInfRaw (q ^ 3) (q ^ 16) * qPochhammerInfRaw (q ^ 5) (q ^ 16) *
            qPochhammerInfRaw (q ^ 11) (q ^ 16) * qPochhammerInfRaw (q ^ 13) (q ^ 16)) /
        (qPochhammerInfRaw (q ^ 16) (q ^ 16) *
          (qPochhammerInfRaw (q ^ 9) (q ^ 48) * qPochhammerInfRaw (q ^ 15) (q ^ 48) *
            qPochhammerInfRaw (q ^ 33) (q ^ 48) * qPochhammerInfRaw (q ^ 39) (q ^ 48)))

/-- Product forms of Ramanujan's theta functions (Lemma 1): for `‖q‖ < 1`, with
`f_k = (q^k; q^k)_∞`, `ψ(q) = f₂² / f₁`, `f(q) = f₂³ / (f₁ f₄)`, `χ(q) = f₂² / (f₁ f₄)` and
`χ(-q) = f₁ / f₂`. The functions are the standard ones of Ramanujan's notebooks (Berndt, Part III,
Chapter 16): `ψ(q) = f(q, q³)`, `f(q) = f(q, -q²)` (so `f(-q) = f₁`) and `χ(q) = (-q; q²)_∞`, with
`f(a, b)` Ramanujan's general theta function `ramanujanThetaRaw a b`.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Lemma 1 (`integers-2025-A16-lem-1`). -/
public theorem_wanted ramanujan_psi_f_chi_eq_qPochhammer (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 3) =
        qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 2 / qPochhammerInfRaw q q ∧
      ramanujanThetaRaw q (-q ^ 2) =
        qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 3 /
          (qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 4) (q ^ 4)) ∧
      qPochhammerInfRaw (-q) (q ^ 2) =
        qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 2 /
          (qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 4) (q ^ 4)) ∧
      qPochhammerInfRaw q (q ^ 2) = qPochhammerInfRaw q q / qPochhammerInfRaw (q ^ 2) (q ^ 2)

/-- Ramanujan's Entry 30 (i)-(iii) for the general theta function `f(a, b)`, quoted in the record
of Lemma 1: for complex `a, b` with `‖a b‖ < 1`, `f(a, ab²) f(b, a²b) = f(a, b) ψ(ab)` (8),
`f(a, b) + f(-a, -b) = 2 f(a³b, ab³)` (9) and, for `a ≠ 0`,
`f(a, b) - f(-a, -b) = 2a f(b/a, a⁵b³)` (10), where `f(a, b) = ramanujanThetaRaw a b` and
`ψ(q) = f(q, q³)`.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Lemma 1 record, quoting Berndt, Part III, Entry 30 (i)-(iii)
(`integers-2025-A16-lem-1`). -/
public theorem_wanted ramanujanTheta_entry30 (a b : ℂ) (hab : ‖a * b‖ < 1) :
    ramanujanThetaRaw a (a * b ^ 2) * ramanujanThetaRaw b (a ^ 2 * b) =
        ramanujanThetaRaw a b * ramanujanThetaRaw (a * b) ((a * b) ^ 3) ∧
      ramanujanThetaRaw a b + ramanujanThetaRaw (-a) (-b) =
        2 * ramanujanThetaRaw (a ^ 3 * b) (a * b ^ 3) ∧
      (a ≠ 0 → ramanujanThetaRaw a b - ramanujanThetaRaw (-a) (-b) =
        2 * a * ramanujanThetaRaw (b / a) (a ^ 5 * b ^ 3))


/-- Ramanujan's continued fractions of order sixteen in the Lambert series of Theorem 2: for
`‖q‖ < 1`,
`∑_{n odd} (q³ⁿ + q⁵ⁿ)/(1 - q¹⁶ⁿ) - ∑_{n odd} (q¹¹ⁿ + q¹³ⁿ)/(1 - q¹⁶ⁿ)
  = η⁴(32τ)/η²(16τ) · (I₁(q²) + 1/I₁(q²))` (54) and
`∑_{n odd} (qⁿ + q⁷ⁿ)/(1 - q¹⁶ⁿ) - ∑_{n odd} (q⁹ⁿ + q¹⁵ⁿ)/(1 - q¹⁶ⁿ)
  = η⁴(32τ)/η²(16τ) · (I₂(q²) + 1/I₂(q²))` (55),
where `I₁(q) = q^{1/2} (q³, q¹³; q¹⁶)_∞ / (q⁵, q¹¹; q¹⁶)_∞` (1) and
`I₂(q) = q^{3/2} (q, q¹⁵; q¹⁶)_∞ / (q⁷, q⁹; q¹⁶)_∞` (2), so that
`I₁(q²) = q (q⁶, q²⁶; q³²)_∞ / (q¹⁰, q²²; q³²)_∞` and `I₂(q²) = q³ (q², q³⁰; q³²)_∞ / (q¹⁴, q¹⁸; q³²)_∞`,
and, with `q = e^{2πiτ}` and `η(τ) = q^{1/24} (q; q)_∞`,
`η⁴(32τ)/η²(16τ) = q⁴ (q³²; q³²)⁴_∞ / (q¹⁶; q¹⁶)²_∞`. The odd `n` are `2k + 1`. At `q = 0` both
sides are `0`.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Theorem 2, Equations (54)-(55) (`integers-2025-A16-thm-2`). -/
public theorem_wanted lambert_odd_order_sixteen_eq_continuedFraction (q : ℂ) (hq : ‖q‖ < 1) :
    let E : ℂ := q ^ 4 * qPochhammerInfRaw (q ^ 32) (q ^ 32) ^ 4 /
      qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2
    let I₁ : ℂ := q * (qPochhammerInfRaw (q ^ 6) (q ^ 32) * qPochhammerInfRaw (q ^ 26) (q ^ 32)) /
      (qPochhammerInfRaw (q ^ 10) (q ^ 32) * qPochhammerInfRaw (q ^ 22) (q ^ 32))
    let I₂ : ℂ := q ^ 3 *
      (qPochhammerInfRaw (q ^ 2) (q ^ 32) * qPochhammerInfRaw (q ^ 30) (q ^ 32)) /
      (qPochhammerInfRaw (q ^ 14) (q ^ 32) * qPochhammerInfRaw (q ^ 18) (q ^ 32))
    (∑' k : ℕ, (q ^ (3 * (2 * k + 1)) + q ^ (5 * (2 * k + 1))) / (1 - q ^ (16 * (2 * k + 1))) -
        ∑' k : ℕ, (q ^ (11 * (2 * k + 1)) + q ^ (13 * (2 * k + 1))) /
          (1 - q ^ (16 * (2 * k + 1)))) = E * (I₁ + 1 / I₁) ∧
    (∑' k : ℕ, (q ^ (2 * k + 1) + q ^ (7 * (2 * k + 1))) / (1 - q ^ (16 * (2 * k + 1))) -
        ∑' k : ℕ, (q ^ (9 * (2 * k + 1)) + q ^ (15 * (2 * k + 1))) /
          (1 - q ^ (16 * (2 * k + 1)))) = E * (I₂ + 1 / I₂)

/-- The Jacobi theta function `θ₁(z | τ) = 2 ∑_{n ≥ 0} (-1)ⁿ q^{(2n+1)²/8} sin((2n+1) z)` with
`q^{(2n+1)²/8} = exp(πiτ (2n+1)²/4)`, i.e. `q = e^{2πiτ}` (Equation (11)).

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Section 3, Equation (11).

This raw version is Mathlib's total `tsum`; it is `0` when the series diverges (for example at
`τ = 0`, `z = π/2`). Use `jacobiThetaOneSine`, which requires `0 < Im τ`, unless that fallback is
intended. -/
noncomputable def jacobiThetaOneSineRaw (z τ : ℂ) : ℂ :=
  2 * ∑' n : ℕ, (-1) ^ n * Complex.exp (Real.pi * Complex.I * τ * (2 * n + 1) ^ 2 / 4) *
    Complex.sin ((2 * n + 1) * z)

/-- The Jacobi theta function `θ₁(z | τ)` of Equation (11), restricted to the upper half-plane
`0 < Im τ`, where its series converges for every `z`.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Section 3, Equation (11). -/
noncomputable def jacobiThetaOneSine (z τ : ℂ) (_hτ : 0 < τ.im) : ℂ :=
  jacobiThetaOneSineRaw z τ

/-- `θ₁(0 | τ) = 0`.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Section 3, Equation (11). -/
theorem jacobiThetaOneSine_zero (τ : ℂ) (hτ : 0 < τ.im) : jacobiThetaOneSine 0 τ hτ = 0 := by
  simp [jacobiThetaOneSine, jacobiThetaOneSineRaw]

/-- `θ₁(z | τ)` is odd in `z`.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Section 3, Equation (11). -/
theorem jacobiThetaOneSine_neg (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneSine (-z) τ hτ = -jacobiThetaOneSine z τ hτ := by
  simp [jacobiThetaOneSine, jacobiThetaOneSineRaw, Complex.sin_neg, tsum_neg]

/-- Lemma 2 of Section 5 (the record's Lemma 2): for `Im τ > 0`, `q = e^{2πiτ}` and
`|Im z| < π Im τ` (where the series converges and the denominators do not vanish),
`∑_{n ≥ 1} (qⁿ - q⁷ⁿ - q⁹ⁿ + q¹⁵ⁿ)/(1 - q¹⁶ⁿ) sin 2nz
  = -θ₁'(0|16τ) θ₁(8πτ|16τ) θ₁(6πτ|16τ) θ₁(2z|16τ)
    / (4 θ₁(z+πτ|16τ) θ₁(z-πτ|16τ) θ₁(z+7πτ|16τ) θ₁(z-7πτ|16τ))` (59) and
`∑_{n ≥ 1} (q³ⁿ - q⁵ⁿ - q¹¹ⁿ + q¹³ⁿ)/(1 - q¹⁶ⁿ) sin 2nz
  = -θ₁'(0|16τ) θ₁(2πτ|16τ) θ₁(8πτ|16τ) θ₁(2z|16τ)
    / (4 θ₁(z+3πτ|16τ) θ₁(z-3πτ|16τ) θ₁(z+5πτ|16τ) θ₁(z-5πτ|16τ))` (60),
with `θ₁` the paper's series as the convergence-gated `jacobiThetaOneSine` (`Im (16τ) > 0`)
and `θ₁'` its `z`-derivative.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Lemma 2 of Section 5, Equations (59)-(60) (`integers-2025-A16-lem-2`). -/
public theorem_wanted lambert_order_sixteen_sine_eq_jacobiThetaOne (τ z : ℂ) (hτ : 0 < τ.im)
    (hz : |z.im| < Real.pi * τ.im) :
    let q : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ)
    let θ : ℂ → ℂ := fun w => jacobiThetaOneSine w (16 * τ) (by simp [hτ])
    let πτ : ℂ := Real.pi * τ
    (∑' n : ℕ, (q ^ (n + 1) - q ^ (7 * (n + 1)) - q ^ (9 * (n + 1)) + q ^ (15 * (n + 1))) /
        (1 - q ^ (16 * (n + 1))) * Complex.sin (2 * ((n : ℂ) + 1) * z)) =
      -(deriv θ 0 * θ (8 * πτ) * θ (6 * πτ) * θ (2 * z)) /
        (4 * θ (z + πτ) * θ (z - πτ) * θ (z + 7 * πτ) * θ (z - 7 * πτ)) ∧
    (∑' n : ℕ, (q ^ (3 * (n + 1)) - q ^ (5 * (n + 1)) - q ^ (11 * (n + 1)) +
          q ^ (13 * (n + 1))) / (1 - q ^ (16 * (n + 1))) * Complex.sin (2 * ((n : ℂ) + 1) * z)) =
      -(deriv θ 0 * θ (2 * πτ) * θ (8 * πτ) * θ (2 * z)) /
        (4 * θ (z + 3 * πτ) * θ (z - 3 * πτ) * θ (z + 5 * πτ) * θ (z - 5 * πτ))

end

end MetaMathlibExt
