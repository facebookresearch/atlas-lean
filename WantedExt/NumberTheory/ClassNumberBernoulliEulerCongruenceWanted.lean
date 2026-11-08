/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.Trace.Defs

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry NumberField

/-- Classical congruence for the class number `h(-p)` of the imaginary quadratic field
`ℚ(√-p)`, `p > 3` prime: `h(-p) ≡ -2 B_{(p+1)/2} (mod p)` when `p ≡ 3 (mod 4)`, and
`h(-p) ≡ 2⁻¹ E_{(p-1)/2} (mod p)` when `p ≡ 1 (mod 4)`, where `Bₙ` are the Bernoulli numbers
(`t/(eᵗ - 1)`) and `Eₙ` the Euler numbers (`2/(eᵗ + e⁻ᵗ)`).

The field is any number field `K` of degree `2` containing a square root of `-p`. `Bₙ` is
Mathlib's `bernoulli` (it agrees with `bernoulli'` at the even index `(p+1)/2 ≥ 4`), and
`E_{(p-1)/2}` is `chapter5EulerEven ((p-1)/4)` (`chapter5EulerEven m = E_{2m}`). The first
congruence is stated as `p ∣ num(h + 2 B_{(p+1)/2})`; the denominator of `B_{(p+1)/2}` is
prime to `p` for `p > 3` (von Staudt-Clausen), so this is the congruence in `ℤ_(p)`. The second
is stated as `p ∣ 2h - E_{(p-1)/2}`, equivalent since `p` is odd.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Theorem 1 (`integers-2026-A112-thm-1`), quoting [5]. -/
public theorem_wanted classNumber_sqrt_neg_prime_congr_bernoulli_euler (p : ℕ) (hp : p.Prime)
    (hp3 : 3 < p) (K : Type*) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) (hsqrt : ∃ x : K, x ^ 2 = -(p : K)) :
    (p % 4 = 3 →
      (p : ℤ) ∣ ((NumberField.classNumber K : ℚ) + 2 * bernoulli ((p + 1) / 2)).num) ∧
    (p % 4 = 1 →
      (p : ℤ) ∣ 2 * (NumberField.classNumber K : ℤ) - chapter5EulerEven ((p - 1) / 4))

/-- The real period `ϖ₁ = ∫₀¹ (1 - t³)^(-2/3) dt` of the Eisenstein lattice satisfies
`ϖ₁ = B(1/3, 1/3)/3 = Γ(1/3)³/(2π√3) = 2^(1/3)/(3√3) · B(1/6, 1/2)`.

`B` is Mathlib's `Complex.betaIntegral`; the identities are stated in `ℂ` for that reason.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 1
(`integers-2026-A112-lem-1`). -/
public theorem_wanted eisensteinRealPeriod_eq_beta_gamma :
    let ϖ : ℝ := ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ)
    (ϖ : ℂ) = Complex.betaIntegral (1 / 3) (1 / 3) / 3 ∧
      ϖ = Real.Gamma (1 / 3) ^ 3 / (2 * Real.pi * Real.sqrt 3) ∧
      (ϖ : ℂ) = (((2 : ℝ) ^ (1 / 3 : ℝ) / (3 * Real.sqrt 3) : ℝ) : ℂ) *
        Complex.betaIntegral (1 / 6) (1 / 2)

/-- Elementary properties of the Weierstrass `℘`-function of the lattice `ϖ₁ ℤ[ρ]`, where
`ρ = e^(2πi/3)` and `ϖ₁ = ∫₀¹ (1 - t³)^(-2/3) dt`: (a) `℘(ρu) = ρ℘(u)`, `℘(-u) = ℘(u)`,
`℘'(ρu) = ℘'(u)`, `℘'(-u) = -℘'(u)`; (b) `℘(ū) = conj ℘(u)`, `℘'(ū) = conj ℘'(u)`;
(c) `℘'² = 4℘³ - 27`; (d) `℘(ϖ₁/3) = 3`, `℘((1 - ρ)ϖ₁/3) = 0`; (e) `℘'(ϖ₁/3) = -9`,
`℘'((1 - ρ)ϖ₁/3) = -3√3 i`.

The lattice is any `PeriodPair` with periods `ϖ₁` and `ϖ₁ρ`; `℘` and `℘'` are Mathlib's
`PeriodPair.weierstrassP` and `PeriodPair.derivWeierstrassP`. The functional identities in
(a)-(c) are stated off the lattice, where both functions are meromorphic with poles. The
reality consequence in (b) is omitted (it follows from the conjugation identities).

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 2
(`integers-2026-A112-lem-2`). -/
public theorem_wanted weierstrassP_eisenstein_lattice (L : PeriodPair) (ϖ : ℝ)
    (hϖ : ϖ = ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
    (hω₁ : L.ω₁ = ϖ) (hω₂ : L.ω₂ = ϖ * Complex.exp (2 * Real.pi * Complex.I / 3)) :
    let ρ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
    (∀ u ∉ L.lattice,
      L.weierstrassP (ρ * u) = ρ * L.weierstrassP u ∧ L.weierstrassP (-u) = L.weierstrassP u ∧
      L.derivWeierstrassP (ρ * u) = L.derivWeierstrassP u ∧
      L.derivWeierstrassP (-u) = -L.derivWeierstrassP u ∧
      L.weierstrassP (starRingEnd ℂ u) = starRingEnd ℂ (L.weierstrassP u) ∧
      L.derivWeierstrassP (starRingEnd ℂ u) = starRingEnd ℂ (L.derivWeierstrassP u) ∧
      L.derivWeierstrassP u ^ 2 = 4 * L.weierstrassP u ^ 3 - 27) ∧
    L.weierstrassP (ϖ / 3) = 3 ∧ L.weierstrassP ((1 - ρ) * ϖ / 3) = 0 ∧
    L.derivWeierstrassP (ϖ / 3) = -9 ∧
    L.derivWeierstrassP ((1 - ρ) * ϖ / 3) = -3 * Real.sqrt 3 * Complex.I

/-- Addition formula for the Eisenstein elliptic function `Sl`:
`Sl(u + v) = (Sl(u)² Cl(v) - Sl(v)² Cl(u)) / (Sl(u) Cl(v)² - Sl(v) Cl(u)²)`, and
`Sl(u + v) ∈ Sl(u) + Sl(v) + (Sl(u), Sl(v))⁴ ℤ[1/3][[Sl(u), Sl(v)]]` inside `ℚ[[u, v]]`.

The Taylor series of `Sl` and `Cl` at `0` enter as power series `S C : ℚ⟦X⟧` subject to
`Sl' = Cl²`, `Cl' = -Sl²`, `Sl(0) = 0`, `Cl(0) = 1` (the paper's Lemma 3; these determine both
series uniquely), since the paper's definition of `Sl` through the Weierstrass `ζ`-function has
no Mathlib counterpart. The quotient is
stated cleared of its denominator, and the second claim as a two-variable series `F` with
coefficients in `ℤ[1/3]` and no terms of total degree below `4`. The arXiv version
(arXiv:2204.04425) states the ideal power `2`; the journal statement, followed here, has `4`
(all terms of `Sl(u + v) - Sl(u) - Sl(v)` have total degree `≡ 1 (mod 3)`).

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 4
(`integers-2026-A112-lem-4`). -/
public theorem_wanted sl_add_formula (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : PowerSeries.constantCoeff S = 0) (hC0 : PowerSeries.constantCoeff C = 1) :
    let su : MvPowerSeries (Fin 2) ℚ := S.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℚ)
    let sv : MvPowerSeries (Fin 2) ℚ := S.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℚ)
    let cu : MvPowerSeries (Fin 2) ℚ := C.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℚ)
    let cv : MvPowerSeries (Fin 2) ℚ := C.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℚ)
    let suv : MvPowerSeries (Fin 2) ℚ :=
      S.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℚ)
    suv * (su * cv ^ 2 - sv * cu ^ 2) = su ^ 2 * cv - sv ^ 2 * cu ∧
      ∃ F : MvPowerSeries (Fin 2) ℚ,
        (∀ e, ∃ (a : ℤ) (k : ℕ), MvPowerSeries.coeff e F = a / 3 ^ k) ∧
        (∀ e : Fin 2 →₀ ℕ, e.degree < 4 → MvPowerSeries.coeff e F = 0) ∧
        suv = su + sv + F.subst ![su, sv]

/-- For every integer `r`, `Sl(ru) ∈ r Sl(u) + Sl(u)⁴ ℤ[1/3][[Sl(u)³]]`, and for `r ≠ 0`,
`Sl(ru)⁻¹ ∈ 1/(r Sl(u)) + Sl(u)² ℤ[1/r, 1/3][[Sl(u)³]]`, inside `ℚ[[u]]` (resp. `u⁻¹ℚ[[u]]`).

The Taylor series of `Sl` and `Cl` at `0` enter as power series `S C : ℚ⟦X⟧` subject to
`Sl' = Cl²`, `Cl' = -Sl²`, `Sl(0) = 0`, `Cl(0) = 1` (the paper's Lemma 3; these determine both
series uniquely), since the paper's definition of `Sl` through the Weierstrass `ζ`-function has
no Mathlib counterpart. `Sl(ru)` is
`PowerSeries.rescale r S`. The second claim, `Sl(ru)⁻¹ = 1/(r Sl(u)) + Sl(u)² h(Sl(u)³)`, is
stated multiplied through by `r Sl(u) Sl(ru)`: `r Sl(u) = Sl(ru) + r Sl(u)³ Sl(ru) h(Sl(u)³)`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 5
(`integers-2026-A112-lem-5`). -/
public theorem_wanted sl_rescale_int_expansion (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : PowerSeries.constantCoeff S = 0) (hC0 : PowerSeries.constantCoeff C = 1) (r : ℤ) :
    (∃ g : PowerSeries ℚ, (∀ n, ∃ (a : ℤ) (k : ℕ), PowerSeries.coeff n g = a / 3 ^ k) ∧
      PowerSeries.rescale (r : ℚ) S = (r : ℚ) • S + S ^ 4 * g.subst (S ^ 3)) ∧
    (r ≠ 0 → ∃ h : PowerSeries ℚ,
      (∀ n, ∃ (a : ℤ) (j k : ℕ), PowerSeries.coeff n h = a / ((r : ℚ) ^ j * 3 ^ k)) ∧
      (r : ℚ) • S = PowerSeries.rescale (r : ℚ) S +
        (r : ℚ) • (S ^ 3 * PowerSeries.rescale (r : ℚ) S * h.subst (S ^ 3)))

/-- The inverse of `Sl` near `0` is
`ArcSl(t) = Σ_{n ≥ 0} (-1)ⁿ binom(-2/3, n) t^(3n+1)/(3n+1)`, i.e.
`u = Σ_{n ≥ 0} (-1)ⁿ binom(-2/3, n) Sl(u)^(3n+1)/(3n+1)` in `ℚ[[u]]`.

The Taylor series of `Sl` and `Cl` at `0` enter as power series `S C : ℚ⟦X⟧` subject to
`Sl' = Cl²`, `Cl' = -Sl²`, `Sl(0) = 0`, `Cl(0) = 1` (the paper's Lemma 3; these determine both
series uniquely), since the paper's definition of `Sl` through the Weierstrass `ζ`-function has
no Mathlib counterpart. `binom(-2/3, n)` is
`Ring.choose (-2/3) n`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Corollary 1
(`integers-2026-A112-cor-1`). -/
public theorem_wanted arcSl_subst_sl (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : PowerSeries.constantCoeff S = 0) (hC0 : PowerSeries.constantCoeff C = 1) :
    (PowerSeries.mk fun k => if k % 3 = 1 then
        (-1 : ℚ) ^ (k / 3) * Ring.choose (-2 / 3 : ℚ) (k / 3) / k else 0).subst S =
      PowerSeries.X

/-- The Hurwitz-normalized Taylor coefficients `c_{3m+1} = (3m+1)! C_{3m+1}` of
`Sl(u) = Σ_m C_{3m+1} u^(3m+1)` are integers.

The Taylor series of `Sl` and `Cl` at `0` enter as power series `S C : ℚ⟦X⟧` subject to
`Sl' = Cl²`, `Cl' = -Sl²`, `Sl(0) = 0`, `Cl(0) = 1` (the paper's Lemma 3; these determine both
series uniquely), since the paper's definition of `Sl` through the Weierstrass `ζ`-function has
no Mathlib counterpart.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 7
(`integers-2026-A112-lem-7`). -/
public theorem_wanted factorial_mul_coeff_sl_isInt (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : PowerSeries.constantCoeff S = 0) (hC0 : PowerSeries.constantCoeff C = 1) (m : ℕ) :
    ∃ z : ℤ, ((3 * m + 1).factorial : ℚ) * PowerSeries.coeff (3 * m + 1) S = z

/-- Writing `1/Sl(u) = 1/u + Σ_n D_{3n+2} u^(3n+2)` and `d_n = n! Dₙ`, one has
`2 d_{6m+2} ∈ ℤ[1/3]` for all `m ≥ 0`.

The Taylor series of `Sl` and `Cl` at `0` enter as power series `S C : ℚ⟦X⟧` subject to
`Sl' = Cl²`, `Cl' = -Sl²`, `Sl(0) = 0`, `Cl(0) = 1` (the paper's Lemma 3; these determine both
series uniquely), since the paper's definition of `Sl` through the Weierstrass `ζ`-function has
no Mathlib counterpart. With `Sl(u) = u S₀(u)`,
`D_k` is the coefficient of `u^(k+1)` in `S₀⁻¹`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 8
(`integers-2026-A112-lem-8`). -/
public theorem_wanted two_mul_factorial_coeff_inv_sl_mem_int_inv_three (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : PowerSeries.constantCoeff S = 0) (hC0 : PowerSeries.constantCoeff C = 1) (m : ℕ) :
    ∃ (a : ℤ) (k : ℕ), 2 * ((6 * m + 2).factorial : ℚ) *
      PowerSeries.coeff (6 * m + 3) (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) S)⁻¹ =
        a / 3 ^ k

/-- For a prime `ℓ`, the denominator of the Bernoulli-Hurwitz-type number `C_{2(ℓ-1)/3}` (the
coefficient of `u^(2(ℓ-1)/3)` in `Sl(u)`) is prime to `ℓ` when `ℓ ≡ 7 (mod 9)`, and that of
`D_{2(ℓ-1)/3}` (the coefficient of `u^(2(ℓ-1)/3)` in `1/Sl(u) - 1/u`) is prime to `ℓ` when
`ℓ ≡ 4 (mod 9)`.

The Taylor series of `Sl` and `Cl` at `0` enter as power series `S C : ℚ⟦X⟧` subject to
`Sl' = Cl²`, `Cl' = -Sl²`, `Sl(0) = 0`, `Cl(0) = 1` (the paper's Lemma 3; these determine both
series uniquely), since the paper's definition of `Sl` through the Weierstrass `ζ`-function has
no Mathlib counterpart. With `Sl(u) = u S₀(u)`, `D_k` is the coefficient of `u^(k+1)` in `S₀⁻¹`.
Only the first sentence of the theorem is stated: the congruences `α_λ ≡ -C_{2(ℓ-1)/3}/3`,
`-D_{2(ℓ-1)/3}/3 (mod λ)` involve the elliptic Gauss sum coefficient `α_λ`, built from the
paper's `φ`, and are omitted.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Theorem 3 (`integers-2026-A112-thm-3`), first sentence. -/
public theorem_wanted sl_hurwitz_numbers_den_coprime (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : PowerSeries.constantCoeff S = 0) (hC0 : PowerSeries.constantCoeff C = 1)
    (ℓ : ℕ) (hℓ : ℓ.Prime) :
    (ℓ % 9 = 7 → ¬ ℓ ∣ (PowerSeries.coeff (2 * (ℓ - 1) / 3) S).den) ∧
    (ℓ % 9 = 4 → ¬ ℓ ∣ (PowerSeries.coeff (2 * (ℓ - 1) / 3 + 1)
      (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) S)⁻¹).den)

/-- Properties of the Eisenstein elliptic functions `φ(u) = 6℘(ϖ₁u)/(9 + ℘'(ϖ₁u))` and
`ψ(u) = (-9 + ℘'(ϖ₁u))/(9 + ℘'(ϖ₁u))`, where `℘` is the Weierstrass function of the lattice
`ϖ₁ ℤ[ρ]`, `ρ = e^(2πi/3)` and `ϖ₁ = ∫₀¹ (1 - t³)^(-2/3) dt`: (d) `φ(ρu) = ρφ(u)`,
`ψ(ρu) = ψ(u)`, `φ(ū) = conj φ(u)`, `ψ(ū) = conj ψ(u)`; (e) `φ' = -3ϖ₁ψ²`, `ψ' = 3ϖ₁φ²`;
(f) `φ³ + ψ³ = 1`, `φ(0) = 0`, `ψ(0) = 1`; (g) `φ(-u) = -φ(u)/ψ(u)`, `ψ(-u) = ψ(u)⁻¹` and
`φ(u)⁻¹ + φ(-u)⁻¹ = 3℘(ϖ₁u)⁻¹`.

`φ` is the paper's introductory definition through `℘` and `ψ` its formula from part (c); the
paper's Definition 1 through the Weierstrass `ζ`-function, and parts (a), (b), (h), which
concern `ζ` and the function `Z` built from it, are omitted (`ζ` is not in Mathlib). The
lattice is any `PeriodPair` with periods `ϖ₁` and `ϖ₁ρ`. The identities are stated off the
poles (`ϖ₁u` off the lattice, the denominators nonzero), and `φ(0) = 0`, `ψ(0) = 1` as limits
at `0`, where `℘` has its pole.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 3 (`integers-2026-A112-lem-3`), parts (d)-(g). -/
public theorem_wanted eisensteinPhiPsi_properties (L : PeriodPair) (ϖ : ℝ)
    (hϖ : ϖ = ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
    (hω₁ : L.ω₁ = ϖ) (hω₂ : L.ω₂ = ϖ * Complex.exp (2 * Real.pi * Complex.I / 3)) :
    let ρ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
    let φ : ℂ → ℂ := fun u => 6 * L.weierstrassP (ϖ * u) / (9 + L.derivWeierstrassP (ϖ * u))
    let ψ : ℂ → ℂ := fun u =>
      (-9 + L.derivWeierstrassP (ϖ * u)) / (9 + L.derivWeierstrassP (ϖ * u))
    (∀ u : ℂ, (ϖ : ℂ) * u ∉ L.lattice → 9 + L.derivWeierstrassP (ϖ * u) ≠ 0 →
      φ (ρ * u) = ρ * φ u ∧ ψ (ρ * u) = ψ u ∧
      φ (starRingEnd ℂ u) = starRingEnd ℂ (φ u) ∧ ψ (starRingEnd ℂ u) = starRingEnd ℂ (ψ u) ∧
      HasDerivAt φ (-3 * ϖ * ψ u ^ 2) u ∧ HasDerivAt ψ (3 * ϖ * φ u ^ 2) u ∧
      φ u ^ 3 + ψ u ^ 3 = 1) ∧
    Filter.Tendsto φ (nhdsWithin 0 {0}ᶜ) (nhds 0) ∧
    Filter.Tendsto ψ (nhdsWithin 0 {0}ᶜ) (nhds 1) ∧
    (∀ u : ℂ, (ϖ : ℂ) * u ∉ L.lattice → 81 - L.derivWeierstrassP (ϖ * u) ^ 2 ≠ 0 →
      φ (-u) = -φ u / ψ u ∧ ψ (-u) = (ψ u)⁻¹ ∧
      (L.weierstrassP (ϖ * u) ≠ 0 → (φ u)⁻¹ + (φ (-u))⁻¹ = 3 / L.weierstrassP (ϖ * u)))

/-- On the real segment, `Sl : [0, ϖ₁] → [0, 1]` is the inverse of
`ArcSl : [0, 1] → [0, ϖ₁]`, `ArcSl(t) = ∫₀ᵗ (1 - s³)^(-2/3) ds
= Σ_{n ≥ 0} (-1)ⁿ binom(-2/3, n) t^(3n+1)/(3n+1)`, where `ϖ₁ = ArcSl(1)`,
`Sl(u) = φ(u/(-3ϖ₁))` and `φ(u) = 6℘(ϖ₁u)/(9 + ℘'(ϖ₁u))` for the Weierstrass `℘` of the
lattice `ϖ₁ ℤ[ρ]`, `ρ = e^(2πi/3)`.

`Sl` is the paper's introductory definition through `℘` (complex-valued; the statement
includes that it is real on `[0, ϖ₁]`). The lattice is any `PeriodPair` with periods `ϖ₁`
and `ϖ₁ρ`, and `binom(-2/3, n)` is `Ring.choose (-2/3 : ℚ) n`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 6 (`integers-2026-A112-lem-6`). -/
public theorem_wanted eisensteinSl_inverse_arcSl (L : PeriodPair) (ϖ : ℝ)
    (hϖ : ϖ = ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
    (hω₁ : L.ω₁ = ϖ) (hω₂ : L.ω₂ = ϖ * Complex.exp (2 * Real.pi * Complex.I / 3)) :
    let arcSl : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, (1 - s ^ 3) ^ (-(2 / 3) : ℝ)
    let sl : ℝ → ℂ := fun x =>
      6 * L.weierstrassP (ϖ * (x / (-3 * ϖ))) / (9 + L.derivWeierstrassP (ϖ * (x / (-3 * ϖ))))
    (∀ t ∈ Set.Icc (0 : ℝ) 1, HasSum (fun n : ℕ =>
      (-1) ^ n * (Ring.choose (-2 / 3 : ℚ) n : ℝ) * t ^ (3 * n + 1) / (3 * n + 1)) (arcSl t)) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) ϖ, ∃ s ∈ Set.Icc (0 : ℝ) 1, sl x = s ∧ arcSl s = x) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, arcSl t ∈ Set.Icc (0 : ℝ) ϖ ∧ sl (arcSl t) = t)

/-- Jacobi sums of the quadratic and the cubic residue character: for a primary prime
`μ ∈ ℤ[ρ]` (`μ ≡ 1 (mod 3)`) of prime norm `p`, the quadratic character `ϕ` of `𝔽_p` and the
cubic residue character `χ` modulo `μ` (`χ(t) ≡ t^((p-1)/3) (mod μ)`) satisfy
`J(ϕ, χ) = χ(4) J(χ, χ) = -χ(4) μ`, where `J(ϕ, χ) = Σ_{t ∈ 𝔽_p} ϕ(t) χ(1 - t)`.

The paper's setting (i) says "any characters `ϕ` and `χ` of `𝔽_p^×`"; the identity holds for
the quadratic `ϕ` and the cubic residue character `χ` modulo `μ`, the characters of the lemma
it cites (Ireland-Rosen, Chap. 18, §3 and Chap. 9, §4) and of its use in Lemma 14 (d); this
reading is stated. `ℤ[ρ]` is the ring of integers of a cyclotomic field `K = ℚ(ζ₃)`, `χ` takes
values in it, and `J` is Mathlib's `jacobiSum`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 13 (`integers-2026-A112-lem-13`), part (a). -/
public theorem_wanted jacobiSum_quadraticChar_cubicResidueChar (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {3} ℚ K] (μ : 𝓞 K) (hμ : (3 : 𝓞 K) ∣ μ - 1)
    (p : ℕ) [Fact p.Prime] (hN : Algebra.norm ℤ μ = p) (χ : MulChar (ZMod p) (𝓞 K))
    (hχ : ∀ t : ℤ, μ ∣ (t : 𝓞 K) ^ ((p - 1) / 3) - χ t) :
    let ϕ : MulChar (ZMod p) (𝓞 K) := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom _)
    jacobiSum ϕ χ = χ 4 * jacobiSum χ χ ∧ jacobiSum χ χ = -μ

/-- For an odd prime `q ≡ 2 (mod 3)`, the quadratic character `ϕ` and a cubic character `χ` of
`𝔽_{q²}` satisfy `J₂(ϕ, χ) = Σ_{t ∈ 𝔽_{q²}} ϕ(t) χ(1 - t) = q`.

The paper's setting (ii) says "any characters `ϕ` and `χ` of `𝔽_{q²}^×`"; the identity holds
for the quadratic `ϕ` and a character `χ` of order `3` (the cubic residue character modulo
`-q` or its conjugate, which give the same value since it is real), as in the sources it
cites; this reading is stated. `q = 2` is excluded since `𝔽₄^×` has no quadratic character.
`𝔽_{q²}` is any finite field `F` with `q²` elements, characters are complex-valued, and `J₂`
is Mathlib's `jacobiSum`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 13 (`integers-2026-A112-lem-13`), part (b). -/
public theorem_wanted jacobiSum_quadraticChar_cubicChar_card_sq (q : ℕ) (hqp : q.Prime)
    (hq : q % 3 = 2) (hq2 : q ≠ 2) (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = q ^ 2) (χ : MulChar F ℂ) (hχ3 : χ ^ 3 = 1) (hχ1 : χ ≠ 1) :
    jacobiSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) χ = q

/-- Cubic reciprocity in `ℤ[ρ]`: for primary primes `λ₁, λ₂` (`λᵢ ≡ 1 (mod 3)`), the cubic
residue symbols agree, `(λ₁/λ₂)₃ = (λ₂/λ₁)₃`.

`ℤ[ρ]` is the ring of integers of a cyclotomic field `K = ℚ(ζ₃)` with a primitive cube root
of unity `ζ`. The symbol `(a/π)₃` is the cube root of unity `ω ∈ {1, ζ, ζ²}` with
`a^((N π - 1)/3) ≡ ω (mod π)`; the statement says that any such `ω₁` for `(λ₁/λ₂)₃` and
`ω₂` for `(λ₂/λ₁)₃` coincide (when `λ₁ = λ₂` both symbols are `0` and no such `ω`
exists). `λᵢ` is written `lamᵢ`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 13 (`integers-2026-A112-lem-13`), part (c). -/
public theorem_wanted cubicResidueSymbol_reciprocity (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] (ζ : 𝓞 K) (hζ : IsPrimitiveRoot ζ 3) (lam₁ lam₂ : 𝓞 K)
    (h₁ : Prime lam₁) (h₂ : Prime lam₂) (hp₁ : (3 : 𝓞 K) ∣ lam₁ - 1)
    (hp₂ : (3 : 𝓞 K) ∣ lam₂ - 1)
    (ω₁ ω₂ : 𝓞 K) (hω₁ : ω₁ ∈ ({1, ζ, ζ ^ 2} : Set (𝓞 K)))
    (hω₂ : ω₂ ∈ ({1, ζ, ζ ^ 2} : Set (𝓞 K)))
    (h₁₂ : lam₂ ∣ lam₁ ^ (((Algebra.norm ℤ lam₂).natAbs - 1) / 3) - ω₁)
    (h₂₁ : lam₁ ∣ lam₂ ^ (((Algebra.norm ℤ lam₁).natAbs - 1) / 3) - ω₂) :
    ω₁ = ω₂

/-- Point counts of the reductions of `E_λ : y² = x³ + λ²/4`, in its global minimal form
`y² + λy = x³`, for a primary prime `λ ∈ ℤ[ρ]` (`λ ≡ 1 (mod 3)`) of prime norm `ℓ`, with
`χ_λ(a) = (a/λ)₃ ∈ {1, ζ, ζ²}`, `a^((ℓ-1)/3) ≡ χ_λ(a) (mod λ)`: (d) for a primary `μ ≠ λ` of
prime norm `p`, `#E_λ(𝔽_p) = p + 1 - (χ_λ(μ) μ̄ + conj(χ_λ(μ) μ̄))`; (e) for a prime
`q ≡ 2 (mod 3)`, `#E_λ(𝔽_{q²}) = q² + 1 + q (χ_λ(q) + conj χ_λ(q))`.

`ℤ[ρ]` is the ring of integers of a cyclotomic field `K = ℚ(ζ₃)` with a primitive cube root
of unity `ζ`; `𝔽_p` and `𝔽_{q²}` are the residue rings `ℤ[ρ]/(μ)` and `ℤ[ρ]/(q)`. Point counts
are affine solutions of `y² + λy = x³` plus the point at infinity. Since `z + z̄` is the trace
of `z` and `χ̄ = χ²` for a cube root of unity, `χ_λ(μ) μ̄ + conj(χ_λ(μ) μ̄) = Tr(χ_λ(μ)² μ)`
and `χ_λ(q) + conj χ_λ(q) = Tr(χ_λ(q))`. Parts (a)-(c) (bad reduction, Kodaira types and
Tamagawa numbers of Néron models) and (f) are not part of this declaration ((f) is
`eisensteinTwist_torsion`).

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 14 (`integers-2026-A112-lem-14`), parts (d), (e). -/
public theorem_wanted eisensteinTwist_card_points (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] (ζ : 𝓞 K) (hζ : IsPrimitiveRoot ζ 3) (lam : 𝓞 K)
    (hlam : (3 : 𝓞 K) ∣ lam - 1) (ℓ : ℕ) (hℓ : ℓ.Prime) (hN : Algebra.norm ℤ lam = ℓ) :
    (∀ (μ : 𝓞 K) (p : ℕ), (3 : 𝓞 K) ∣ μ - 1 → p.Prime → Algebra.norm ℤ μ = p → μ ≠ lam →
      ∀ ω ∈ ({1, ζ, ζ ^ 2} : Set (𝓞 K)), lam ∣ μ ^ ((ℓ - 1) / 3) - ω →
        (Nat.card {xy : (𝓞 K ⧸ Ideal.span {μ}) × (𝓞 K ⧸ Ideal.span {μ}) //
          xy.2 ^ 2 + Ideal.Quotient.mk _ lam * xy.2 = xy.1 ^ 3} : ℤ) + 1 =
          p + 1 - Algebra.trace ℤ (𝓞 K) (ω ^ 2 * μ)) ∧
    (∀ q : ℕ, q.Prime → q % 3 = 2 →
      ∀ ω ∈ ({1, ζ, ζ ^ 2} : Set (𝓞 K)), lam ∣ (q : 𝓞 K) ^ ((ℓ - 1) / 3) - ω →
        (Nat.card {xy : (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) × (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) //
          xy.2 ^ 2 + Ideal.Quotient.mk _ lam * xy.2 = xy.1 ^ 3} : ℤ) + 1 =
          q ^ 2 + 1 + q * Algebra.trace ℤ (𝓞 K) ω)

/-- The torsion of `E_λ : y² = x³ + λ²/4` over `ℚ(ρ)`, for a primary prime `λ ∈ ℤ[ρ]`
(`λ ≡ 1 (mod 3)`) of prime norm: `E_λ(ℚ(ρ))_tors = E_λ(ℚ(ρ))[3] = {∞, (0, ±λ/2)}`, so
`#E_λ(ℚ(ρ))_tors = 3`.

`ℚ(ρ)` is a cyclotomic field `K = ℚ(ζ₃)` and `ℤ[ρ]` its ring of integers; points are Mathlib's
`WeierstrassCurve.Affine.Point`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 14 (`integers-2026-A112-lem-14`), part (f). -/
public theorem_wanted eisensteinTwist_torsion (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] [DecidableEq K] (lam : 𝓞 K) (hlam : (3 : 𝓞 K) ∣ lam - 1) (ℓ : ℕ)
    (hℓ : ℓ.Prime) (hN : Algebra.norm ℤ lam = ℓ) :
    let W : WeierstrassCurve K := ⟨0, 0, 0, 0, (lam : K) ^ 2 / 4⟩
    (∀ P : W.toAffine.Point, IsOfFinAddOrder P ↔ 3 • P = 0) ∧
    (∀ P : W.toAffine.Point, 3 • P = 0 ↔ P = 0 ∨
      (∃ h, P = .some 0 ((lam : K) / 2) h) ∨ ∃ h, P = .some 0 (-(lam : K) / 2) h) ∧
    Nat.card {P : W.toAffine.Point // IsOfFinAddOrder P} = 3

/-- Congruence for the square of `λ̃ = ∏_{χ_λ(r) = 1} φ(r/λ)`: `λ̃² ≡ Λ^(2(ℓ-1)/3)` modulo
`Λ^(2(ℓ-1)/3 + 1)` in `O_λ`, where `Λ = φ(1/λ)` and `O_λ` is the ring of integers of `ℚ(ρ, Λ)`.

Setting: `ℓ` prime, `λ = a + bρ ∈ ℤ[ρ]` with `a ≡ 1`, `b ≡ 0 (mod 3)` and `λλ̄ = ℓ`;
`φ(u) = 6℘(ϖ₁u)/(9 + ℘'(ϖ₁u))` (the paper's introductory definition through `℘`, for the lattice
`ϖ₁ ℤ[ρ]`, any `PeriodPair` with periods `ϖ₁`, `ϖ₁ρ`); `χ_λ` the cubic residue character modulo
`λ`, given on `ℤ[ρ]/(λ) ≅ ℤ/ℓ` (`ρ ↦ r₀`) by `χ_λ(t) = ρᵏ` when `t^((ℓ-1)/3) = r₀ᵏ`. The classes
of `(ℤ[ρ]/(λ))ˣ` are represented by `r = 1, …, ℓ-1`. `O_λ` is the set of algebraic integers in
the subfield `ℚ(ρ, Λ)` of `ℂ`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 10 (`integers-2026-A112-lem-10`). -/
public theorem_wanted eisensteinLambdaTilde_sq_congr (L : PeriodPair) (ϖ : ℝ)
    (hϖ : ϖ = ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
    (hω₁ : L.ω₁ = ϖ) (hω₂ : L.ω₂ = ϖ * Complex.exp (2 * Real.pi * Complex.I / 3))
    (a b : ℤ) (ha : a % 3 = 1) (hb : b % 3 = 0) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hN : (ℓ : ℤ) = a ^ 2 - a * b + b ^ 2) (r₀ : ZMod ℓ) (hr₀ : (a : ZMod ℓ) + b * r₀ = 0)
    (χ : ZMod ℓ → ℂ) (hχ : ∀ t : ZMod ℓ, t ≠ 0 → ∃ k : ℕ,
      χ t = Complex.exp (2 * Real.pi * Complex.I / 3) ^ k ∧ t ^ ((ℓ - 1) / 3) = r₀ ^ k) :
    let ρ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
    let lam : ℂ := a + b * ρ
    let φ : ℂ → ℂ := fun u => 6 * L.weierstrassP (ϖ * u) / (9 + L.derivWeierstrassP (ϖ * u))
    let Λ : ℂ := φ (1 / lam)
    let lamTilde : ℂ :=
      ∏ r ∈ (Finset.Ioo 0 ℓ).filter (fun r : ℕ => χ (r : ZMod ℓ) = 1), φ ((r : ℂ) / lam)
    ∃ x : ℂ, IsIntegral ℤ x ∧ x ∈ IntermediateField.adjoin ℚ ({ρ, Λ} : Set ℂ) ∧
      lamTilde ^ 2 - Λ ^ (2 * (ℓ - 1) / 3) = Λ ^ (2 * (ℓ - 1) / 3 + 1) * x

/-- The elliptic Gauss sum `G_λ(χ_λ, f) = (1/3) Σ_{r ∈ (ℤ[ρ]/(λ))ˣ} χ_λ(r) f(r/λ)`, with
`f = φ` for `ℓ ≡ 7 (mod 9)` and `f = φ⁻¹` for `ℓ ≡ 4 (mod 9)`, (a) lies in `O_λ`, and
(b) equals `Σ_{r ∈ ker χ_λ} f(r/λ)`.

Setting as in `eisensteinLambdaTilde_sq_congr`: `λ = a + bρ` primary of prime norm `ℓ`,
`φ(u) = 6℘(ϖ₁u)/(9 + ℘'(ϖ₁u))`, `χ_λ` given on `ℤ[ρ]/(λ) ≅ ℤ/ℓ` (`ρ ↦ r₀`), classes
represented by `r = 1, …, ℓ-1`, and `O_λ` the algebraic integers in `ℚ(ρ, Λ)`, `Λ = φ(1/λ)`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 11 (`integers-2026-A112-lem-11`). -/
public theorem_wanted ellipticGaussSum_mem_integers_eq_sum_ker (L : PeriodPair) (ϖ : ℝ)
    (hϖ : ϖ = ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
    (hω₁ : L.ω₁ = ϖ) (hω₂ : L.ω₂ = ϖ * Complex.exp (2 * Real.pi * Complex.I / 3))
    (a b : ℤ) (ha : a % 3 = 1) (hb : b % 3 = 0) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hN : (ℓ : ℤ) = a ^ 2 - a * b + b ^ 2) (h9 : ℓ % 9 = 7 ∨ ℓ % 9 = 4) (r₀ : ZMod ℓ)
    (hr₀ : (a : ZMod ℓ) + b * r₀ = 0) (χ : ZMod ℓ → ℂ) (hχ : ∀ t : ZMod ℓ, t ≠ 0 → ∃ k : ℕ,
      χ t = Complex.exp (2 * Real.pi * Complex.I / 3) ^ k ∧ t ^ ((ℓ - 1) / 3) = r₀ ^ k) :
    let ρ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
    let lam : ℂ := a + b * ρ
    let φ : ℂ → ℂ := fun u => 6 * L.weierstrassP (ϖ * u) / (9 + L.derivWeierstrassP (ϖ * u))
    let f : ℂ → ℂ := fun u => if ℓ % 9 = 7 then φ u else (φ u)⁻¹
    let G : ℂ := (1 / 3) * ∑ r ∈ Finset.Ioo 0 ℓ, χ (r : ZMod ℓ) * f ((r : ℂ) / lam)
    (IsIntegral ℤ G ∧ G ∈ IntermediateField.adjoin ℚ ({ρ, φ (1 / lam)} : Set ℂ)) ∧
      G = ∑ r ∈ (Finset.Ioo 0 ℓ).filter (fun r : ℕ => χ (r : ZMod ℓ) = 1), f ((r : ℂ) / lam)

/-- Congruences for `|α_λ|²`, where `α_λ = G_λ(χ_λ, f)/λ̃²` is the coefficient of the elliptic
Gauss sum: modulo `λ`, `|α_λ|² ≡ (conj χ_λ(3) C_{2(ℓ-1)/3})²/9` if `ℓ ≡ 7 (mod 9)` and
`≡ (χ_λ(3) D_{2(ℓ-1)/3})²/9` if `ℓ ≡ 4 (mod 9)`; modulo `ℓ`,
`|α_λ|² ≡ (3^((ℓ-7)/6) C_{2(ℓ-1)/3})²`, resp. `(3^((ℓ-4)/3) D_{2(ℓ-1)/3})²`.

Setting as in `eisensteinLambdaTilde_sq_congr` and `ellipticGaussSum_mem_integers_eq_sum_ker`
(`f = φ` for `ℓ ≡ 7`, `f = φ⁻¹` for `ℓ ≡ 4 (mod 9)`, `λ̃ = ∏_{χ_λ(r) = 1} φ(r/λ)`; the paper's
introductory definition of `α_λ`). `C_n` and `D_n` are the Taylor coefficients at `0` of
`Sl(u) = φ(u/(-3ϖ₁))` and of `Sl(u)⁻¹ - u⁻¹`, written `iteratedDeriv n _ 0 / n!` (both
functions take their limit value `0` at `0`). A congruence `x ≡ y` between numbers whose
denominators are prime to `ℓ` is stated as `m (x - y) ∈ λ ℤ[ρ]`, resp. `ℓ ℤ`, for an integer `m`
prime to `ℓ`.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 12 (`integers-2026-A112-lem-12`). -/
public theorem_wanted ellipticGaussSum_coeff_normSq_congr (L : PeriodPair) (ϖ : ℝ)
    (hϖ : ϖ = ∫ t in (0 : ℝ)..1, (1 - t ^ 3) ^ (-(2 / 3) : ℝ))
    (hω₁ : L.ω₁ = ϖ) (hω₂ : L.ω₂ = ϖ * Complex.exp (2 * Real.pi * Complex.I / 3))
    (a b : ℤ) (ha : a % 3 = 1) (hb : b % 3 = 0) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hN : (ℓ : ℤ) = a ^ 2 - a * b + b ^ 2) (r₀ : ZMod ℓ) (hr₀ : (a : ZMod ℓ) + b * r₀ = 0)
    (χ : ZMod ℓ → ℂ) (hχ : ∀ t : ZMod ℓ, t ≠ 0 → ∃ k : ℕ,
      χ t = Complex.exp (2 * Real.pi * Complex.I / 3) ^ k ∧ t ^ ((ℓ - 1) / 3) = r₀ ^ k) :
    let ρ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
    let lam : ℂ := a + b * ρ
    let φ : ℂ → ℂ := fun u => 6 * L.weierstrassP (ϖ * u) / (9 + L.derivWeierstrassP (ϖ * u))
    let f : ℂ → ℂ := fun u => if ℓ % 9 = 7 then φ u else (φ u)⁻¹
    let G : ℂ := (1 / 3) * ∑ r ∈ Finset.Ioo 0 ℓ, χ (r : ZMod ℓ) * f ((r : ℂ) / lam)
    let lamTilde : ℂ :=
      ∏ r ∈ (Finset.Ioo 0 ℓ).filter (fun r : ℕ => χ (r : ZMod ℓ) = 1), φ ((r : ℂ) / lam)
    let α : ℂ := G / lamTilde ^ 2
    let sl : ℂ → ℂ := fun u => φ (u / (-3 * ϖ))
    let k : ℕ := 2 * (ℓ - 1) / 3
    let C : ℂ := iteratedDeriv k sl 0 / k.factorial
    let D : ℂ := iteratedDeriv k (fun u => (sl u)⁻¹ - u⁻¹) 0 / k.factorial
    (ℓ % 9 = 7 →
      (∃ m c d : ℤ, ¬ (ℓ : ℤ) ∣ m ∧
        m * ((Complex.normSq α : ℂ) - (starRingEnd ℂ (χ 3) * C) ^ 2 / 9) = lam * (c + d * ρ)) ∧
      ∃ m c : ℤ, ¬ (ℓ : ℤ) ∣ m ∧
        m * ((Complex.normSq α : ℂ) - (3 ^ ((ℓ - 7) / 6) * C) ^ 2) = ℓ * c) ∧
    (ℓ % 9 = 4 →
      (∃ m c d : ℤ, ¬ (ℓ : ℤ) ∣ m ∧
        m * ((Complex.normSq α : ℂ) - (χ 3 * D) ^ 2 / 9) = lam * (c + d * ρ)) ∧
      ∃ m c : ℤ, ¬ (ℓ : ℤ) ∣ m ∧
        m * ((Complex.normSq α : ℂ) - (3 ^ ((ℓ - 4) / 3) * D) ^ 2) = ℓ * c)

end

end MetaMathlibExt
