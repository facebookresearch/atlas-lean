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

/-- **Class number congruences for $\mathbb{Q}(\sqrt{-p})$.** Let $p > 3$ be a prime and let $K$
be a number field of degree $2$ over $\mathbb{Q}$ that contains a square root of $-p$, with class
number $h$. Let $B_n$ be the Bernoulli numbers, $t/(e^t - 1) = \sum_n B_n t^n/n!$, and $E_n$ the
Euler numbers, $2/(e^t + e^{-t}) = \sum_n E_n t^n/n!$ (so $E_2 = -1$). If $p \equiv 3 \pmod 4$,
then $p$ divides the numerator, in lowest terms, of the rational number $h + 2B_{(p+1)/2}$. If
$p \equiv 1 \pmod 4$, then $p$ divides the integer $2h - E_{(p-1)/2}$.

Since the denominator of $B_{(p+1)/2}$ is prime to $p$ for $p > 3$ (von Staudt–Clausen) and $p$
is odd, these are the congruences $h \equiv -2B_{(p+1)/2} \pmod p$ and
$h \equiv E_{(p-1)/2}/2 \pmod p$.

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

/-- **Beta and Gamma values of the real Eisenstein period.** The real number
$\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$ satisfies
$\varpi_1 = \frac13 B(\frac13, \frac13) = \frac{\Gamma(1/3)^3}{2\pi\sqrt3}
= \frac{2^{1/3}}{3\sqrt3} B(\frac16, \frac12)$, where $B$ is the Beta function.

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

/-- **The Weierstrass function of the Eisenstein lattice.** Let $\rho = e^{2\pi i/3}$, let
$\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, and let $\wp$ be the Weierstrass function of the
lattice $\Lambda = \varpi_1 \mathbb{Z} + \varpi_1 \rho \mathbb{Z}$, with derivative $\wp'$. Then for
every $u \in \mathbb{C} \setminus \Lambda$:
(a) $\wp(\rho u) = \rho\,\wp(u)$, $\wp(-u) = \wp(u)$, $\wp'(\rho u) = \wp'(u)$ and
$\wp'(-u) = -\wp'(u)$;
(b) $\wp(\bar u) = \overline{\wp(u)}$ and $\wp'(\bar u) = \overline{\wp'(u)}$;
(c) $\wp'(u)^2 = 4\wp(u)^3 - 27$.
Moreover, (d) $\wp(\varpi_1/3) = 3$ and $\wp((1 - \rho)\varpi_1/3) = 0$, and
(e) $\wp'(\varpi_1/3) = -9$ and $\wp'((1 - \rho)\varpi_1/3) = -3\sqrt{3}\,i$.

By (b), $\wp$ and $\wp'$ take real values at real points off $\Lambda$.

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

/-- **Addition formula for the Eisenstein function Sl.** Let $\mathrm{Sl}, \mathrm{Cl}$ be formal
power series in $\mathbb{Q}[[u]]$ with $\mathrm{Sl}' = \mathrm{Cl}^2$,
$\mathrm{Cl}' = -\mathrm{Sl}^2$, $\mathrm{Sl}(0) = 0$ and $\mathrm{Cl}(0) = 1$. In the ring
$\mathbb{Q}[[u, v]]$ of formal power series in two variables,
$$\mathrm{Sl}(u + v)\bigl(\mathrm{Sl}(u)\,\mathrm{Cl}(v)^2 - \mathrm{Sl}(v)\,\mathrm{Cl}(u)^2\bigr)
= \mathrm{Sl}(u)^2\,\mathrm{Cl}(v) - \mathrm{Sl}(v)^2\,\mathrm{Cl}(u),$$
and there is a power series $F \in \mathbb{Q}[[x, y]]$, with every coefficient in $\mathbb{Z}[1/3]$
and no terms of total degree below $4$, such that
$\mathrm{Sl}(u + v) = \mathrm{Sl}(u) + \mathrm{Sl}(v) + F(\mathrm{Sl}(u), \mathrm{Sl}(v))$.

The four conditions determine $\mathrm{Sl}$ and $\mathrm{Cl}$ uniquely: they are the Taylor series
at $0$ of the Eisenstein elliptic functions of the source. The first identity is the addition
formula $\mathrm{Sl}(u + v) = \frac{\mathrm{Sl}(u)^2 \mathrm{Cl}(v) - \mathrm{Sl}(v)^2
\mathrm{Cl}(u)}{\mathrm{Sl}(u) \mathrm{Cl}(v)^2 - \mathrm{Sl}(v) \mathrm{Cl}(u)^2}$ with its
denominator cleared. The arXiv version of the source (arXiv:2204.04425) has the exponent $2$ in
place of $4$; every term of $\mathrm{Sl}(u + v) - \mathrm{Sl}(u) - \mathrm{Sl}(v)$ has total
degree $\equiv 1 \pmod 3$.

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

/-- **Sl(ru) as a power series in Sl(u).** Let $\mathrm{Sl}, \mathrm{Cl}$ be formal power series
in $\mathbb{Q}[[u]]$ with $\mathrm{Sl}' = \mathrm{Cl}^2$, $\mathrm{Cl}' = -\mathrm{Sl}^2$,
$\mathrm{Sl}(0) = 0$ and $\mathrm{Cl}(0) = 1$, and let $r$ be an integer. Then there is a power
series $g \in \mathbb{Q}[[x]]$, with every coefficient in $\mathbb{Z}[1/3]$, such that
$\mathrm{Sl}(ru) = r\,\mathrm{Sl}(u) + \mathrm{Sl}(u)^4\,g(\mathrm{Sl}(u)^3)$. If moreover
$r \ne 0$, there is a power series $h \in \mathbb{Q}[[x]]$, each coefficient of which has the form
$a/(r^j 3^k)$ with $a \in \mathbb{Z}$ and $j, k \ge 0$, such that
$r\,\mathrm{Sl}(u) = \mathrm{Sl}(ru) + r\,\mathrm{Sl}(u)^3\,\mathrm{Sl}(ru)\,h(\mathrm{Sl}(u)^3)$.

Dividing by $r\,\mathrm{Sl}(u)\,\mathrm{Sl}(ru)$, the second identity reads
$\mathrm{Sl}(ru)^{-1} = (r\,\mathrm{Sl}(u))^{-1} + \mathrm{Sl}(u)^2\,h(\mathrm{Sl}(u)^3)$ in the
Laurent series in $u$. The four conditions determine $\mathrm{Sl}$ and $\mathrm{Cl}$ uniquely:
they are the Taylor series at $0$ of the Eisenstein elliptic functions of the source.

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

/-- **Power series inverse of $\mathrm{Sl}$.** Let $S, C \in \mathbb{Q}[[u]]$ be formal power
series with $S' = C^2$, $C' = -S^2$, $S(0) = 0$ and $C(0) = 1$. Then
$$\sum_{n \ge 0} (-1)^n \binom{-2/3}{n} \frac{S^{3n+1}}{3n+1} = u$$
in $\mathbb{Q}[[u]]$, where $\binom{-2/3}{n} = \frac{1}{n!} \prod_{j=0}^{n-1} (-2/3 - j)$ is the
generalized binomial coefficient.

These conditions determine $S$ and $C$ uniquely: they are the Taylor series at $0$ of the
Eisenstein elliptic functions $\mathrm{Sl}$ and $\mathrm{Cl}$. The statement says that
$\mathrm{ArcSl}(t) = \sum_{n \ge 0} (-1)^n \binom{-2/3}{n} t^{3n+1}/(3n+1)$ is the inverse of
$\mathrm{Sl}$ near $0$.

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

/-- **The Hurwitz-normalized coefficients of Sl are integers.** Let $\mathrm{Sl}, \mathrm{Cl}$ be
formal power series in $\mathbb{Q}[[u]]$ with $\mathrm{Sl}' = \mathrm{Cl}^2$,
$\mathrm{Cl}' = -\mathrm{Sl}^2$, $\mathrm{Sl}(0) = 0$ and $\mathrm{Cl}(0) = 1$, and let $C_n$ be
the coefficient of $u^n$ in $\mathrm{Sl}$. Then $(3m + 1)!\,C_{3m+1}$ is an integer for every
$m \ge 0$.

The four conditions determine $\mathrm{Sl}$ and $\mathrm{Cl}$ uniquely: they are the Taylor series
at $0$ of the Eisenstein elliptic functions of the source.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 7
(`integers-2026-A112-lem-7`). -/
public theorem_wanted factorial_mul_coeff_sl_isInt (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : PowerSeries.constantCoeff S = 0) (hC0 : PowerSeries.constantCoeff C = 1) (m : ℕ) :
    ∃ z : ℤ, ((3 * m + 1).factorial : ℚ) * PowerSeries.coeff (3 * m + 1) S = z

/-- **The Hurwitz-normalized coefficients of 1/Sl.** Let $\mathrm{Sl}, \mathrm{Cl}$ be formal power
series in $\mathbb{Q}[[u]]$ with $\mathrm{Sl}' = \mathrm{Cl}^2$, $\mathrm{Cl}' = -\mathrm{Sl}^2$,
$\mathrm{Sl}(0) = 0$ and $\mathrm{Cl}(0) = 1$. Write $\mathrm{Sl}(u) = u\,S_0(u)$ with
$S_0 \in \mathbb{Q}[[u]]$, and let $D_n$ be the coefficient of $u^{n+1}$ in $S_0^{-1}$, so that
$1/\mathrm{Sl}(u) = 1/u + \sum_{n \ge 0} D_n u^n$. Then for every $m \ge 0$ the number
$2\,(6m + 2)!\,D_{6m+2}$ lies in $\mathbb{Z}[1/3]$, that is, it equals $a/3^k$ for some
$a \in \mathbb{Z}$ and $k \ge 0$.

The four conditions determine $\mathrm{Sl}$ and $\mathrm{Cl}$ uniquely: they are the Taylor series
at $0$ of the Eisenstein elliptic functions of the source.

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

/-- **Denominators of the Hurwitz-type numbers of Sl.** Let $\mathrm{Sl}, \mathrm{Cl}$ be formal
power series in $\mathbb{Q}[[u]]$ with $\mathrm{Sl}' = \mathrm{Cl}^2$,
$\mathrm{Cl}' = -\mathrm{Sl}^2$, $\mathrm{Sl}(0) = 0$ and $\mathrm{Cl}(0) = 1$. Let $C_n$ be the
coefficient of $u^n$ in $\mathrm{Sl}$; write $\mathrm{Sl}(u) = u\,S_0(u)$ with
$S_0 \in \mathbb{Q}[[u]]$ and let $D_n$ be the coefficient of $u^{n+1}$ in $S_0^{-1}$, so that
$1/\mathrm{Sl}(u) = 1/u + \sum_{n \ge 0} D_n u^n$. Let $\ell$ be a prime and put
$k = 2(\ell - 1)/3$. If $\ell \equiv 7 \pmod 9$, then $\ell$ does not divide the denominator of
$C_k$ in lowest terms; if $\ell \equiv 4 \pmod 9$, then $\ell$ does not divide the denominator of
$D_k$ in lowest terms.

The four conditions determine $\mathrm{Sl}$ and $\mathrm{Cl}$ uniquely: they are the Taylor series
at $0$ of the Eisenstein elliptic functions of the source.

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

/-- **Identities for the Eisenstein elliptic functions $\varphi$ and $\psi$.** Let
$\rho = e^{2\pi i/3}$, let $\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, and let $\wp$ be the
Weierstrass function of the lattice spanned by $\varpi_1$ and $\varpi_1\rho$. Put
$\varphi(u) = 6\wp(\varpi_1 u)/(9 + \wp'(\varpi_1 u))$ and
$\psi(u) = (\wp'(\varpi_1 u) - 9)/(\wp'(\varpi_1 u) + 9)$. For every $u \in \mathbb{C}$ with
$\varpi_1 u$ off the lattice and $\wp'(\varpi_1 u) \ne -9$: $\varphi(\rho u) = \rho\varphi(u)$,
$\psi(\rho u) = \psi(u)$, $\varphi(\bar u) = \overline{\varphi(u)}$,
$\psi(\bar u) = \overline{\psi(u)}$, the functions $\varphi$ and $\psi$ are complex differentiable
at $u$ with $\varphi'(u) = -3\varpi_1 \psi(u)^2$ and $\psi'(u) = 3\varpi_1 \varphi(u)^2$, and
$\varphi(u)^3 + \psi(u)^3 = 1$. As $u \to 0$ with $u \ne 0$, $\varphi(u) \to 0$ and
$\psi(u) \to 1$. For every $u$ with $\varpi_1 u$ off the lattice and $\wp'(\varpi_1 u)^2 \ne 81$:
$\varphi(-u) = -\varphi(u)/\psi(u)$ and $\psi(-u) = \psi(u)^{-1}$, and if moreover
$\wp(\varpi_1 u) \ne 0$, then $\varphi(u)^{-1} + \varphi(-u)^{-1} = 3/\wp(\varpi_1 u)$.

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

/-- **$\mathrm{Sl}$ and $\mathrm{ArcSl}$ are inverse on the real segment.** Let
$\rho = e^{2\pi i/3}$, let $\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, let $\wp$ be the
Weierstrass function of the lattice spanned by $\varpi_1$ and $\varpi_1\rho$, and put
$\varphi(u) = 6\wp(\varpi_1 u)/(9 + \wp'(\varpi_1 u))$. For real $x$ put
$\mathrm{Sl}(x) = \varphi(x/(-3\varpi_1))$, and for real $t$ put
$\mathrm{ArcSl}(t) = \int_0^t (1 - s^3)^{-2/3}\,ds$, so that $\varpi_1 = \mathrm{ArcSl}(1)$. Then:
for every $t \in [0, 1]$ the series $\sum_{n \ge 0} (-1)^n \binom{-2/3}{n} t^{3n+1}/(3n+1)$ has
sum $\mathrm{ArcSl}(t)$, where $\binom{-2/3}{n}$ is the generalized binomial coefficient; for
every $x \in [0, \varpi_1]$, $\mathrm{Sl}(x)$ is a real number $s \in [0, 1]$ with
$\mathrm{ArcSl}(s) = x$; and for every $t \in [0, 1]$, $\mathrm{ArcSl}(t) \in [0, \varpi_1]$ and
$\mathrm{Sl}(\mathrm{ArcSl}(t)) = t$.

At $x = 0$, where $\wp$ has a pole, the values $\wp(0)$ and $\wp'(0)$ are taken to be $0$, so
$\mathrm{Sl}(0) = 0$.

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

/-- **Jacobi sums of the quadratic and the cubic residue character.** Let $K$ be a number field
generated over $\mathbb{Q}$ by a primitive cube root of unity, with ring of integers
$\mathcal{O}_K$. Let $\mu \in \mathcal{O}_K$ with $\mu \equiv 1 \pmod 3$, and let $p$ be a prime
such that the norm of $\mu$ from $\mathcal{O}_K$ to $\mathbb{Z}$ is $p$. Let
$\chi : \mathbb{Z}/p\mathbb{Z} \to \mathcal{O}_K$ be a multiplicative character with
$\chi(t) \equiv t^{(p-1)/3} \pmod{\mu}$ for every integer $t$ (the cubic residue character modulo
$\mu$), and let $\phi$ be the quadratic character of $\mathbb{Z}/p\mathbb{Z}$, with values in
$\{0, \pm 1\} \subset \mathcal{O}_K$. Writing
$J(\alpha, \beta) = \sum_{t \in \mathbb{Z}/p\mathbb{Z}} \alpha(t)\,\beta(1 - t)$, one has
$J(\phi, \chi) = \chi(4)\,J(\chi, \chi)$ and $J(\chi, \chi) = -\mu$.

The source states this for arbitrary characters $\phi$ and $\chi$ of $\mathbb{F}_p^\times$; the
identity holds for the quadratic $\phi$ and the cubic residue character $\chi$ modulo $\mu$, the
characters of the lemma it cites (Ireland-Rosen, Chap. 18, §3 and Chap. 9, §4).

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 13 (`integers-2026-A112-lem-13`), part (a). -/
public theorem_wanted jacobiSum_quadraticChar_cubicResidueChar (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {3} ℚ K] (μ : 𝓞 K) (hμ : (3 : 𝓞 K) ∣ μ - 1)
    (p : ℕ) [Fact p.Prime] (hN : Algebra.norm ℤ μ = p) (χ : MulChar (ZMod p) (𝓞 K))
    (hχ : ∀ t : ℤ, μ ∣ (t : 𝓞 K) ^ ((p - 1) / 3) - χ t) :
    let ϕ : MulChar (ZMod p) (𝓞 K) := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom _)
    jacobiSum ϕ χ = χ 4 * jacobiSum χ χ ∧ jacobiSum χ χ = -μ

/-- **The Jacobi sum of the quadratic and a cubic character of a field with $q^2$ elements.** Let
$q$ be an odd prime with $q \equiv 2 \pmod 3$, let $F$ be a finite field with $q^2$ elements, let
$\phi$ be the quadratic character of $F$, and let $\chi : F \to \mathbb{C}$ be a multiplicative
character of order $3$, that is, $\chi^3 = 1$ and $\chi \ne 1$ (characters take the value $0$ at
$0$). Then the Jacobi sum $J(\phi, \chi) = \sum_{t \in F} \phi(t)\,\chi(1 - t)$ equals $q$.

The source states this for arbitrary characters $\phi$ and $\chi$ of $F^\times$; the identity
holds for the quadratic $\phi$ and a $\chi$ of order $3$, the characters of the sources it cites.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Lemma 13 (`integers-2026-A112-lem-13`), part (b). -/
public theorem_wanted jacobiSum_quadraticChar_cubicChar_card_sq (q : ℕ) (hqp : q.Prime)
    (hq : q % 3 = 2) (hq2 : q ≠ 2) (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = q ^ 2) (χ : MulChar F ℂ) (hχ3 : χ ^ 3 = 1) (hχ1 : χ ≠ 1) :
    jacobiSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) χ = q

/-- **Cubic reciprocity.** Let $K$ be the cyclotomic field generated by a primitive cube root of
unity, with ring of integers $\mathcal{O}_K$, and let $\zeta \in \mathcal{O}_K$ be a primitive cube
root of unity. Let $\lambda_1, \lambda_2 \in \mathcal{O}_K$ be primes with
$\lambda_1 \equiv \lambda_2 \equiv 1 \pmod 3$, and write $N$ for the absolute value of the norm
from $\mathcal{O}_K$ to $\mathbb{Z}$. If $\omega_1, \omega_2 \in \{1, \zeta, \zeta^2\}$ satisfy
$\lambda_1^{(N\lambda_2 - 1)/3} \equiv \omega_1 \pmod{\lambda_2}$ and
$\lambda_2^{(N\lambda_1 - 1)/3} \equiv \omega_2 \pmod{\lambda_1}$, then $\omega_1 = \omega_2$.

Here $\mathcal{O}_K = \mathbb{Z}[\zeta]$ and $N\lambda_i \equiv 1 \pmod 3$, so the exponents are
integers. In terms of cubic residue symbols the statement is
$(\lambda_1/\lambda_2)_3 = (\lambda_2/\lambda_1)_3$; when $\lambda_1 = \lambda_2$ no such
$\omega_1$ exists and the statement is empty.

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

/-- **Point counts of $y^2 + \lambda y = x^3$ modulo primes of $\mathbb{Z}[\zeta_3]$.** Let $K$
be the cyclotomic field generated by a primitive cube root of unity, with ring of integers
$\mathcal{O}_K$, let $\zeta \in \mathcal{O}_K$ be a primitive cube root of unity, and write $N$
and $\mathrm{Tr}$ for the norm and trace from $\mathcal{O}_K$ to $\mathbb{Z}$. Let
$\lambda \in \mathcal{O}_K$ satisfy $\lambda \equiv 1 \pmod 3$ with $N\lambda = \ell$ a prime. For
a principal ideal $I$ of $\mathcal{O}_K$, let $n(I)$ be the number of pairs
$(x, y) \in (\mathcal{O}_K/I)^2$ with $y^2 + \lambda y = x^3$. Then:
(d) if $\mu \in \mathcal{O}_K$ with $\mu \ne \lambda$ and $\mu \equiv 1 \pmod 3$ has prime norm
$N\mu = p$, and $\omega \in \{1, \zeta, \zeta^2\}$ satisfies
$\mu^{(\ell-1)/3} \equiv \omega \pmod \lambda$, then
$n((\mu)) + 1 = p + 1 - \mathrm{Tr}(\omega^2\mu)$;
(e) if $q$ is a prime with $q \equiv 2 \pmod 3$, and $\omega \in \{1, \zeta, \zeta^2\}$ satisfies
$q^{(\ell-1)/3} \equiv \omega \pmod \lambda$, then $n((q)) + 1 = q^2 + 1 + q\,\mathrm{Tr}(\omega)$.

The curve $y^2 + \lambda y = x^3$ is a global minimal model of
$E_\lambda : y^2 = x^3 + \lambda^2/4$, and $\mathcal{O}_K/(\mu) \cong \mathbb{F}_p$,
$\mathcal{O}_K/(q) \cong \mathbb{F}_{q^2}$, so $n + 1$ counts the points of $E_\lambda$ over these
fields, including the point at infinity. With $\chi_\lambda(a) = \omega$ the cubic residue symbol
$(a/\lambda)_3$, the right-hand sides are
$p + 1 - (\chi_\lambda(\mu)\bar\mu + \overline{\chi_\lambda(\mu)\bar\mu})$ and
$q^2 + 1 + q(\chi_\lambda(q) + \overline{\chi_\lambda(q)})$.

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

/-- **Torsion of $y^2 = x^3 + \lambda^2/4$ over $\mathbb{Q}(\zeta_3)$.** Let $K$ be the cyclotomic
field generated by a primitive cube root of unity, with ring of integers $\mathcal{O}_K$, and let
$\lambda \in \mathcal{O}_K$ satisfy $\lambda \equiv 1 \pmod 3$, with norm from $\mathcal{O}_K$ to
$\mathbb{Z}$ a prime number. Let $E$ be the Weierstrass curve $y^2 = x^3 + \lambda^2/4$ over $K$,
with point at infinity $O$. Then a point $P \in E(K)$ has finite order if and only if $3P = O$;
$3P = O$ if and only if $P$ is $O$, $(0, \lambda/2)$ or $(0, -\lambda/2)$; and $E(K)$ has exactly
$3$ points of finite order.

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

/-- **Congruence for the square of $\tilde\lambda$.** Let $\rho = e^{2\pi i/3}$, let
$\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, let $\wp$ be the Weierstrass function of the lattice
spanned by $\varpi_1$ and $\varpi_1\rho$, and put
$\varphi(u) = 6\wp(\varpi_1 u)/(9 + \wp'(\varpi_1 u))$. Let $a, b$ be integers with $a \equiv 1$ and
$b \equiv 0 \pmod 3$ such that $\ell = a^2 - ab + b^2$ is prime, and put $\lambda = a + b\rho$.
Let $r_0 \in \mathbb{Z}/\ell$ satisfy $a + b r_0 = 0$, and let
$\chi : \mathbb{Z}/\ell \to \mathbb{C}$ be such that for every $t \ne 0$ there is
$j \in \mathbb{N}$ with $\chi(t) = \rho^j$ and $t^{(\ell-1)/3} = r_0^j$. Put
$\Lambda = \varphi(1/\lambda)$ and $\tilde\lambda = \prod \varphi(r/\lambda)$, the product
over the integers $0 < r < \ell$ with $\chi(r) = 1$. Then
$\tilde\lambda^2 - \Lambda^{2(\ell-1)/3} = \Lambda^{2(\ell-1)/3 + 1} x$ for some algebraic
integer $x$ in the subfield $\mathbb{Q}(\rho, \Lambda)$ of $\mathbb{C}$.

Here $\lambda\bar\lambda = \ell$, $\rho \mapsto r_0$ identifies $\mathbb{Z}[\rho]/(\lambda)$ with
$\mathbb{Z}/\ell$, and $\chi$ is the cubic residue character modulo $\lambda$. The statement is
the congruence $\tilde\lambda^2 \equiv \Lambda^{2(\ell-1)/3}$ modulo $\Lambda^{2(\ell-1)/3 + 1}$
in the ring of integers of $\mathbb{Q}(\rho, \Lambda)$.

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

/-- **Integrality of the elliptic Gauss sum.** Let $\rho = e^{2\pi i/3}$, let
$\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, let $\wp$ be the Weierstrass function of the lattice
$\varpi_1 \mathbb{Z} + \varpi_1 \rho \mathbb{Z}$, and let
$\varphi(u) = 6\wp(\varpi_1 u)/(9 + \wp'(\varpi_1 u))$. Let $a, b$ be integers with
$a \equiv 1 \pmod 3$ and $b \equiv 0 \pmod 3$ such that $\ell = a^2 - ab + b^2$ is a prime with
$\ell \equiv 7 \pmod 9$ or $\ell \equiv 4 \pmod 9$, and put $\lambda = a + b\rho$. Let
$r_0 \in \mathbb{Z}/\ell\mathbb{Z}$ satisfy $a + b r_0 = 0$, and let
$\chi_\lambda : \mathbb{Z}/\ell\mathbb{Z} \to \mathbb{C}$ be a function such that for every
$t \ne 0$ there is an integer $k \ge 0$ with $\chi_\lambda(t) = \rho^k$ and
$t^{(\ell-1)/3} = r_0^k$. Let $f = \varphi$ if $\ell \equiv 7 \pmod 9$ and $f = 1/\varphi$ if
$\ell \equiv 4 \pmod 9$, and let
$$G = \frac{1}{3} \sum_{r=1}^{\ell-1} \chi_\lambda(r)\,f(r/\lambda).$$
Then $G$ is an algebraic integer lying in the subfield $\mathbb{Q}(\rho, \varphi(1/\lambda))$ of
$\mathbb{C}$, and $G$ equals the sum of $f(r/\lambda)$ over the integers $1 \le r \le \ell - 1$ with
$\chi_\lambda(r) = 1$.

Here $\chi_\lambda$ is the cubic residue character modulo $\lambda$, read through the isomorphism
$\mathbb{Z}[\rho]/(\lambda) \cong \mathbb{Z}/\ell\mathbb{Z}$ that sends $\rho$ to $r_0$; the
integers $1, \dots, \ell - 1$ represent $(\mathbb{Z}[\rho]/(\lambda))^\times$, so $G$ is the
elliptic Gauss sum $G_\lambda(\chi_\lambda, f)$ of the source.

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

/-- **Congruences for $|\alpha_\lambda|^2$.** Let $\rho = e^{2\pi i/3}$, let
$\varpi_1 = \int_0^1 (1 - t^3)^{-2/3}\,dt$, let $\wp$ be the Weierstrass function of the lattice
spanned by $\varpi_1$ and $\varpi_1\rho$, and put
$\varphi(u) = 6\wp(\varpi_1 u)/(9 + \wp'(\varpi_1 u))$. Put
$\mathrm{Sl}(u) = \varphi(u/(-3\varpi_1))$. Let $a, b$ be integers with $a \equiv 1$ and
$b \equiv 0 \pmod 3$ such that $\ell = a^2 - ab + b^2$ is prime, and put $\lambda = a + b\rho$.
Let $r_0 \in \mathbb{Z}/\ell$ satisfy $a + b r_0 = 0$, and let
$\chi : \mathbb{Z}/\ell \to \mathbb{C}$ be such that for every $t \ne 0$ there is
$j \in \mathbb{N}$ with $\chi(t) = \rho^j$ and $t^{(\ell-1)/3} = r_0^j$. Let $f = \varphi$ if
$\ell \equiv 7 \pmod 9$ and $f = 1/\varphi$ otherwise, and put
$G = \frac13 \sum_{0 < r < \ell} \chi(r) f(r/\lambda)$,
$\tilde\lambda = \prod_{0 < r < \ell,\ \chi(r) = 1} \varphi(r/\lambda)$ and
$\alpha = G/\tilde\lambda^2$. Let $k = 2(\ell-1)/3$, and let $C$ and $D$ be the coefficients of
$u^k$ in the Taylor expansions at $0$ of $\mathrm{Sl}(u)$ and of $\mathrm{Sl}(u)^{-1} - u^{-1}$.
If $\ell \equiv 7 \pmod 9$, there are integers $m, m'$ prime to $\ell$ with
$m(|\alpha|^2 - (\overline{\chi(3)}\,C)^2/9) \in \lambda\mathbb{Z}[\rho]$ and
$m'(|\alpha|^2 - (3^{(\ell-7)/6} C)^2) \in \ell\mathbb{Z}$. If $\ell \equiv 4 \pmod 9$, there are
integers $m, m'$ prime to $\ell$ with $m(|\alpha|^2 - (\chi(3) D)^2/9) \in \lambda\mathbb{Z}[\rho]$
and $m'(|\alpha|^2 - (3^{(\ell-4)/3} D)^2) \in \ell\mathbb{Z}$.

Here $\lambda\bar\lambda = \ell$, $\rho \mapsto r_0$ identifies $\mathbb{Z}[\rho]/(\lambda)$ with
$\mathbb{Z}/\ell$, $\chi$ is the cubic residue character $\chi_\lambda$ modulo $\lambda$, $G$ is
the elliptic Gauss sum $G_\lambda(\chi_\lambda, f)$ and $\alpha = \alpha_\lambda$ its coefficient,
so the statement gives congruences modulo $\lambda$ and modulo $\ell$. At $u = 0$, where $\wp$ has
a pole, both functions take the value $0$, their limit there, and $C$, $D$ are their $k$-th
derivatives at $0$ divided by $k!$.

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
