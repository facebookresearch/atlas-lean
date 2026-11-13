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

/-- **Weighted Lambert series for the continued fractions of order sixteen.** Write
$(a; q)_\infty = \prod_{n \ge 0} (1 - a q^n)$,
$(a_1, \dots, a_k; q)_\infty = (a_1; q)_\infty \cdots (a_k; q)_\infty$ and
$f_k = (q^k; q^k)_\infty$. For every complex number $q$ with $|q| < 1$,
$$\sum_{n \ge 1} n \frac{q^n - q^{7n} - q^{9n} + q^{15n}}{1 - q^{16n}} =
\frac{q f_{16}^2 f_8^2 (q^6, q^{10}; q^{16})_\infty}{(q, q^7, q^9, q^{15}; q^{16})_\infty^2}$$
and
$$\sum_{n \ge 1} n \frac{q^{3n} - q^{5n} - q^{11n} + q^{13n}}{1 - q^{16n}} =
\frac{q^3 f_{16}^2 f_8^2 (q^2, q^{14}; q^{16})_\infty}
{(q^3, q^5, q^{11}, q^{13}; q^{16})_\infty^2}.$$

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

/-- **Lambert series of order sixteen twisted by the Legendre symbol modulo $3$.** Write
$(a; q)_\infty = \prod_{n \ge 0} (1 - a q^n)$,
$(a_1, \dots, a_k; q)_\infty = (a_1; q)_\infty \cdots (a_k; q)_\infty$ and
$f_k = (q^k; q^k)_\infty$, and let $\left(\frac{n}{3}\right)$ be the Legendre symbol modulo $3$.
For every complex number $q$ with $|q| < 1$,
$$\sum_{n \ge 1} \left(\frac{n}{3}\right) \frac{q^n - q^{7n} - q^{9n} + q^{15n}}{1 - q^{16n}} =
\frac{q f_8^2 f_{48} (q^6, q^{10}; q^{16})_\infty (q, q^7, q^9, q^{15}; q^{16})_\infty}
{f_{16} (q^3, q^{21}, q^{27}, q^{45}; q^{48})_\infty}$$
and
$$\sum_{n \ge 1} \left(\frac{n}{3}\right) \frac{q^{3n} - q^{5n} - q^{11n} + q^{13n}}{1 - q^{16n}} =
\frac{q^3 f_8^2 f_{48} (q^2, q^{14}; q^{16})_\infty (q^3, q^5, q^{11}, q^{13}; q^{16})_\infty}
{f_{16} (q^9, q^{15}, q^{33}, q^{39}; q^{48})_\infty}.$$

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

/-- **Product forms of Ramanujan's theta functions $\psi$, $f$ and $\chi$.** Write
$(a; q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ and $f_k = (q^k; q^k)_\infty$, and let
$f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's general theta
function. For every complex number $q$ with $|q| < 1$,
$f(q, q^3) = f_2^2 / f_1$, $f(q, -q^2) = f_2^3 / (f_1 f_4)$, $(-q; q^2)_\infty = f_2^2 / (f_1 f_4)$
and $(q; q^2)_\infty = f_1 / f_2$.

In Ramanujan's notation (Berndt, Part III, Chapter 16), with $\psi(q) = f(q, q^3)$,
$f(q) = f(q, -q^2)$ and $\chi(q) = (-q; q^2)_\infty$, these read $\psi(q) = f_2^2 / f_1$,
$f(q) = f_2^3 / (f_1 f_4)$, $\chi(q) = f_2^2 / (f_1 f_4)$ and $\chi(-q) = f_1 / f_2$.

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

/-- **Ramanujan's Entry 30 (i)–(iii) for the general theta function.** Let
$f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's general theta
function and $\psi(q) = f(q, q^3)$. For all complex numbers $a$ and $b$ with $|ab| < 1$,
$f(a, ab^2) f(b, a^2 b) = f(a, b) \psi(ab)$ and $f(a, b) + f(-a, -b) = 2 f(a^3 b, a b^3)$, and if
moreover $a \ne 0$, then $f(a, b) - f(-a, -b) = 2a f(b/a, a^5 b^3)$.

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


/-- **Odd Lambert series for Ramanujan's continued fractions of order sixteen.** Write
$(a; q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ and $(a, b; q)_\infty = (a; q)_\infty (b; q)_\infty$.
For a complex number $q$ with $|q| < 1$, put
$S(a, b) = \sum_{k \ge 0} (q^{a(2k+1)} + q^{b(2k+1)}) / (1 - q^{16(2k+1)})$, a sum over the odd
multiples $n = 2k + 1$, and
$E = q^4 (q^{32}; q^{32})_\infty^4 / (q^{16}; q^{16})_\infty^2$,
$I_1 = q (q^6, q^{26}; q^{32})_\infty / (q^{10}, q^{22}; q^{32})_\infty$ and
$I_2 = q^3 (q^2, q^{30}; q^{32})_\infty / (q^{14}, q^{18}; q^{32})_\infty$. Then
$S(3, 5) - S(11, 13) = E (I_1 + 1/I_1)$ and $S(1, 7) - S(9, 15) = E (I_2 + 1/I_2)$.
At $q = 0$, where $I_1 = I_2 = 0$, the quotients $1/I_1$ and $1/I_2$ are read as $0$ and both
sides of each identity are $0$.

Here $I_1$ and $I_2$ are $I_1(q^2)$ and $I_2(q^2)$ for Ramanujan's continued fractions of order
sixteen $I_1(q) = q^{1/2} (q^3, q^{13}; q^{16})_\infty / (q^5, q^{11}; q^{16})_\infty$ and
$I_2(q) = q^{3/2} (q, q^{15}; q^{16})_\infty / (q^7, q^9; q^{16})_\infty$, and $E$ is the eta
quotient $\eta^4(32\tau) / \eta^2(16\tau)$ for $q = e^{2 \pi i \tau}$, where
$\eta(\tau) = q^{1/24} (q; q)_\infty$.

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

/-- **Raw Jacobi theta function $\theta_1$.** For complex numbers $z$ and $\tau$, the raw Jacobi
theta function is
$$\theta_1(z \mid \tau) = 2 \sum_{n=0}^{\infty} (-1)^n e^{\pi i \tau (2n+1)^2/4} \sin((2n+1) z)$$
when this series is summable, and $0$ otherwise. With $q = e^{2 \pi i \tau}$, the factor
$e^{\pi i \tau (2n+1)^2/4}$ is $q^{(2n+1)^2/8}$.

The value $0$ for a non-summable series is a convention; it occurs, for example, at $\tau = 0$
and $z = \pi/2$. The intended object is the Jacobi theta function on the upper half-plane
$\operatorname{Im} \tau > 0$, where the series converges for every $z$.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Section 3, Equation (11). -/
noncomputable def jacobiThetaOneSineRaw (z τ : ℂ) : ℂ :=
  2 * ∑' n : ℕ, (-1) ^ n * Complex.exp (Real.pi * Complex.I * τ * (2 * n + 1) ^ 2 / 4) *
    Complex.sin ((2 * n + 1) * z)

/-- **Jacobi theta function $\theta_1$.** For complex numbers $z$ and $\tau$ with
$\operatorname{Im} \tau > 0$, the Jacobi theta function is
$$\theta_1(z \mid \tau) = 2 \sum_{n=0}^{\infty} (-1)^n e^{\pi i \tau (2n+1)^2/4} \sin((2n+1) z).$$
With $q = e^{2 \pi i \tau}$, the factor $e^{\pi i \tau (2n+1)^2/4}$ is $q^{(2n+1)^2/8}$.

On the upper half-plane $\operatorname{Im} \tau > 0$ the series converges for every $z$.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Section 3, Equation (11). -/
noncomputable def jacobiThetaOneSine (z τ : ℂ) (_hτ : 0 < τ.im) : ℂ :=
  jacobiThetaOneSineRaw z τ

/-- **The Jacobi theta function $\theta_1$ vanishes at $z = 0$.** For every complex number $\tau$
with $\operatorname{Im} \tau > 0$, the Jacobi theta function satisfies $\theta_1(0 \mid \tau) = 0$.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Section 3, Equation (11). -/
theorem jacobiThetaOneSine_zero (τ : ℂ) (hτ : 0 < τ.im) : jacobiThetaOneSine 0 τ hτ = 0 := by
  simp [jacobiThetaOneSine, jacobiThetaOneSineRaw]

/-- **Oddness of the Jacobi theta function $\theta_1$.** For all complex numbers $z$ and $\tau$
with $\operatorname{Im} \tau > 0$, the Jacobi theta function satisfies
$\theta_1(-z \mid \tau) = -\theta_1(z \mid \tau)$.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Section 3, Equation (11). -/
theorem jacobiThetaOneSine_neg (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiThetaOneSine (-z) τ hτ = -jacobiThetaOneSine z τ hτ := by
  simp [jacobiThetaOneSine, jacobiThetaOneSineRaw, Complex.sin_neg, tsum_neg]

/-- **Sine Lambert series of order sixteen as quotients of theta functions.** Let $\tau$ and $z$
be complex numbers with $\operatorname{Im} \tau > 0$ and
$|\operatorname{Im} z| < \pi \operatorname{Im} \tau$, let $q = e^{2 \pi i \tau}$, write
$\theta(w) = \theta_1(w \mid 16\tau)$ for the Jacobi theta function $\theta_1$, and let $\theta'$
be the derivative of $\theta$. Then
$$\sum_{n \ge 1} \frac{q^n - q^{7n} - q^{9n} + q^{15n}}{1 - q^{16n}} \sin 2nz =
\frac{-\theta'(0) \theta(8\pi\tau) \theta(6\pi\tau) \theta(2z)}
{4 \theta(z + \pi\tau) \theta(z - \pi\tau) \theta(z + 7\pi\tau) \theta(z - 7\pi\tau)}$$
and
$$\sum_{n \ge 1} \frac{q^{3n} - q^{5n} - q^{11n} + q^{13n}}{1 - q^{16n}} \sin 2nz =
\frac{-\theta'(0) \theta(2\pi\tau) \theta(8\pi\tau) \theta(2z)}
{4 \theta(z + 3\pi\tau) \theta(z - 3\pi\tau) \theta(z + 5\pi\tau) \theta(z - 5\pi\tau)}.$$

Under these hypotheses the series converge and the denominators do not vanish.

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
