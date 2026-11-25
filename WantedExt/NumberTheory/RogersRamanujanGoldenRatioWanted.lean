/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.PowerSeries.Expand
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import WantedExt.NumberTheory.SquaresTriangularRepresentationsWanted

/-!
# Ramanujan's theta functions, the Rogers-Ramanujan continued fraction and the golden ratio

Statements from S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43.

`ψ(q) = ∑_{n ≥ 0} q^{n(n+1)/2}` and the coefficient
`g(0) = (16ψ⁵(q) - τ(q){τ⁴(q) + 5τ²(q)ρ(q) + 5ρ²(q)}) / (5ψ(q⁵))`, with
`τ(q) = ψ(q) - 5q³ψ(q²⁵)` and `ρ(q) = ψ²(q) - 5qψ²(q⁵)`. Theorem 1 is stated on the imaginary
axis `τ = it`, `t > 0`, where `q = e^{πiτ} = e^{-πt}` and `q' = e^{-π/t}` are real in `(0, 1)`
and every power is a positive real power. Theorem 2 is stated as an identity of integer power
series (`ψ` is `triangularThetaSeries`, `(q^k; q^k)_∞` is `qEulerProduct k`, `q ↦ q^k` is
`PowerSeries.expand k`), with the denominators `5ψ(q⁵)`, `E₅` and `E₂₅` cleared.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **The real Rogers–Ramanujan continued fraction.** For a real number $x$,
$$
R(x) = x^{1/5} \prod_{n \ge 0}
\frac{(1 - x^{5n+1})(1 - x^{5n+4})}{(1 - x^{5n+2})(1 - x^{5n+3})},
$$
where $x^{1/5}$ is the real power function (the nonnegative fifth root for $x \ge 0$, and
$|x|^{1/5} \cos(\pi/5)$ for $x < 0$), a factor whose denominator is $0$ is read as $0$, and the
infinite product is taken to be $1$ when it does not converge unconditionally. For $0 \le x < 1$
this is the product formula
$R(x) = x^{1/5} (x; x^5)_\infty (x^4; x^5)_\infty / ((x^2; x^5)_\infty (x^3; x^5)_\infty)$ of the
Rogers–Ramanujan continued fraction, where $(c; q)_\infty = \prod_{m \ge 0} (1 - c q^m)$.

Source: S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43,
Section 1 (the Rogers-Ramanujan continued fraction formula). -/
public noncomputable def rogersRamanujanContFracReal (x : ℝ) : ℝ :=
  x ^ (1 / 5 : ℝ) * ∏' n : ℕ, ((1 - x ^ (5 * n + 1)) * (1 - x ^ (5 * n + 4)) /
    ((1 - x ^ (5 * n + 2)) * (1 - x ^ (5 * n + 3))))

/-- **The Rogers–Ramanujan continued fraction vanishes at zero.** The real Rogers–Ramanujan
continued fraction $R$ satisfies $R(0) = 0$.

Source: S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43,
Section 1 (the Rogers-Ramanujan continued fraction formula). -/
public theorem rogersRamanujanContFracReal_zero : rogersRamanujanContFracReal 0 = 0 := by
  simp [rogersRamanujanContFracReal]

/-- **Golden-ratio relation for the Rogers–Ramanujan continued fraction.** Let $t > 0$, and put
$q = e^{-\pi t}$ and $q' = e^{-\pi/t}$. Let $\psi(x) = \sum_{n \ge 0} x^{n(n+1)/2}$ and
$E(x) = (x; x)_\infty = \prod_{n \ge 1} (1 - x^n)$, and set
$\tau(q) = \psi(q) - 5q^3 \psi(q^{25})$, $\rho(q) = \psi(q)^2 - 5q\,\psi(q^5)^2$ and
$$
g(0) = \frac{16\psi(q)^5 - \tau(q)\bigl(\tau(q)^4 + 5\tau(q)^2\rho(q) +
5\rho(q)^2\bigr)}{5\psi(q^5)}.
$$
Let $\Phi = (\sqrt{5} + 1)/2$, let $R$ be the real Rogers–Ramanujan continued fraction, and put
$U = \bigl(R(q)\,R(q'^{4/5})\bigr)^{5/2}$ and $V = \bigl(R(q)/R(q'^{4/5})\bigr)^{5/2}$. Then
$$
\Bigl(\sqrt{\Phi} - \frac{1}{\sqrt{\Phi}}\Bigr)\Bigl(U + \frac{1}{U}\Bigr) +
\Bigl(\sqrt{\Phi} + \frac{1}{\sqrt{\Phi}}\Bigr)\Bigl(V - \frac{1}{V}\Bigr) =
\frac{g(0)}{\sqrt{q}\,\bigl(E(q)\,E(q^5)\bigr)^2}.
$$

This is Theorem 1 of the source on the imaginary axis $z = it$, where $q = e^{\pi i z}$ and
$q' = e^{\pi i z'}$ with $z z' = -1$.

Source: S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43,
Theorem 1, Equation (3) (`integers-2025-A43-thm-1`). -/
public theorem_wanted rogersRamanujan_golden_ratio_theta_relation (t : ℝ) (ht : 0 < t) :
    let q : ℝ := Real.exp (-Real.pi * t)
    let q' : ℝ := Real.exp (-Real.pi / t)
    let ψ : ℝ → ℝ := fun x => ∑' n : ℕ, x ^ (n * (n + 1) / 2)
    let E : ℝ → ℝ := fun x => ∏' n : ℕ, (1 - x ^ (n + 1))
    let τ : ℝ := ψ q - 5 * q ^ 3 * ψ (q ^ 25)
    let ρ : ℝ := ψ q ^ 2 - 5 * q * ψ (q ^ 5) ^ 2
    let g₀ : ℝ := (16 * ψ q ^ 5 - τ * (τ ^ 4 + 5 * τ ^ 2 * ρ + 5 * ρ ^ 2)) / (5 * ψ (q ^ 5))
    let Φ : ℝ := (Real.sqrt 5 + 1) / 2
    let R₁ : ℝ := rogersRamanujanContFracReal q
    let R₂ : ℝ := rogersRamanujanContFracReal (q' ^ (4 / 5 : ℝ))
    let U : ℝ := (R₁ * R₂) ^ (5 / 2 : ℝ)
    let V : ℝ := (R₁ / R₂) ^ (5 / 2 : ℝ)
    (Real.sqrt Φ - 1 / Real.sqrt Φ) * (U + 1 / U) +
        (Real.sqrt Φ + 1 / Real.sqrt Φ) * (V - 1 / V) =
      1 / Real.sqrt q * (g₀ / (E q * E (q ^ 5)) ^ 2)

/-- **Eta-quotient form of the Gladun–Chaudhary theta coefficient.** In the ring of integer
power series in $q$, let $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$ be the triangular theta series
and $E_k = (q^k; q^k)_\infty$ the Euler products, and set $\tau(q) = \psi(q) - 5q^3\psi(q^{25})$
and $\rho(q) = \psi(q)^2 - 5q\,\psi(q^5)^2$. Then
$$
\bigl(16\psi(q)^5 - \tau(q)\bigl(\tau(q)^4 + 5\tau(q)^2\rho(q) + 5\rho(q)^2\bigr)\bigr)E_5E_{25} =
5\psi(q^5)\bigl(E_5^6 + 20q\,E_1^4E_{25}^2 + 110q^2E_1^3E_{25}^3 + 350q^3E_1^2E_{25}^4 +
600q^4E_1E_{25}^5 + 625q^5E_{25}^6\bigr).
$$

This is Theorem 2 of the source, which writes
$g(0) = \bigl(16\psi(q)^5 - \tau(q)(\tau(q)^4 + 5\tau(q)^2\rho(q) + 5\rho(q)^2)\bigr)/(5\psi(q^5))$
as $E_5^5/E_{25} + 20q\,E_1^4E_{25}/E_5 + 110q^2E_1^3E_{25}^2/E_5 + 350q^3E_1^2E_{25}^3/E_5 +
600q^4E_1E_{25}^4/E_5 + 625q^5E_{25}^5/E_5$, multiplied through by $5\psi(q^5)E_5E_{25}$.

Source: S. E. Gladun and M. P. Chaudhary, *Connecting Ramanujan's Theta Functions, the
Rogers-Ramanujan Continued Fraction, and the Golden Ratio*, INTEGERS 25 (2025), Article A43,
Theorem 2 (`integers-2025-A43-thm-2`). -/
public theorem_wanted rogersRamanujan_theta_coeff_eta_quotient :
    let ψ : ℤ⟦X⟧ := triangularThetaSeries
    let τ : ℤ⟦X⟧ := ψ - 5 * X ^ 3 * expand 25 (by norm_num) ψ
    let ρ : ℤ⟦X⟧ := ψ ^ 2 - 5 * X * expand 5 (by norm_num) ψ ^ 2
    (16 * ψ ^ 5 - τ * (τ ^ 4 + 5 * τ ^ 2 * ρ + 5 * ρ ^ 2)) * qEulerProduct 5 * qEulerProduct 25 =
      5 * expand 5 (by norm_num) ψ *
        (qEulerProduct 5 ^ 6 + qEulerProduct 25 *
          (20 * X * qEulerProduct 1 ^ 4 * qEulerProduct 25 +
            110 * X ^ 2 * qEulerProduct 1 ^ 3 * qEulerProduct 25 ^ 2 +
            350 * X ^ 3 * qEulerProduct 1 ^ 2 * qEulerProduct 25 ^ 3 +
            600 * X ^ 4 * qEulerProduct 1 * qEulerProduct 25 ^ 4 +
            625 * X ^ 5 * qEulerProduct 25 ^ 5))

end

end MetaMathlibExt
