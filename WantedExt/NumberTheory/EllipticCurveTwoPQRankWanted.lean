/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.NumberTheory.EllipticCurveTwoPQRank
public import MathlibExt.NumberTheory.Padics.MultivariableHensel

/-! # Rank of the elliptic curve `y² = x³ - 2pqx`

Mina and Bacani study the rank of `E₂ₚq : y² = x³ - 2pqx` for distinct odd primes `p` and `q`.
Their Theorem 1(i) is proved in `MathlibExt.NumberTheory.EllipticCurveTwoPQRank` and re-exported
here. The statements below give Theorem 1(ii) and (iii) and Theorem 2.

The Mordell–Weil theorem gives finite generation of the rational point group, whose rank is
`Module.finrank ℤ E.toProjective.Point`. Birch and Stephens' formula gives root number `-1`
in the cases considered here, so the paper's parity hypothesis enters as oddness of the rank.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Odd-rank curves y² = x³ − 2pqx: rank one or three cases.** Let $p \ne q$ be primes and let
$E$ be the elliptic curve $y^2 = x^3 - 2pqx$ over $\mathbb{Q}$, and write
$\left(\frac{p}{q}\right)$ for the Legendre symbol. Suppose that $p \equiv q \equiv 1 \pmod 8$
and $\left(\frac{p}{q}\right) = -1$, or that $p \equiv q \equiv 7 \pmod 8$, or that
$p \equiv 1 \pmod 8$, $q \equiv 3, 5$ or $7 \pmod 8$ and $\left(\frac{p}{q}\right) = 1$. If the
rank of the group $E(\mathbb{Q})$ of rational points is odd, then it equals $1$ or $3$.

The odd-rank hypothesis stands for the parity conjecture for $E$.

Source: Renz Jimwel Mina and Jerico Bacani, *Rank of the Elliptic Curve y^2=x^3-2pqx*,
INTEGERS 26 (2026), Article A51, Theorem 1 (ii) (`integers-2026-A51-thm-1`). -/
public theorem_wanted finrank_point_two_mul_mul_eq_one_or_three {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (E : WeierstrassCurve ℚ)
    (hE : E = ⟨0, 0, 0, -(2 * p * q : ℚ), 0⟩)
    (hcase : (p % 8 = 1 ∧ q % 8 = 1 ∧ jacobiSym p q = -1) ∨ (p % 8 = 7 ∧ q % 8 = 7) ∨
      (p % 8 = 1 ∧ q % 8 ∈ [3, 5, 7] ∧ jacobiSym p q = 1))
    (hparity : Odd (Module.finrank ℤ E.toProjective.Point)) :
    Module.finrank ℤ E.toProjective.Point = 1 ∨ Module.finrank ℤ E.toProjective.Point = 3

/-- **Odd-rank curves y² = x³ − 2pqx: rank one, three or five case.** Let $p \ne q$ be primes
with $p \equiv q \equiv 1 \pmod 8$ and Legendre symbol $\left(\frac{p}{q}\right) = 1$, and let
$E$ be the elliptic curve $y^2 = x^3 - 2pqx$ over $\mathbb{Q}$. If the rank of the group
$E(\mathbb{Q})$ of rational points is odd, then it equals $1$, $3$ or $5$.

The odd-rank hypothesis stands for the parity conjecture for $E$.

Source: Renz Jimwel Mina and Jerico Bacani, *Rank of the Elliptic Curve y^2=x^3-2pqx*,
INTEGERS 26 (2026), Article A51, Theorem 1 (iii) (`integers-2026-A51-thm-1`). -/
public theorem_wanted finrank_point_two_mul_mul_eq_one_or_three_or_five {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (E : WeierstrassCurve ℚ)
    (hE : E = ⟨0, 0, 0, -(2 * p * q : ℚ), 0⟩)
    (hcase : p % 8 = 1 ∧ q % 8 = 1 ∧ jacobiSym p q = 1)
    (hparity : Odd (Module.finrank ℤ E.toProjective.Point)) :
    Module.finrank ℤ E.toProjective.Point = 1 ∨ Module.finrank ℤ E.toProjective.Point = 3 ∨
      Module.finrank ℤ E.toProjective.Point = 5

/-- **Odd-rank curves y² = x³ − 2pqx: a rank three family.** Let $r$ be a positive integer such
that $p = 272r^2 + 120r + 9$ and $q = 2p + 9 = 544r^2 + 240r + 27$ are both prime, and let $E$
be the elliptic curve $y^2 = x^3 - 2pqx$ over $\mathbb{Q}$. If the rank of the group
$E(\mathbb{Q})$ of rational points is odd, then it equals $3$.

The odd-rank hypothesis stands for the parity conjecture for $E$.

Source: Renz Jimwel Mina and Jerico Bacani, *Rank of the Elliptic Curve y^2=x^3-2pqx*,
INTEGERS 26 (2026), Article A51, Theorem 2 (`integers-2026-A51-thm-2`). -/
public theorem_wanted finrank_point_two_mul_mul_eq_three {r : ℕ} (hr : 0 < r)
    (hp : (272 * r ^ 2 + 120 * r + 9).Prime) (hq : (544 * r ^ 2 + 240 * r + 27).Prime)
    (E : WeierstrassCurve ℚ)
    (hE : E = ⟨0, 0, 0,
      -(2 * (272 * r ^ 2 + 120 * r + 9 : ℕ) * (544 * r ^ 2 + 240 * r + 27 : ℕ) : ℚ), 0⟩)
    (hparity : Odd (Module.finrank ℤ E.toProjective.Point)) :
    Module.finrank ℤ E.toProjective.Point = 3

end

end MetaMathlibExt
