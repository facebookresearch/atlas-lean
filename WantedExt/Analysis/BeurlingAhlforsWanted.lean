/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.BeurlingAhlfors

@[expose] public section

namespace MathlibExt.Analysis.BeurlingAhlforsWanted

open MathlibExt.Analysis.BeurlingAhlfors

/-!
# Catalogue bounds for the Beurling--Ahlfors transform

The published norm bounds from Optimization Problems record 54a. The
upper bound is stated as an actual admissible `L^p` bound (`IsBound`),
not merely as an inequality for the totalized infimum `beurlingNorm`:
since the admissible-constant set could otherwise be empty (in which
case the totalized infimum is `0`), an inequality
`beurlingNorm p ≤ 1.575 * (pstar p - 1)` alone would not assert that any
bound exists. Together with the characteristic lemma
`beurlingNorm_le_of_isBound`, the upper bound here yields that norm
inequality. Together with Lehto's lower bound they give the catalogue
range `1 ≤ C₅₄ ≤ 1.575`; that conversion (and Iwaniec's conjecture
`C₅₄ = 1`) is not formalized here.
-/

/-- **Lehto's lower bound for the Beurling–Ahlfors transform.** For a function
$f : \mathbb{C} \to \mathbb{C}$ let $Bf(z)$ be the limit as $\varepsilon \to 0^+$ of
$-\frac{1}{\pi} \int_{|w - z| > \varepsilon} \frac{f(w)}{(z - w)^2} \, dA(w)$, where $dA$ is
Lebesgue area measure (a junk value where the limit does not exist). For real $p > 1$ let
$p^* = \max(p, p/(p - 1))$ and let $\|B\|_p$ be the infimum of the constants $C \ge 0$ such that
$\|Bf\|_{L^p} \le C\,\|f\|_{L^p}$ in $[0, \infty]$ for every almost everywhere strongly
measurable $f : \mathbb{C} \to \mathbb{C}$, taken to be $0$ when there is no such $C$. Then
$p^* - 1 \le \|B\|_p$ for every real $p > 1$.

Because $\|B\|_p$ is $0$ when no such $C$ exists, this also asserts that $B$ has an admissible
$L^p$ bound for every $p > 1$.

Source: Lehto (1965): `‖B‖ₚ ≥ p* - 1` for all `1 < p`. Known
literature result; its proof is not supplied here. -/
theorem_wanted lehtoLowerBound_wanted :
    ∀ p : ℝ, 1 < p → pstar p - 1 ≤ beurlingNorm p

/-- **Bañuelos–Janakiraman upper bound for the Beurling–Ahlfors transform.** For a function
$f : \mathbb{C} \to \mathbb{C}$ let $Bf(z)$ be the limit as $\varepsilon \to 0^+$ of
$-\frac{1}{\pi} \int_{|w - z| > \varepsilon} \frac{f(w)}{(z - w)^2} \, dA(w)$, where $dA$ is
Lebesgue area measure (a junk value where the limit does not exist), and for real $p > 1$ let
$p^* = \max(p, p/(p - 1))$. For every real $p > 1$ and every almost everywhere strongly measurable
$f : \mathbb{C} \to \mathbb{C}$, $\|Bf\|_{L^p} \le 1.575\,(p^* - 1)\,\|f\|_{L^p}$, with the
$L^p$ norms taken in $[0, \infty]$.

Source: Bañuelos and Janakiraman, *Lp-bounds for the
Beurling--Ahlfors transform*, Trans. Amer. Math. Soc. 360 (2008):
`‖B‖ₚ ≤ 1.575 (p* - 1)` for all `1 < p`. Stated as the actual finite
exponential bound (an admissible `L^p` bound constant), not as an
inequality for the totalized infimum; combined with
`beurlingNorm_le_of_isBound` (and `0 ≤ 1.575 * (pstar p - 1)`, from
`two_le_pstar`) it yields `beurlingNorm p ≤ 1.575 * (pstar p - 1)`.
Known literature result; its proof is not supplied here. -/
theorem_wanted banuelosJanakiramanUpperBound_wanted :
    ∀ p : ℝ, 1 < p → IsBound p ((1575 / 1000 : ℝ) * (pstar p - 1))

/-- **The Beurling–Ahlfors transform has $L^2$ norm $1$.** For a function
$f : \mathbb{C} \to \mathbb{C}$ let $Bf(z)$ be the limit as $\varepsilon \to 0^+$ of
$-\frac{1}{\pi} \int_{|w - z| > \varepsilon} \frac{f(w)}{(z - w)^2} \, dA(w)$, where $dA$ is
Lebesgue area measure (a junk value where the limit does not exist). The infimum $\|B\|_2$ of the
constants $C \ge 0$ such that $\|Bf\|_{L^2} \le C\,\|f\|_{L^2}$ in $[0, \infty]$ for every almost
everywhere strongly measurable $f : \mathbb{C} \to \mathbb{C}$ (taken to be $0$ when there is no
such $C$) equals $1$.

Source: the `L²` isometry recorded in Bañuelos--Janakiraman (2008),
introduction: `‖B‖₂ = 1`. Known literature result; the Fourier-side
proof is not supplied here. -/
theorem_wanted l2Norm_wanted :
    beurlingNorm 2 = 1

end MathlibExt.Analysis.BeurlingAhlforsWanted
