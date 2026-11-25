/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic

namespace WeierstrassCurve

open IsDedekindDomain NumberField

/-- **Gross–Zagier–Kolyvagin, rank-one case, for a global minimal equation.** Let $E$ be an
elliptic curve over $\mathbb{Q}$ given by a global minimal Weierstrass equation: its coefficients
are integers and it is minimal at every prime. If its Hasse–Weil $L$-function vanishes to order
exactly one at $s = 1$, then the Mordell–Weil group $E(\mathbb{Q})$ has rank one. The $L$-function
is given as an entire function $F$ that agrees with the $L$-series on the half-plane
$\operatorname{Re}(s) > 3/2$, where the series converges absolutely.

Source: Robert L. Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic
curves of analytic rank zero and one*, LMS J. Comput. Math. 14 (2011), 327–350,
[Theorem 4.4, p. 336](https://doi.org/10.1112/S1461157011000180), in the case
$r_{\mathrm{an}}(E) = 1$: "If $r_{\mathrm{an}}(E) \le 1$, then there exists a quadratic field $K$
satisfying the Heegner hypothesis such that $y_K$ is non-torsion. In particular,
$r(E) = r_{\mathrm{an}}(E)$, …". The conventions are those of §1, p. 327: "Let $E$ be an elliptic
curve defined over $\mathbb{Q}$, given by a global minimal Weierstrass equation. We denote … the
rank of the Mordell–Weil group $E(\mathbb{Q})$ by $r$ … Let $L(E/\mathbb{Q}, s)$ be the Hasse–Weil
$L$-function of $E$, and denote its order of vanishing at $s = 1$ by
$r_{\mathrm{an}}(E/\mathbb{Q})$." -/
public theorem_wanted rank_eq_one_of_isMinimal_of_analyticOrderAt_eq_one
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [E.IsIntegral ℤ]
    (hmin : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (E.baseChange (v.adicCompletion ℚ)).IsMinimal (v.adicCompletionIntegers ℚ))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hL : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s)
    (horder : analyticOrderAt F 1 = 1) :
    Module.rank ℤ E.toAffine.Point = 1

end WeierstrassCurve
