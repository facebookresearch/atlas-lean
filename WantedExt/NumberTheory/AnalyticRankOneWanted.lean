/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic

namespace WeierstrassCurve

/-- **Gross–Zagier–Kolyvagin, rank-one implication.** Let $E/\mathbb{Q}$ be an elliptic curve,
and let $F$ be an entire function agreeing with the $L$-series of $E$ on the half-plane of
absolute convergence $\operatorname{Re}(s)>3/2$, so that $F$ is the entire continuation of the
Hasse–Weil $L$-function of $E$. If $F(1)=0$ and $F'(1)\ne 0$, that is, if this $L$-function has
a simple zero at $s=1$, then the Mordell–Weil rank of $E$ is one: the group $E(\mathbb{Q})$ of
rational points has rank one as a $\mathbb{Z}$-module.

This is the rank-one case of the rank equality in Robert L. Miller,
*Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank
zero and one*, LMS J. Comput. Math. 14 (2011), 327–350,
[Theorem 4.4, pp. 336–337](https://doi.org/10.1112/S1461157011000180). -/
public theorem_wanted rank_eq_one_of_simple_zero_lSeries (E : WeierstrassCurve ℚ)
    (hE : E.IsElliptic) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hL : ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s)
    (hzero : F 1 = 0) (hderiv : deriv F 1 ≠ 0) :
    Module.rank ℤ E.toAffine.Point = 1

end WeierstrassCurve
