/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_HasseInvariant.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Data.Nat.Basic

@[expose] public section

/-!
# Hasse invariant and the Legendre curve

This file defines the coefficient `WeierstrassCurve.hasseInvariant` of the Hasse criterion for
supersingularity, the Legendre curve `WeierstrassCurve.legendreCurve`, and
`ModularCurve.ssJSetHasse`, the description through the Hasse invariant of the supersingular
`j`-invariants of a finite field of odd characteristic.

Reference: J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Theorem V.4.1 (the
Hasse criterion).
-/

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- **Hasse coefficient of a Weierstrass curve.** For a Weierstrass curve $W$ over a commutative
ring $R$ and $q \in \mathbb{N}$, `W.hasseInvariant q` is the coefficient of $X^{q-1}$ in
$\Psi(X)^{(q-1)/2}$, where $\Psi(X) = 4X^3 + b_2X^2 + 2b_4X + b_6$ is `W.twoTorsionPolynomial`;
subtraction and division in $\mathbb{N}$ are truncated.

Over every commutative ring, $(2y + a_1x + a_3)^2 - \Psi(x)$ is $4$ times the Weierstrass
polynomial of $W$. The equation $(2y + a_1x + a_3)^2 = \Psi(x)$ is a model of $W$ only when $2$ is
invertible: then $(x, y) \mapsto (x, 2y + a_1x + a_3)$ identifies $W$ with the curve
$Y^2 = \Psi(x)$. Otherwise it can lose the curve: over $\mathbb{F}_2$, for $y^2 + y = x^3$ it
reads $1 = 1$, which $(1, 0)$ satisfies although $(1, 0)$ is not a point of the curve.

When $R$ is a field whose characteristic is an odd prime $p$, $q = p$ and $W$ is an elliptic
curve, that is, nonsingular, this is the coefficient of the Hasse criterion (Silverman, *The
Arithmetic of Elliptic Curves*, Theorem V.4.1(a)) for the model $Y^2 = \Psi(x)$ of $W$: the Hasse
invariant of $W$. For other $q$ it is only a coefficient: for example `W.hasseInvariant 2 = 0`
for every $W$, because $(2 - 1)/2 = 0$. -/
noncomputable def hasseInvariant (q : ℕ) (W : WeierstrassCurve R) : R :=
  (W.twoTorsionPolynomial.toPoly ^ ((q - 1) / 2)).coeff (q - 1)

/-- **Legendre curve.** For $t$ in a commutative ring $R$, the Legendre curve is the Weierstrass
curve $y^2 = x(x - 1)(x - t)$, that is, $y^2 = x^3 - (1 + t)x^2 + tx$. -/
def legendreCurve (t : R) : WeierstrassCurve R :=
  ⟨0, -(1 + t), 0, t, 0⟩

end WeierstrassCurve

namespace ModularCurve

/-- **Supersingular $j$-invariants through the Hasse invariant.** Let $K$ be a finite field of
characteristic $p \ne 2$, so that $p$ is an odd prime. A value $j \in K$ lies in
`ssJSetHasse p K` when every elliptic curve $W$ over $K$ with $j$-invariant $j$ has vanishing
Hasse invariant `W.hasseInvariant p`.

Since $2$ is invertible in $K$, $(x, y) \mapsto (x, 2y + a_1x + a_3)$ identifies $W$ with the
curve $Y^2 = \Psi(x)$, where $\Psi$ is `W.twoTorsionPolynomial`, and `W.hasseInvariant p` is the
coefficient of $x^{p-1}$ in $\Psi(x)^{(p-1)/2}$.

Reference: by the Hasse criterion (Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed.,
Theorem V.4.1(a)), an elliptic curve $Y^2 = f(x)$ over a finite field of characteristic $p \ge 3$
is supersingular if and only if the coefficient of $x^{p-1}$ in $f(x)^{(p-1)/2}$ is zero. So $j$
lies in this set exactly when the elliptic curves over $K$ with $j$-invariant $j$ are
supersingular. -/
def ssJSetHasse (p : ℕ) (K : Type*) [Field K] [Finite K] [CharP K p] [NeZero (2 : K)] :
    Set K :=
  {j | ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j → W.hasseInvariant p = 0}

end ModularCurve
