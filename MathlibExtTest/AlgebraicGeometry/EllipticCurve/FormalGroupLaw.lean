/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.FormalGroupLaw

@[expose] public section

open PowerSeries

-- `exactSource` consumer: the defining equation with the original binders.
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.formalW
      = X ^ 3 + C W.a₁ * X * W.formalW + C W.a₂ * X ^ 2 * W.formalW
        + C W.a₃ * W.formalW ^ 2 + C W.a₄ * X * W.formalW ^ 2
        + C W.a₆ * W.formalW ^ 3 :=
  W.formalW_eq

-- Higher-universe consumer.
example {R : Type 1} [CommRing R] (W : WeierstrassCurve R) :
    W.formalW
      = X ^ 3 + C W.a₁ * X * W.formalW + C W.a₂ * X ^ 2 * W.formalW
        + C W.a₃ * W.formalW ^ 2 + C W.a₄ * X * W.formalW ^ 2
        + C W.a₆ * W.formalW ^ 3 :=
  W.formalW_eq

example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 1) W.formalGroupLaw = 1 :=
  W.coeff_single_formalGroupLaw i

-- Boundary: over a nontrivial ring the order is exactly `3`, so `formalW`
-- is nonzero and is not divisible by `X ^ 4`.
example {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) :
    (W.formalW).order = 3 :=
  W.order_formalW

example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    PowerSeries.coeff 3 W.formalW = 1 ∧ PowerSeries.coeff 4 W.formalW = W.a₁ :=
  ⟨W.coeff_formalW_three, W.coeff_formalW_four⟩
