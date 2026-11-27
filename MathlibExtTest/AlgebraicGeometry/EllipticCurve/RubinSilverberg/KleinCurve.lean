/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.RubinSilverberg.KleinCurve

@[expose] public section

open RubinSilverberg

-- Consumer with the original binders.
private theorem exactSource {K : Type*} [Field K] [CharZero K] (ζ : K)
    (hζ : IsPrimitiveRoot ζ 5) (x : RatFunc K) :
    ((kleinCurve (RatFunc.X : RatFunc K)).Ψ₃).eval x ≠ 0 :=
  kleinCurve_Psi3_eval_ne_zero ζ hζ x

-- Boundary: over the base field the statement fails. At `u = 0` the Klein curve is
-- `y² = x³ - x/48 + 1/864`, and `x = 1/12` is a root of its `3`-division polynomial.
example : ((kleinCurve (0 : ℚ)).Ψ₃).eval (1 / 12) = 0 := by
  norm_num [kleinCurve, kleinH, kleinT, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
