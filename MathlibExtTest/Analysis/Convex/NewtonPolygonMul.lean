/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.NewtonPolygonMul

@[expose] public section

open NewtonPolygon MathlibExt.Analysis.Convex.NewtonPolygonMul
open scoped Pointwise

namespace MathlibExtTest.Analysis.Convex.NewtonPolygonMul

/-- Non-vacuity: the Newton polygon of `(x + 1)(y + 1)`, the unit square, is the Minkowski sum of
the two unit segments. -/
example :
    newtonPolygon ((MvPolynomial.X 0 + 1) * (MvPolynomial.X 1 + 1) : MvPolynomial (Fin 2) ℚ) =
    newtonPolygon (MvPolynomial.X 0 + 1 : MvPolynomial (Fin 2) ℚ) +
      newtonPolygon (MvPolynomial.X 1 + 1 : MvPolynomial (Fin 2) ℚ) :=
  newtonPolygon_mul _ _

/-- Over the integers, where cancellation of coefficients could a priori shrink the polygon. -/
example (f g : MvPolynomial (Fin 2) ℤ) :
    newtonPolygon (f * g) = newtonPolygon f + newtonPolygon g :=
  newtonPolygon_mul f g

/-- The inclusion of Newton supports holds over any commutative ring, zero divisors included. -/
example (f g : MvPolynomial (Fin 2) (ZMod 4)) :
    newtonSupport (f * g) ⊆ newtonSupport f + newtonSupport g :=
  newtonSupport_mul_subset f g

end MathlibExtTest.Analysis.Convex.NewtonPolygonMul
