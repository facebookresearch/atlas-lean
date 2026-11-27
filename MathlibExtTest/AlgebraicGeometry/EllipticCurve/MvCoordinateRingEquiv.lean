/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.MvCoordinateRingEquiv

open MvPolynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

-- The isomorphism of coordinate rings, for any Weierstrass curve over a field.
noncomputable example {F : Type} [Field F] (W : WeierstrassCurve F) :
    W.MvCoordinateRing ≃ₐ[F] W.toAffine.CoordinateRing :=
  W.mvCoordinateRingEquiv

-- It sends `x̄ ↦ X̄` and `ȳ ↦ Ȳ`, and its inverse is evaluation at `(x̄, ȳ)`.
example {F : Type} [Field F] (W : WeierstrassCurve F) :
    W.mvCoordinateRingEquiv (W.mvMk (X 1)) = AdjoinRoot.mk W.toAffine.polynomial Polynomial.X :=
  (W.mvCoordinateRingEquiv_X).2

example {F : Type} [Field F] (W : WeierstrassCurve F) (p : F[X][Y]) :
    W.mvCoordinateRingEquiv.symm (AdjoinRoot.mk W.toAffine.polynomial p) =
      W.toMvCoordinateRing p :=
  W.mvCoordinateRingEquiv_symm_mk p

-- `y² = x³ - x` over `ℚ`: the class of `y² - x³ + x` is zero on both sides.
example : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).mvCoordinateRingEquiv
    ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).mvMk (X 1 ^ 2 - X 0 ^ 3 + X 0)) = 0 := by
  have h : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).mvMk (X 1 ^ 2 - X 0 ^ 3 + X 0) = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ?_)
    simp [mvPolynomial]
    ring
  rw [h, map_zero]

end WeierstrassCurve
