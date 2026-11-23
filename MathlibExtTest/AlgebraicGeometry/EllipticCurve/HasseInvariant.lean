/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import MathlibExt.AlgebraicGeometry.EllipticCurve.HasseInvariant

open WeierstrassCurve

example {R : Type*} [CommRing R] (t : R) : legendreCurve t = ⟨0, -(1 + t), 0, t, 0⟩ := rfl

example {F : Type*} [Field F] (q : ℕ) (W : WeierstrassCurve F) :
    W.hasseInvariant q = (W.twoTorsionPolynomial.toPoly ^ ((q - 1) / 2)).coeff (q - 1) := rfl
