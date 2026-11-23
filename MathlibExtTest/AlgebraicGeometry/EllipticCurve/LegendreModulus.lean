/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import MathlibExt.AlgebraicGeometry.EllipticCurve.LegendreModulus

open WeierstrassCurve

example {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).legendreLambda 0 1 = t :=
  legendreLambda_legendreCurve h2 t

example {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).thirdTwoTorsionX 0 1 = t :=
  thirdTwoTorsionX_legendreCurve h2 t

