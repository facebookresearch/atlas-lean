/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

open AlgebraicCurve

example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n * v.deg :=
  Divisor.degree_single v n

example {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :
    D ∈ Divisor.degZero (K := K) (F := F) ↔ Divisor.degree D = 0 :=
  Divisor.mem_degZero
