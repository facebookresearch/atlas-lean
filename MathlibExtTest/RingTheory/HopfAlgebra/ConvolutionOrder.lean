/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.ConvolutionOrder

@[expose] public section

universe u v w

/-- The restated theorem applied with the original binders. -/
theorem exactSource
    (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]
    (T : Type w) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) :
    f ^ Module.finrank R H = 1 :=
  HopfAlgebra.convPow_finrank_eq_one_of_isCocomm R H T f

/-- Boundary check: rank zero forces the power to be `f ^ 0 = 1` definitionally. -/
example (R : Type u) [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
    [Coalgebra.IsCocomm R H] [Module.Finite R H] [Module.Free R H]
    (T : Type w) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T))
    (h : Module.finrank R H = 0) : f ^ Module.finrank R H = 1 := by
  rw [h, pow_zero]
