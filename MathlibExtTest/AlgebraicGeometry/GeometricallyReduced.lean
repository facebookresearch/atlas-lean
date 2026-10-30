/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Algebra.TensorProductReduced
public import MathlibExt.AlgebraicGeometry.GeometricallyReduced

@[expose] public section

open AlgebraicGeometry

universe u v w

open scoped TensorProduct

example (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [Algebra k A]
    [IsReduced A] (L : Type w) [Field L] [Algebra k L] :
    IsReduced (L ⊗[k] A) :=
  Algebra.isReduced_tensorProduct_of_perfectField k A L

example {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [IsReduced X] :
    AlgebraicGeometry.GeometricallyReduced f :=
  AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField f
