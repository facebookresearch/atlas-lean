/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ClosedPoint

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      z.left.base (IsLocalRing.closedPoint k) = x :=
  AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t x hx
