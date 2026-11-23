/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Sections

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

example {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    Dense {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧
      s (IsLocalRing.closedPoint k) = x} :=
  AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed f

example {κ : Type u} [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of κ)) (fY : Y ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType fX] [IsReduced X] [IsSeparated fY]
    {f g : X ⟶ Y} (hf : f ≫ fY = fX) (hg : g ≫ fY = fX)
    (h : ∀ x : Spec (CommRingCat.of κ) ⟶ X, x ≫ fX = 𝟙 _ → x ≫ f = x ≫ g) :
    f = g :=
  AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed fX fY hf hg h

example {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Surjective f] (y : Spec (.of K) ⟶ Y) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ f = y :=
  AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed f y
