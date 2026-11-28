/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GroupSchemeTranslates

/-!
# Tests for translates of open subsets of a group scheme over a field
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace MathlibExtTest.AlgebraicGeometry.GroupSchemeTranslates

universe u

/-- The image of `T ×_k U ⟶ G`, `(t, u) ↦ a(t) * u`, is open. -/
example {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    {T : Scheme.{u}} (a : T ⟶ G) (U : G.Opens) :
    IsOpen (Set.range (((Over.homMk a rfl : Over.mk (a ≫ f) ⟶ Over.mk f) ⊗ₘ
      (Over.homMk U.ι rfl : Over.mk (U.ι ≫ f) ⟶ Over.mk f)) ≫ μ).left) :=
  isOpen_range_mul_of_grpObj f a U

/-- In particular, for a `k`-rational point `g : Spec k ⟶ G`, the image of `U` under left
translation by `g` is open. -/
example {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    (g : Spec (.of k) ⟶ G) (U : G.Opens) :
    IsOpen (Set.range (((Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) ⊗ₘ
      (Over.homMk U.ι rfl : Over.mk (U.ι ≫ f) ⟶ Over.mk f)) ≫ μ).left) :=
  isOpen_range_mul_of_grpObj f g U

/-- The second component of the shearing automorphism of `T ×_S G`, for a group scheme `G` over
`S` and a morphism `a : T ⟶ G` over `S`, is `(t, g) ↦ a(t) * g`. -/
example {S : Scheme.{u}} {T G : Over S} [GrpObj G] (a : T ⟶ G) :
    (GrpObj.shearIso a).hom ≫ snd T G = fst T G ≫ a * snd T G := by
  simp [Hom.mul_def]

end MathlibExtTest.AlgebraicGeometry.GroupSchemeTranslates
