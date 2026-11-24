/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.Limits.Shapes.EndofunctorCone

noncomputable section
universe uC vC
open CategoryTheory Limits
open scoped ZeroObject

namespace EndofunctorConeClients
variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasPushouts C] (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)

example (X : C) : e₁.app X ≫ OriginalScalarCone.quotient S e₁ X = 0 :=
  OriginalScalarCone.endpoint_quotient S e₁ X

example {X Y : C} (f : X ⟶ Y) :
    (OriginalScalarCone.doubleCofiberIso S e₀ e₁ f).hom ≫
      (OriginalScalarCone.doubleCofiberIso S e₀ e₁ f).inv = 𝟙 _ :=
  (OriginalScalarCone.doubleCofiberIso S e₀ e₁ f).hom_inv_id

example {X Y : C} (f : X ⟶ Y) :
    (OriginalScalarCone.doubleCofiberIso S e₀ e₁ f).inv ≫
      (OriginalScalarCone.doubleCofiberIso S e₀ e₁ f).hom = 𝟙 _ :=
  (OriginalScalarCone.doubleCofiberIso S e₀ e₁ f).inv_hom_id

example {Z : C} (hZ : IsZero Z) {f g : Arrow C} (a : f ⟶ g) :
    (OriginalScalarCone.rotationFunctor S e₀ e₁).map a ≫
        OriginalScalarCone.rotationComparison S e₀ e₁ hZ g =
      OriginalScalarCone.rotationComparison S e₀ e₁ hZ f ≫
        (OriginalScalarCone.suspensionFunctor S e₀ e₁ hZ).map a.left :=
  OriginalScalarCone.rotationComparison_naturality S e₀ e₁ hZ a

example {Z : C} (hZ : IsZero Z) (f : Arrow C) :
    OriginalScalarCone.boundary S e₀ e₁ hZ f ≫
        (OriginalScalarCone.suspensionFunctor S e₀ e₁ hZ).map f.hom =
      OriginalScalarCone.targetConeComparison S e₀ e₁ f ≫
        OriginalScalarCone.suspensionQuotient S e₀ e₁ hZ f.right :=
  OriginalScalarCone.boundary_suspension_factors_targetCone S e₀ e₁ hZ f

example {f g : Arrow C} (a : f ⟶ g) :
    (OriginalScalarCone.cofiberFunctor S e₀ e₁).map a ≫
        OriginalScalarCone.canonicalQuotientComparison S e₀ e₁ g =
      OriginalScalarCone.canonicalQuotientComparison S e₀ e₁ f ≫
        (HomotopicalAlgebra.ordinaryCofiber (C := C)).map a :=
  OriginalScalarCone.canonicalQuotientComparison_naturality S e₀ e₁ a


example {A X Z P A' X' Z' P' : C}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (h : IsPushout i z kX kZ) (h' : IsPushout i' z' kX' kZ')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (d : P ⟶ P')
    (hi : a ≫ i' = i ≫ b) (hz : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ d) (hZ : c ≫ kZ' = kZ ≫ d) :
    (OriginalScalarCone.cofiberFunctor S e₀ e₁).map
        (Arrow.homMk (f := Arrow.mk i) (g := Arrow.mk i') a b hi) ≫
      (OriginalScalarCone.cofiberFunctor S e₀ e₁).map
        (Arrow.homMk (f := Arrow.mk i') (g := Arrow.mk kZ') z' kX' h'.w.symm) =
    (OriginalScalarCone.cofiberFunctor S e₀ e₁).map
        (Arrow.homMk (f := Arrow.mk i) (g := Arrow.mk kZ) z kX h.w.symm) ≫
      (OriginalScalarCone.cofiberFunctor S e₀ e₁).map
        (Arrow.homMk (f := Arrow.mk kZ) (g := Arrow.mk kZ') c d hZ) :=
  OriginalScalarCone.originalCallerPushoutCofiber_square S e₀ e₁ i z kX kZ
    i' z' kX' kZ' h h' a b c d hi hz hX hZ

end EndofunctorConeClients
