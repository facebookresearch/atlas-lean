/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.NerveProduct

/-!
# Strict nerve product consumer tests

Focused same-universe checks for the public `nerveProdIso`:
generic iso type, forward `mk₀`/`mk₁` actions, inverse paired actions,
and projection compatibility.
Strict nerve-level checks only.
-/

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace MathlibExtTest.CategoryTheory.NerveProductTests

variable (C D : Type u) [Category.{v} C] [Category.{v} D]

/-- Generic same-universe iso type. -/
noncomputable example : nerve (C × D) ≅ nerve C ⨯ nerve D :=
  nerveProdIso C D

/-- Forward action on `mk₀`. -/
example (X : C × D) :
    (nerveProdIso C D).hom.app (op ⦋0⦌) (ComposableArrows.mk₀ X) =
      FunctorToTypes.prodMk (ComposableArrows.mk₀ X.1) (ComposableArrows.mk₀ X.2) :=
  nerveProdIso_hom_app_mk₀ C D X

/-- Forward action on `mk₁`. -/
example {X Y : C × D} (f : X ⟶ Y) :
    (nerveProdIso C D).hom.app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      FunctorToTypes.prodMk (ComposableArrows.mk₁ f.1) (ComposableArrows.mk₁ f.2) :=
  nerveProdIso_hom_app_mk₁ C D f

/-- Inverse action on a paired `mk₀`. -/
example (X : C) (Y : D) :
    (nerveProdIso C D).inv.app (op ⦋0⦌)
      (FunctorToTypes.prodMk (ComposableArrows.mk₀ X) (ComposableArrows.mk₀ Y)) =
      ComposableArrows.mk₀ (X, Y) :=
  nerveProdIso_inv_app_pair_mk₀ C D X Y

/-- Inverse action on a paired `mk₁`. -/
example {X₁ Y₁ : C} {X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (nerveProdIso C D).inv.app (op ⦋1⦌)
      (FunctorToTypes.prodMk (ComposableArrows.mk₁ f) (ComposableArrows.mk₁ g)) =
      ComposableArrows.mk₁ (Prod.mkHom f g) :=
  nerveProdIso_inv_app_pair_mk₁ C D f g

/-- Forward iso followed by the first projection. -/
example : (nerveProdIso C D).hom ≫ prod.fst = nerveMap (CategoryTheory.Prod.fst C D) :=
  nerveProdIso_hom_comp_fst C D

/-- Forward iso followed by the second projection. -/
example : (nerveProdIso C D).hom ≫ prod.snd = nerveMap (CategoryTheory.Prod.snd C D) :=
  nerveProdIso_hom_comp_snd C D

/-- Forward naturality in each factor (strict nerve-level only). -/
example (C C' D D' : Type u) [Category.{v} C] [Category.{v} C'] [Category.{v} D]
    [Category.{v} D'] (F : C ⥤ C') (G : D ⥤ D') :
    nerveMap (F.prod G) ≫ (nerveProdIso C' D').hom =
      (nerveProdIso C D).hom ≫ Limits.prod.map (nerveMap F) (nerveMap G) :=
  nerveProdIso_natural C C' D D' F G

end MathlibExtTest.CategoryTheory.NerveProductTests
