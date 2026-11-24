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

import MathlibExt.CategoryTheory.Adjunction.ParametrizedLeftIsoComparison
import Mathlib.Tactic.Linter.Lint

/-! # Public use of original parametrized left-adjoint comparisons -/

set_option autoImplicit false
noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory Opposite
open CategoryTheory.ParametrizedAdjunction.LeftIsoComparison

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F L : C₁ ⥤ C₂ ⥤ C₃} {G R : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}

example (a : F ⊣₂ G) (b : L ⊣₂ R) (e : G ≅ R) {A B : C₁} (p : A ⟶ B) :
    F.map p ≫ (component a b e B).hom = (component a b e A).hom ≫ L.map p :=
  component_naturality a b e p

example (a : F ⊣₂ G) (b : L ⊣₂ R) (e : G ≅ R) (A : C₁) :
    (iso a b e).app A =
      Adjunction.RightIsoComparison.comparison (a.adj A) (b.adj A) (e.app (op A)) :=
  iso_app a b e A

example (a : F ⊣₂ G) (b : L ⊣₂ R) (e : G ≅ R) (A : C₁) (X : C₂) :
    (a.adj A).unit.app X ≫ (e.app (op A)).hom.app ((F.obj A).obj X) ≫
        (R.obj (op A)).map ((component a b e A).hom.app X) = (b.adj A).unit.app X :=
  Adjunction.RightIsoComparison.unit (a.adj A) (b.adj A) (e.app (op A)) X

example (a : F ⊣₂ G) (b : L ⊣₂ R) (e : G ≅ R) (A : C₁) (Y : C₃) :
    (component a b e A).hom.app ((R.obj (op A)).obj Y) ≫ (b.adj A).counit.app Y =
      (F.obj A).map ((e.app (op A)).inv.app Y) ≫ (a.adj A).counit.app Y :=
  Adjunction.RightIsoComparison.counit (a.adj A) (b.adj A) (e.app (op A)) Y

#print axioms component
#print axioms component_naturality
#print axioms iso
#print axioms iso_app
#lint only unusedArguments in MathlibExt.CategoryTheory.Adjunction.ParametrizedLeftIsoComparison
