/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping

/-!
# Local endomorphisms computed from original beta-ring section maps

Each endomorphism uses the actual monoidal beta unit, the map of the
original ordinary ring section, and the actual native bimodule action.
For analytic Ind modules it is applied after the actual open restriction;
it never asserts a coefficient-open action on all Db^t of that open.
Source: DK1311.2374v2 Section4.10 and Proposition5.1.3;
Mathlib56a005 native monoidal units and Bimod, Apache2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeBetaSectionActions

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe uC uD vC vD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
  (R : Mon C) (A B : Mon D)

def leftSectionEnd (comparison : F.mapMon.obj R ≅ A) (M : Bimod A B)
    (sectionMap : 𝟙_ C ⟶ R.X) : M.X ⟶ M.X :=
  (λ_ M.X).inv ≫ (Functor.LaxMonoidal.ε F ⊗ₘ 𝟙 M.X) ≫
    (F.map sectionMap ⊗ₘ 𝟙 M.X) ≫ (comparison.hom.hom ⊗ₘ 𝟙 M.X) ≫ M.actLeft

def rightSectionEnd (comparison : F.mapMon.obj R ≅ B) (M : Bimod A B)
    (sectionMap : 𝟙_ C ⟶ R.X) : M.X ⟶ M.X :=
  (ρ_ M.X).inv ≫ (𝟙 M.X ⊗ₘ Functor.LaxMonoidal.ε F) ≫
    (𝟙 M.X ⊗ₘ F.map sectionMap) ≫ (𝟙 M.X ⊗ₘ comparison.hom.hom) ≫ M.actRight

end MathlibExt.CategoryTheory.NativeBetaSectionActions
