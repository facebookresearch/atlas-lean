/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeMappingEnd

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.CommutativeModuleConversion (RightModule)
open CategoryTheory.RightModuleMappingEnd
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.RightModuleFreeMappingEndTests

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C]
  (R : C) [MonObj R]

-- The full mapping object and generator map require no scalar commutativity.
example (X : C) (N : RightModule R) :
    RightModuleMappingEnd.Hom R (RightModuleFree.freeObject R X) N ⟶
      (ihom X).obj N.X :=
  RightModuleMappingEnd.freeSourceForward R X N

-- No scalar-commutativity instance has been supplied or silently obtained.
example : True := by
  fail_if_success letI : IsCommMonObj R := inferInstance
  exact True.intro

/-- The public object isomorphism works with independent universes and a general monoid. -/
def noncommutativeIso (X : C) (N : RightModule R) :
    Hom R (RightModuleFree.freeObject R X) N ≅ (ihom X).obj N.X :=
  freeSourceIso R X N

/-- Every inverse coefficient arrow retains the whole original balanced extension family. -/
theorem inverse_projection (X P : C) (N : RightModule R) (q : P ⟶ (ihom X).obj N.X) :
    (q ≫ (noncommutativeIso R X N).inv) ≫ ι R (RightModuleFree.freeObject R X) N =
      MonoidalClosed.curry (freeSourceExtension R X P N (MonoidalClosed.uncurry q)) := by
  change (q ≫ freeSourceBackward R X N) ≫ _ = _
  rw [← freeSourceParameterEquiv_symm_apply, freeSourceParameterEquiv_symm_ι]

/-- Whole source-module arrows are classified by their actual free-generator component. -/
theorem whole_source_generator {X X' P : C}
    (f : RightModuleFree.freeObject R X' ⟶ RightModuleFree.freeObject R X)
    (N : RightModule R) (p : P ⟶ Hom R (RightModuleFree.freeObject R X) N) :
    freeSourceParameterEquiv R X' N P (p ≫ pre R f N) =
      p ≫ ι R (RightModuleFree.freeObject R X) N ≫
        (MonoidalClosed.pre (RightModuleFree.freeGenerator R X' ≫ f.hom)).app N.X := by
  rw [freeSourceParameterEquiv_apply, Category.assoc, freeSourceForward_pre]

/-- All three original variances commute on a complete coefficient family. -/
theorem all_variances_commute {X X' P Q : C} (f : Q ⟶ P) (h : X' ⟶ X)
    {N N' : RightModule R} (g : N ⟶ N')
    (p : P ⟶ Hom R (RightModuleFree.freeObject R X) N) :
    freeSourceParameterEquiv R X' N' Q
        (f ≫ p ≫ pre R (RightModuleFree.freeMap R h) N ≫
          post R (RightModuleFree.freeObject R X') g) =
      f ≫ freeSourceParameterEquiv R X N P p ≫
        (MonoidalClosed.pre h).app N.X ≫ (ihom X').map g.hom := by
  simp only [freeSourceParameterEquiv_apply, Category.assoc]
  rw [freeSourceForward_naturality_target, freeSourceForward_naturality_source_assoc]

-- The original free unit is used in the forward object map.
example (X : C) (N : RightModule R) :
    (noncommutativeIso R X N).hom = ι R (RightModuleFree.freeObject R X) N ≫
      (MonoidalClosed.pre ((RightModuleFree.adjunction R).unit.app X)).app N.X :=
  freeSourceForward_unit R X N

-- The original free counit acts on the whole parameterized extension.
example (X P : C) (N : RightModule R) (q : X ⊗ P ⟶ N.X) :
    freeSourceExtensionModule R X P N q =
      (RightModuleFree.coefficientFreeIso R P X).hom ≫
        RightModuleFree.freeMap R ((β_ P X).hom ≫ q) ≫ RightModuleFree.actionCounit R N :=
  freeSourceExtensionModule_counit R X P N q

-- Full balance holds on every coefficient, before any generator point is selected.
example (X P : C) (N : RightModule R) (q : X ⊗ P ⟶ N.X) :
    MonoidalClosed.curry (freeSourceExtension R X P N q) ≫
        sourceActionMap R (RightModuleFree.freeObject R X) N =
      MonoidalClosed.curry (freeSourceExtension R X P N q) ≫
        targetActionMap R (RightModuleFree.freeObject R X) N :=
  (freeSourceExtensionFamily R X P N q).condition

-- Both whole object maps are inverses on the original source object and internal Hom.
example (X : C) (N : RightModule R) :
    (noncommutativeIso R X N).hom ≫ (noncommutativeIso R X N).inv = 𝟙 _ :=
  (noncommutativeIso R X N).hom_inv_id

example (X : C) (N : RightModule R) :
    (noncommutativeIso R X N).inv ≫ (noncommutativeIso R X N).hom = 𝟙 _ :=
  (noncommutativeIso R X N).inv_hom_id

end CategoryTheory.RightModuleFreeMappingEndTests
