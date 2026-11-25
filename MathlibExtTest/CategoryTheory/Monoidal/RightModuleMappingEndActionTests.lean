/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEndAction

/-!
# Full original-action and bifunctor clients

The action characteristic is checked on the actual source equalizer module.
Complete module arrows in both arguments retain their actual raw carrier
maps and commute on every object of the source mapping bifunctor.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite Opposite
open CategoryTheory.CommutativeModuleConversion
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.RightModuleMappingEndActionTests

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C]
  (R : C) [MonObj R] [IsCommMonObj R]

/-- The entire source mapping module action retains its original ambient inclusion. -/
@[reassoc]
theorem original_action (M N : RightModule R) :
    (RightModuleMappingEnd.moduleObject R M N).action ≫ RightModuleMappingEnd.ι R M N =
      (RightModuleMappingEnd.ι R M N ▷ R) ≫
        RightModuleMappingEnd.auxiliaryRightAction R M N :=
  RightModuleMappingEnd.moduleObject_action_ι R M N

/-- Every parameter arrow into the whole original action domain retains the same action. -/
theorem original_action_after_parameter (M N : RightModule R) {P : C}
    (q : P ⟶ RightModuleMappingEnd.Hom R M N ⊗ R) :
    q ≫ (RightModuleMappingEnd.moduleObject R M N).action ≫
        RightModuleMappingEnd.ι R M N =
      q ≫ (RightModuleMappingEnd.ι R M N ▷ R) ≫
        RightModuleMappingEnd.auxiliaryRightAction R M N := by
  exact congrArg (fun z => q ≫ z)
    (RightModuleMappingEnd.moduleObject_action_ι R M N)

/-- The original target map is a complete module arrow whose underlying map is raw post. -/
theorem original_target_map (M : RightModule R) {N N' : RightModule R} (g : N ⟶ N') :
    ((RightModuleMappingEnd.functor R M).map g).hom = RightModuleMappingEnd.post R M g :=
  RightModuleMappingEnd.map_hom R M g

variable [HasCoequalizers C]

/-- Every complete original source arrow acts as a genuine mapping-module arrow. -/
def changeSource {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (RightModuleMappingEnd.functor R M).obj N ⟶
      (RightModuleMappingEnd.functor R M').obj N :=
  RightModuleMappingEnd.sourceMap R f N

/-- Its whole carrier map is the literal raw equalizer precomposition. -/
theorem changeSource_carrier {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (changeSource R f N).hom = RightModuleMappingEnd.pre R f N :=
  RightModuleMappingEnd.sourceMap_hom R f N

/-- Every whole source arrow retains its actual carrier map at the original end inclusion. -/
@[reassoc]
theorem changeSource_ι {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (changeSource R f N).hom ≫ RightModuleMappingEnd.ι R M' N =
      RightModuleMappingEnd.ι R M N ≫ (MonoidalClosed.pre f.hom).app N.X :=
  RightModuleMappingEnd.sourceMap_ι R f N

/-- The complete original source and target maps commute as whole module morphisms. -/
theorem both_changes {M M' N N' : RightModule R} (f : M' ⟶ M) (g : N ⟶ N') :
    (RightModuleMappingEnd.functor R M).map g ≫ changeSource R f N' =
      changeSource R f N ≫ (RightModuleMappingEnd.functor R M').map g :=
  RightModuleMappingEnd.sourceMap_naturality R f g

/-- The public bifunctor has the actual source equalizer module at every pair. -/
example (M N : RightModule R) :
    (((RightModuleMappingEnd.bifunctor R).obj (op M)).obj N).X =
      RightModuleMappingEnd.Hom R M N := rfl

/-- Every source map of the public bifunctor has its actual complete raw carrier arrow. -/
theorem bifunctor_source_carrier {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (((RightModuleMappingEnd.bifunctor R).map f.op).app N).hom =
      RightModuleMappingEnd.pre R f N :=
  RightModuleMappingEnd.sourceMap_hom R f N

/-- Every target map of the public bifunctor has its actual complete raw carrier arrow. -/
theorem bifunctor_target_carrier (M : RightModule R) {N N' : RightModule R} (g : N ⟶ N') :
    (((RightModuleMappingEnd.bifunctor R).obj (op M)).map g).hom =
      RightModuleMappingEnd.post R M g :=
  RightModuleMappingEnd.map_hom R M g

/-- Original contravariant composition is retained by the actual whole source maps. -/
theorem original_source_order {M M' M'' : RightModule R}
    (f : M' ⟶ M) (g : M'' ⟶ M') (N : RightModule R) :
    changeSource R (g ≫ f) N = changeSource R f N ≫ changeSource R g N :=
  RightModuleMappingEnd.sourceMap_comp R f g N

end CategoryTheory.RightModuleMappingEndActionTests
