/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEndComponents
public import MathlibExt.CategoryTheory.Monoidal.Mod.ClosedComponents

/-!
# Original source components of the balanced mapping adjunction

The formulas retain both original conversion units and counits and the
balanced relative tensor unit and counit. All functors, modules and arrows
are those of the actual original right-module adjunction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.CommutativeModuleConversion
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.RightModuleMappingEnd

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasCoequalizers C]
  (R : C) [MonObj R] [IsCommMonObj R]

/-- The actual relative tensor structure used by the original mapping adjunction. -/
local instance originalModuleMonoidal : MonoidalCategory (RightModule R) :=
  RightModuleFree.tensorMonoidal R

variable [HasEqualizers C]

/-- The whole original stock unit keeps both conversion units and the balanced unit. -/
theorem stockAdjunction_unit_app (M N : RightModule R) :
    (stockAdjunction R M).unit.app N =
      (moduleEquivalence R).symm.toAdjunction.unit.app N ≫
        (moduleEquivalence R).functor.map
          ((Mod.relativeTensorInternalHomAdjunction (scalar R) (leftModule R M)).unit.app
            ((moduleEquivalence R).inverse.obj N)) ≫
        (moduleEquivalence R).functor.map
          ((Mod.internalHomOfEqualizer (scalar R) (leftModule R M)).map
            ((moduleEquivalence R).toAdjunction.unit.app
              (((Mod.relativeTensor (scalar R)).obj (leftModule R M)).obj
                ((moduleEquivalence R).inverse.obj N)))) := by
  let E := moduleEquivalence R
  let F := (Mod.relativeTensor (scalar R)).obj (leftModule R M)
  let G := Mod.internalHomOfEqualizer (scalar R) (leftModule R M)
  let a : F ⊣ G := Mod.relativeTensorInternalHomAdjunction (scalar R) (leftModule R M)
  let b : E.inverse ⋙ F ⊣ G ⋙ E.functor := E.symm.toAdjunction.comp a
  have h₁ := Adjunction.comp_unit_app b E.toAdjunction N
  have h₂ := Adjunction.comp_unit_app E.symm.toAdjunction a N
  change (stockAdjunction R M).unit.app N = b.unit.app N ≫
    E.functor.map (G.map (E.toAdjunction.unit.app (F.obj (E.inverse.obj N)))) at h₁
  change b.unit.app N = E.symm.toAdjunction.unit.app N ≫
    E.functor.map (a.unit.app (E.inverse.obj N)) at h₂
  rw [h₂] at h₁
  exact h₁.trans (Category.assoc _ _ _)

/-- The whole original stock counit keeps both conversion counits and balanced evaluation. -/
theorem stockAdjunction_counit_app (M N : RightModule R) :
    (stockAdjunction R M).counit.app N =
      (moduleEquivalence R).functor.map
        (((Mod.relativeTensor (scalar R)).obj (leftModule R M)).map
          ((moduleEquivalence R).symm.toAdjunction.counit.app
            ((Mod.internalHomOfEqualizer (scalar R) (leftModule R M)).obj
              ((moduleEquivalence R).inverse.obj N)))) ≫
        (moduleEquivalence R).functor.map
          ((Mod.relativeTensorInternalHomAdjunction (scalar R) (leftModule R M)).counit.app
            ((moduleEquivalence R).inverse.obj N)) ≫
        (moduleEquivalence R).toAdjunction.counit.app N := by
  let E := moduleEquivalence R
  let F := (Mod.relativeTensor (scalar R)).obj (leftModule R M)
  let G := Mod.internalHomOfEqualizer (scalar R) (leftModule R M)
  let a : F ⊣ G := Mod.relativeTensorInternalHomAdjunction (scalar R) (leftModule R M)
  let b : E.inverse ⋙ F ⊣ G ⋙ E.functor := E.symm.toAdjunction.comp a
  have h₁ := Adjunction.comp_counit_app b E.toAdjunction N
  have h₂ := Adjunction.comp_counit_app E.symm.toAdjunction a (E.inverse.obj N)
  change (stockAdjunction R M).counit.app N =
    E.functor.map (b.counit.app (E.inverse.obj N)) ≫ E.toAdjunction.counit.app N at h₁
  change b.counit.app (E.inverse.obj N) =
    F.map (E.symm.toAdjunction.counit.app (G.obj (E.inverse.obj N))) ≫
      a.counit.app (E.inverse.obj N) at h₂
  rw [h₂, E.functor.map_comp, Category.assoc] at h₁
  exact h₁

end CategoryTheory.RightModuleMappingEnd
