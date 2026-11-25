/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEnd
public import MathlibExt.CategoryTheory.Monoidal.Mod.FreeInternalHom

/-!
# Original action and source variance of the right-module mapping equalizer

The actual source equalizer action is linear into the original auxiliary
internal-Hom module. The source map is a genuine module morphism and its
entire underlying map is the original raw equalizer precomposition. Together
with the already constructed target functor, these maps give the full
source/target bifunctor without assuming a source-map dictionary.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory MonoidalOpposite
open CategoryTheory.CommutativeModuleConversion
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.RightModuleMappingEnd

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C]
  (R : C) [MonObj R] [IsCommMonObj R]

/-- The original auxiliary right module on the actual ambient internal Hom. -/
abbrev auxiliaryModule (M N : RightModule R) : RightModule R :=
  toRight R (Mod.internalHomAuxiliary (scalar R) M.X (leftModule R N))

/-- Its entire right action is the original braiding followed by the actual auxiliary action. -/
abbrev auxiliaryRightAction (M N : RightModule R) : ambient R M N ⊗ R ⟶ ambient R M N :=
  (auxiliaryModule R M N).action

/-- The original stock equalizer inclusion retains its whole actual right action. -/
@[reassoc]
theorem stockRightAction_stockι (M N : RightModule R) :
    (stockRightHom R M N).action ≫ stockι R M N =
      (stockι R M N ▷ R) ≫ auxiliaryRightAction R M N := by
  have h := Mod.internalHomι_smul (scalar R) (leftModule R M) (leftModule R N)
  change (stockHom R M N).mod.smul ≫ stockι R M N =
    (R ◁ stockι R M N) ≫
      (Mod.internalHomAuxiliary (scalar R) M.X (leftModule R N)).mod.smul at h
  change ((β_ (stockHom R M N).X R).hom ≫ (stockHom R M N).mod.smul) ≫ stockι R M N =
    (stockι R M N ▷ R) ≫ (β_ (ambient R M N) R).hom ≫
      (Mod.internalHomAuxiliary (scalar R) M.X (leftModule R N)).mod.smul
  rw [Category.assoc, h]
  rw [← Category.assoc, ← braiding_naturality_left]
  exact Category.assoc _ _ _

/-- The entire source Mapping_R action is the original ambient action after its actual inclusion. -/
@[reassoc]
theorem moduleObject_action_ι (M N : RightModule R) :
    (moduleObject R M N).action ≫ ι R M N =
      (ι R M N ▷ R) ≫ auxiliaryRightAction R M N := by
  rw [moduleObject_action]
  simp only [Category.assoc]
  rw [stockComparison_inv_ι,
    stockRightAction_stockι]
  rw [← comp_whiskerRight_assoc, stockComparison_hom_ι]

omit [HasEqualizers C] in
/-- The original auxiliary action retains the full source argument shuffle, evaluation and
the converted actual target right action. -/
theorem auxiliaryRightAction_eq (M N : RightModule R) :
    auxiliaryRightAction R M N = (β_ (ambient R M N) R).hom ≫
      MonoidalClosed.curry
        ((α_ M.X R (ambient R M N)).inv ≫
          ((β_ M.X R).hom ▷ ambient R M N) ≫
          (α_ R M.X (ambient R M N)).hom ≫
          (R ◁ (ihom.ev M.X).app N.X) ≫ (β_ R N.X).hom ≫ N.action) := by
  change (β_ (ambient R M N) R).hom ≫
      (Mod.internalHomAuxiliary (scalar R) M.X (leftModule R N)).mod.smul = _
  rw [Mod.internalHomAuxiliary_smul]
  rfl

/-- The actual target module map is precisely the original raw action-equalizer postcomposition. -/
theorem map_hom (M : RightModule R) {N N' : RightModule R} (f : N ⟶ N') :
    ((functor R M).map f).hom = post R M f := by
  apply hom_ext R M N'
  rw [map_ι, post_ι]

variable [HasCoequalizers C]

/-- The action comparison uses the original monoidal structure on left modules. -/
local instance leftModuleMonoidal : MonoidalCategory (Mod C R) :=
  Mod.instMonoidalCategory (scalar R)

/-- The same original left-module tensor has its stock closed structure. -/
local instance leftModuleClosed : MonoidalClosed (Mod C R) :=
  Mod.instMonoidalClosed (scalar R)

/-- Source precomposition on the whole original stock right-module Hom. -/
def stockSourceMap {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    stockRightHom R M N ⟶ stockRightHom R M' N :=
  toRightMap R ((MonoidalClosed.pre (toLeftMap R f)).app (leftModule R N))

/-- Stock source precomposition retains the actual original full carrier arrow. -/
@[reassoc]
theorem stockSourceMap_ι {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (stockSourceMap R f N).hom ≫ stockι R M' N =
      stockι R M N ≫ (MonoidalClosed.pre f.hom).app N.X := by
  have h := Mod.FreeInternalHom.precompose_projection
    (scalar R) (toLeftMap R f) (leftModule R N)
  rw [toLeftMap_hom] at h
  unfold stockSourceMap
  rw [toRightMap_hom]
  exact h

/-- Every source module morphism acts on the actual Mapping_R source equalizer as a whole
right-module morphism. -/
def sourceMap {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (functor R M).obj N ⟶ (functor R M').obj N :=
  (moduleComparison R M N).hom ≫ stockSourceMap R f N ≫ (moduleComparison R M' N).inv

/-- Every source map has the literal original ambient internal-Hom precomposition. -/
@[reassoc]
theorem sourceMap_ι {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (sourceMap R f N).hom ≫ ι R M' N =
      ι R M N ≫ (MonoidalClosed.pre f.hom).app N.X := by
  change ((stockComparison R M N).hom ≫ (stockSourceMap R f N).hom ≫
    (stockComparison R M' N).inv) ≫ ι R M' N = _
  rw [Category.assoc, Category.assoc, stockComparison_inv_ι,
    stockSourceMap_ι, ← Category.assoc, stockComparison_hom_ι]

/-- The genuine source-module arrow has the entire original raw source equalizer map. -/
theorem sourceMap_hom {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    (sourceMap R f N).hom = pre R f N := by
  apply hom_ext R M' N
  rw [sourceMap_ι, pre_ι]

/-- The original source identity gives the entire mapping-module identity. -/
@[simp]
theorem sourceMap_id (M N : RightModule R) : sourceMap R (𝟙 M) N = 𝟙 ((functor R M).obj N) := by
  apply Mod.hom_ext
  rw [sourceMap_hom, pre_id]
  rfl

/-- Source precomposition retains the full original contravariant order of module arrows. -/
theorem sourceMap_comp {M M' M'' : RightModule R} (f : M' ⟶ M) (g : M'' ⟶ M')
    (N : RightModule R) : sourceMap R (g ≫ f) N = sourceMap R f N ≫ sourceMap R g N := by
  apply Mod.hom_ext
  rw [sourceMap_hom, Mod.comp_hom', sourceMap_hom, sourceMap_hom, pre_comp]

/-- Both actual variances commute on the entire original source mapping module. -/
theorem sourceMap_naturality {M M' N N' : RightModule R} (f : M' ⟶ M) (g : N ⟶ N') :
    (functor R M).map g ≫ sourceMap R f N' = sourceMap R f N ≫ (functor R M').map g := by
  apply Mod.hom_ext
  rw [Mod.comp_hom', Mod.comp_hom', map_hom, map_hom, sourceMap_hom, sourceMap_hom]
  exact (pre_post R f g).symm

/-- Every original full source map gives its genuine target-natural mapping transformation. -/
def sourceNatTrans {M M' : RightModule R} (f : M' ⟶ M) : functor R M ⟶ functor R M' where
  app := sourceMap R f
  naturality _ _ g := sourceMap_naturality R f g

/-- The complete original source and target maps form a lawful right-module mapping bifunctor. -/
def bifunctor : (RightModule R)ᵒᵖ ⥤ (RightModule R ⥤ RightModule R) where
  obj M := functor R M.unop
  map f := sourceNatTrans R f.unop
  map_id M := by
    apply NatTrans.ext
    funext N
    exact sourceMap_id R M.unop N
  map_comp f g := by
    apply NatTrans.ext
    funext N
    exact sourceMap_comp R f.unop g.unop N

end CategoryTheory.RightModuleMappingEnd
