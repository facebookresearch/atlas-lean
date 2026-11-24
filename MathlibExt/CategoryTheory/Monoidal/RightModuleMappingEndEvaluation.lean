/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEndAdjunctionComponents

/-!
# Original balanced evaluation of the right-module mapping equalizer

The original quotient projection computes the actual balanced counit. Its
source inclusion is the full original action equalizer inclusion. Conversion
maps are reduced by their proved carrier laws after retaining the entire
unit and counit formulas.
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

/-- The actual relative tensor structure used by balanced evaluation. -/
local instance evaluationModuleMonoidal : MonoidalCategory (RightModule R) :=
  RightModuleFree.tensorMonoidal R

/-- The actual relative tensor symmetry used by balanced evaluation. -/
local instance evaluationModuleSymmetric : SymmetricCategory (RightModule R) :=
  RightModuleFree.tensorSymmetric R

variable [HasEqualizers C]

omit [HasEqualizers C] in
/-- Every actual left tensor map retains its entire original quotient projection. -/
@[reassoc]
theorem tensorLeft_map_π (M : RightModule R) {N N' : RightModule R} (g : N ⟶ N') :
    RightModuleFree.relativeTensorπ R M N ≫ ((tensorLeft M).map g).hom =
      (M.X ◁ g.hom) ≫ RightModuleFree.relativeTensorπ R M N' := by
  have hmap : RightModuleFree.relativeTensorMap R (𝟙 M) g = (tensorLeft M).map g := by
    change (𝟙 M) ⊗ₘ g = M ◁ g
    exact id_tensorHom M g
  rw [← hmap, RightModuleFree.relativeTensorMap_π]
  simp only [Mod.id_hom', tensorHom_def, id_whiskerRight, Category.id_comp]

omit [HasEqualizers C] in
/-- Every actual right tensor map retains its entire original quotient projection. -/
@[reassoc]
theorem tensorRight_map_π (M : RightModule R) {N N' : RightModule R} (g : N ⟶ N') :
    RightModuleFree.relativeTensorπ R N M ≫ ((tensorRight M).map g).hom =
      (g.hom ▷ M.X) ≫ RightModuleFree.relativeTensorπ R N' M := by
  have hmap : RightModuleFree.relativeTensorMap R g (𝟙 M) = (tensorRight M).map g := by
    change g ⊗ₘ (𝟙 M) = g ▷ M
    exact tensorHom_id g M
  rw [← hmap, RightModuleFree.relativeTensorMap_π]
  simp only [Mod.id_hom', tensorHom_id]

/-- The actual stock counit evaluates its whole original action equalizer inclusion. -/
@[reassoc]
theorem stockAdjunction_counit_π (M N : RightModule R) :
    RightModuleFree.relativeTensorπ R M ((stockFunctor R M).obj N) ≫
        ((stockAdjunction R M).counit.app N).hom =
      MonoidalClosed.uncurry (stockι R M N) := by
  let A := scalar R
  let E := moduleEquivalence R
  let F := (Mod.relativeTensor A).obj (leftModule R M)
  let H := (Mod.internalHomOfEqualizer A (leftModule R M)).obj (E.inverse.obj N)
  have hformula : RightModuleFree.relativeTensorπ R M ((stockFunctor R M).obj N) ≫
      ((stockAdjunction R M).counit.app N).hom =
      Mod.relativeTensorπ A (leftModule R M) (E.inverse.obj (E.functor.obj H)) ≫
        (F.map (E.unitIso.inv.app H)).hom ≫
          ((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).counit.app
            (E.inverse.obj N)).hom ≫ (E.counitIso.hom.app N).hom :=
    congrArg (fun f => RightModuleFree.relativeTensorπ R M ((stockFunctor R M).obj N) ≫
      f.hom) (stockAdjunction_counit_app R M N)
  have hcarrier : (M.X ◁ (E.unitIso.inv.app H).hom) = 𝟙 (M.X ⊗ H.X) :=
    (congrArg (fun f => M.X ◁ f) (moduleEquivalence_unit_inv R H)).trans
      (whiskerLeft_id M.X H.X)
  have hprojection :
      Mod.relativeTensorπ A (leftModule R M) (E.inverse.obj (E.functor.obj H)) ≫
        (F.map (E.unitIso.inv.app H)).hom = Mod.relativeTensorπ A (leftModule R M) H :=
    (Mod.relativeTensor_map_π A (leftModule R M) (E.unitIso.inv.app H)).trans
      ((congrArg (fun f => f ≫ Mod.relativeTensorπ A (leftModule R M) H) hcarrier).trans
        (Category.id_comp _))
  have hcounit := congrArg (fun f =>
    Mod.relativeTensorπ A (leftModule R M) (E.inverse.obj (E.functor.obj H)) ≫
      (F.map (E.unitIso.inv.app H)).hom ≫
        ((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).counit.app
          (E.inverse.obj N)).hom ≫ f) (moduleEquivalence_counit_hom R N)
  have hid := congrArg (fun f =>
    Mod.relativeTensorπ A (leftModule R M) (E.inverse.obj (E.functor.obj H)) ≫
      (F.map (E.unitIso.inv.app H)).hom ≫ f)
    (Category.comp_id ((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).counit.app
      (E.inverse.obj N)).hom)
  have hassoc := (Category.assoc
    (Mod.relativeTensorπ A (leftModule R M) (E.inverse.obj (E.functor.obj H)))
    (F.map (E.unitIso.inv.app H)).hom
    ((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).counit.app
      (E.inverse.obj N)).hom).symm
  have hbalanced := congrArg (fun f => f ≫
    ((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).counit.app
      (E.inverse.obj N)).hom) hprojection
  exact hformula.trans (hcounit.trans (hid.trans (hassoc.trans
    (hbalanced.trans (Mod.relativeTensorInternalHomAdjunction_counit_π A
      (leftModule R M) (E.inverse.obj N))))))

/-- The actual stock unit retains the entire original balanced projection after inclusion. -/
@[reassoc]
theorem stockAdjunction_unit_ι (M N : RightModule R) :
    ((stockAdjunction R M).unit.app N).hom ≫
        stockι R M ((tensorLeft M).obj N) =
      MonoidalClosed.curry (RightModuleFree.relativeTensorπ R M N) := by
  let A := scalar R
  let E := moduleEquivalence R
  let F := (Mod.relativeTensor A).obj (leftModule R M)
  let T := F.obj (E.inverse.obj N)
  have hformula : ((stockAdjunction R M).unit.app N).hom ≫
      stockι R M ((tensorLeft M).obj N) =
      ((E.counitIso.inv.app N).hom ≫
        ((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).unit.app
          (E.inverse.obj N)).hom ≫
        ((Mod.internalHomOfEqualizer A (leftModule R M)).map (E.unitIso.hom.app T)).hom) ≫
        Mod.internalHomι A (leftModule R M) (E.inverse.obj (E.functor.obj T)) :=
    congrArg (fun f => f.hom ≫ stockι R M ((tensorLeft M).obj N))
      (stockAdjunction_unit_app R M N)
  have hcarrier : (ihom M.X).map (E.unitIso.hom.app T).hom =
      𝟙 ((ihom M.X).obj T.X) :=
    (congrArg (fun f => (ihom M.X).map f) (moduleEquivalence_unit_hom R T)).trans
      ((ihom M.X).map_id T.X)
  have hinclusion : ((Mod.internalHomOfEqualizer A (leftModule R M)).map
        (E.unitIso.hom.app T)).hom ≫
      Mod.internalHomι A (leftModule R M) (E.inverse.obj (E.functor.obj T)) =
      Mod.internalHomι A (leftModule R M) T :=
    (Mod.internalHomMap A (leftModule R M) (E.unitIso.hom.app T)).trans
      ((congrArg (fun f => Mod.internalHomι A (leftModule R M) T ≫ f) hcarrier).trans
        (Category.comp_id _))
  have hcounit := congrArg (fun f =>
    (f ≫ ((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).unit.app
      (E.inverse.obj N)).hom ≫
      ((Mod.internalHomOfEqualizer A (leftModule R M)).map (E.unitIso.hom.app T)).hom) ≫
      Mod.internalHomι A (leftModule R M) (E.inverse.obj (E.functor.obj T)))
    (moduleEquivalence_counit_inv R N)
  have hid := congrArg (fun f => f ≫
    Mod.internalHomι A (leftModule R M) (E.inverse.obj (E.functor.obj T)))
    (Category.id_comp
      (((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).unit.app
        (E.inverse.obj N)).hom ≫
        ((Mod.internalHomOfEqualizer A (leftModule R M)).map (E.unitIso.hom.app T)).hom))
  have hassoc := Category.assoc
    ((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).unit.app
      (E.inverse.obj N)).hom
    ((Mod.internalHomOfEqualizer A (leftModule R M)).map (E.unitIso.hom.app T)).hom
    (Mod.internalHomι A (leftModule R M) (E.inverse.obj (E.functor.obj T)))
  have hbalanced := congrArg (fun f =>
    ((Mod.relativeTensorInternalHomAdjunction A (leftModule R M)).unit.app
      (E.inverse.obj N)).hom ≫ f) hinclusion
  exact hformula.trans (hcounit.trans (hid.trans (hassoc.trans
    (hbalanced.trans (Mod.relativeTensorInternalHomAdjunction_unit_ι A
      (leftModule R M) (E.inverse.obj N))))))

/-- The actual source left unit keeps the original full source equalizer inclusion. -/
@[reassoc]
theorem leftAdjunction_unit_ι (M N : RightModule R) :
    ((leftAdjunction R M).unit.app N).hom ≫
        ι R M ((tensorLeft M).obj N) =
      MonoidalClosed.curry (RightModuleFree.relativeTensorπ R M N) := by
  exact (Category.assoc ((stockAdjunction R M).unit.app N).hom
    (stockComparison R M ((tensorLeft M).obj N)).inv
    (ι R M ((tensorLeft M).obj N))).trans
    ((congrArg (fun f => ((stockAdjunction R M).unit.app N).hom ≫ f)
      (stockComparison_inv_ι R M ((tensorLeft M).obj N))).trans
      (stockAdjunction_unit_ι R M N))

/-- The actual source left counit is evaluation of the whole source action equalizer. -/
@[reassoc]
theorem leftAdjunction_counit_π (M N : RightModule R) :
    RightModuleFree.relativeTensorπ R M ((functor R M).obj N) ≫
        ((leftAdjunction R M).counit.app N).hom =
      MonoidalClosed.uncurry (ι R M N) := by
  have hprojection : RightModuleFree.relativeTensorπ R M ((functor R M).obj N) ≫
      ((tensorLeft M).map (moduleComparison R M N).hom).hom ≫
        ((stockAdjunction R M).counit.app N).hom =
      (M.X ◁ (stockComparison R M N).hom) ≫
        RightModuleFree.relativeTensorπ R M ((stockFunctor R M).obj N) ≫
          ((stockAdjunction R M).counit.app N).hom :=
    tensorLeft_map_π_assoc R M (moduleComparison R M N).hom
      ((stockAdjunction R M).counit.app N).hom
  have hstock := congrArg (fun f => (M.X ◁ (stockComparison R M N).hom) ≫ f)
    (stockAdjunction_counit_π R M N)
  have hclosed := (MonoidalClosed.uncurry_natural_left
    (stockComparison R M N).hom (stockι R M N)).symm
  have hcomparison := congrArg MonoidalClosed.uncurry (stockComparison_hom_ι R M N)
  exact hprojection.trans (hstock.trans (hclosed.trans hcomparison))

/-- The full source-oriented unit retains its original leading ambient tensor braid. -/
@[reassoc]
theorem adjunction_unit_ι (M N : RightModule R) :
    ((adjunction R M).unit.app N).hom ≫
        ι R M ((tensorRight M).obj N) =
      MonoidalClosed.curry
        ((β_ M.X N.X).hom ≫ RightModuleFree.relativeTensorπ R N M) := by
  calc
    _ = ((leftAdjunction R M).unit.app N).hom ≫
        (((functor R M).map (β_ M N).hom).hom ≫
          ι R M ((tensorRight M).obj N)) := Category.assoc _ _ _
    _ = ((leftAdjunction R M).unit.app N).hom ≫
        (ι R M ((tensorLeft M).obj N) ≫ (ihom M.X).map (β_ M N).hom.hom) :=
      congrArg (fun f => ((leftAdjunction R M).unit.app N).hom ≫ f)
        (map_ι R M (β_ M N).hom)
    _ = (((leftAdjunction R M).unit.app N).hom ≫
        ι R M ((tensorLeft M).obj N)) ≫
          (ihom M.X).map (β_ M N).hom.hom := (Category.assoc _ _ _).symm
    _ = MonoidalClosed.curry (RightModuleFree.relativeTensorπ R M N) ≫
        (ihom M.X).map (β_ M N).hom.hom :=
      congrArg (fun f => f ≫ (ihom M.X).map (β_ M N).hom.hom)
        (leftAdjunction_unit_ι R M N)
    _ = MonoidalClosed.curry (RightModuleFree.relativeTensorπ R M N ≫
        (β_ M N).hom.hom) := (MonoidalClosed.curry_natural_right _ _).symm
    _ = _ := congrArg MonoidalClosed.curry
      (RightModuleFree.relativeTensorBraiding_hom_π R M N)

/-- The full source-oriented counit retains its original leading ambient tensor braid. -/
@[reassoc]
theorem adjunction_counit_π (M N : RightModule R) :
    RightModuleFree.relativeTensorπ R ((functor R M).obj N) M ≫
        ((adjunction R M).counit.app N).hom =
      (β_ ((functor R M).obj N).X M.X).hom ≫ MonoidalClosed.uncurry (ι R M N) := by
  calc
    _ = RightModuleFree.relativeTensorπ R ((functor R M).obj N) M ≫
        (β_ ((functor R M).obj N) M).hom.hom ≫
          ((leftAdjunction R M).counit.app N).hom :=
      congrArg (fun f => RightModuleFree.relativeTensorπ R ((functor R M).obj N) M ≫
        f.hom ≫ ((leftAdjunction R M).counit.app N).hom)
        (SymmetricCategory.braiding_swap_eq_inv_braiding M ((functor R M).obj N)).symm
    _ = (RightModuleFree.relativeTensorπ R ((functor R M).obj N) M ≫
        (β_ ((functor R M).obj N) M).hom.hom) ≫
          ((leftAdjunction R M).counit.app N).hom := (Category.assoc _ _ _).symm
    _ = ((β_ ((functor R M).obj N).X M.X).hom ≫
        RightModuleFree.relativeTensorπ R M ((functor R M).obj N)) ≫
          ((leftAdjunction R M).counit.app N).hom :=
      congrArg (fun f => f ≫ ((leftAdjunction R M).counit.app N).hom)
        (RightModuleFree.relativeTensorBraiding_hom_π R ((functor R M).obj N) M)
    _ = (β_ ((functor R M).obj N).X M.X).hom ≫
        (RightModuleFree.relativeTensorπ R M ((functor R M).obj N) ≫
          ((leftAdjunction R M).counit.app N).hom) := Category.assoc _ _ _
    _ = _ := congrArg (fun f => (β_ ((functor R M).obj N).X M.X).hom ≫ f)
      (leftAdjunction_counit_π R M N)

end CategoryTheory.RightModuleMappingEnd
