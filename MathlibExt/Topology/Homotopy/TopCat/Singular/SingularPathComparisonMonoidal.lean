/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathComparison
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Monoidal characteristic of the singular path comparison

The uncurried singular/free-path comparison is the canonical composite built
from the singular interval, the lax-monoidal product map for the singular
functor, the tensor-to-chosen-product comparison, and literal interval
evaluation.

The proof relates the Cartesian tensor comparison for geometric realization
to the chosen binary-product comparison used by
`SSet.singularPathComparisonAdjunct`, then applies monoidal adjunction
compatibility.  The comparison bridge and its projection machinery remain
private.

This file proves only the exact monoidal characteristic.  It defines no
endpoint equation, based-path or loop comparison, inverse, isomorphism, weak
equivalence, or Q/S result.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial
  Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped Simplicial

universe v₁ v₂ u₁ u₂ u

private noncomputable def prodFunctorFst
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    (X Y : C) : (Limits.prod.functor.obj X).obj Y ⟶ X :=
  Limits.prod.fst

private noncomputable def prodFunctorSnd
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    (X Y : C) : (Limits.prod.functor.obj X).obj Y ⟶ Y :=
  Limits.prod.snd

@[reassoc]
private theorem prodFunctor_obj_map_fst
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    (X : C) {A B : C} (g : A ⟶ B) :
    (Limits.prod.functor.obj X).map g ≫ prodFunctorFst X B =
      prodFunctorFst X A := by
  unfold prodFunctorFst Limits.prod.functor
  rw [Limits.prod.map_fst, Category.comp_id]

@[reassoc]
private theorem prodFunctor_obj_map_snd
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    (X : C) {A B : C} (g : A ⟶ B) :
    (Limits.prod.functor.obj X).map g ≫ prodFunctorSnd X B =
      prodFunctorSnd X A ≫ g := by
  unfold prodFunctorSnd Limits.prod.functor
  rw [Limits.prod.map_snd]

@[reassoc]
private theorem prodFunctor_map_app_fst
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {A B : C} (f : A ⟶ B) (T : C) :
    (Limits.prod.functor.map f).app T ≫ prodFunctorFst B T =
      prodFunctorFst A T ≫ f := by
  unfold prodFunctorFst Limits.prod.functor
  rw [Limits.prod.map_fst]

@[reassoc]
private theorem prodFunctor_map_app_snd
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {A B : C} (f : A ⟶ B) (T : C) :
    (Limits.prod.functor.map f).app T ≫ prodFunctorSnd B T =
      prodFunctorSnd A T := by
  unfold prodFunctorSnd Limits.prod.functor
  rw [Limits.prod.map_snd, Category.comp_id]

@[reassoc]
private theorem prodComparisonNatTrans_app_fst
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasBinaryProducts D]
    (F : C ⥤ D) (K L : C) :
    (Limits.prodComparisonNatTrans F K).app L ≫
        prodFunctorFst (F.obj K) (F.obj L) =
      F.map (prodFunctorFst K L) := by
  unfold Limits.prodComparisonNatTrans prodFunctorFst Limits.prod.functor
  exact Limits.prodComparison_fst _ _ _

@[reassoc]
private theorem prodComparisonNatTrans_app_snd
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasBinaryProducts D]
    (F : C ⥤ D) (K L : C) :
    (Limits.prodComparisonNatTrans F K).app L ≫
        prodFunctorSnd (F.obj K) (F.obj L) =
      F.map (prodFunctorSnd K L) := by
  unfold Limits.prodComparisonNatTrans prodFunctorSnd Limits.prod.functor
  exact Limits.prodComparison_snd _ _ _

@[reassoc]
private theorem tensorLeftIsoProd_hom_fst
    {C : Type u₁} [Category.{v₁} C]
    [CartesianMonoidalCategory C] [HasBinaryProducts C]
    (X Y : C) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app Y ≫
        prodFunctorFst X Y =
      CartesianMonoidalCategory.fst X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.left⟩

@[reassoc]
private theorem tensorLeftIsoProd_hom_snd
    {C : Type u₁} [Category.{v₁} C]
    [CartesianMonoidalCategory C] [HasBinaryProducts C]
    (X Y : C) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app Y ≫
        prodFunctorSnd X Y =
      CartesianMonoidalCategory.snd X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.right⟩

@[reassoc]
private theorem tensorLeftIsoProd_inv_fst
    {C : Type u₁} [Category.{v₁} C]
    [CartesianMonoidalCategory C] [HasBinaryProducts C]
    (X Y : C) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app Y ≫
        CartesianMonoidalCategory.fst X Y =
      prodFunctorFst X Y :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.left⟩

@[reassoc]
private theorem tensorLeftIsoProd_inv_snd
    {C : Type u₁} [Category.{v₁} C]
    [CartesianMonoidalCategory C] [HasBinaryProducts C]
    (X Y : C) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app Y ≫
        CartesianMonoidalCategory.snd X Y =
      prodFunctorSnd X Y :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.right⟩

/-- The Cartesian tensor comparison for realization agrees with the chosen
binary-product comparison after the canonical tensor/product bridges. -/
private theorem toTop_tensor_prodComparison
    {K L : SSet.{u}} {X Y : TopCat.{u}}
    (f : SSet.toTop.obj K ⟶ X) (g : SSet.toTop.obj L ⟶ Y) :
    CartesianMonoidalCategory.prodComparison SSet.toTop K L ≫
        (f ⊗ₘ g) =
      SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd K).hom.app L) ≫
        (Limits.prodComparisonNatTrans SSet.toTop K).app L ≫
        (Limits.prod.functor.map f).app (SSet.toTop.obj L) ≫
        (Limits.prod.functor.obj X).map g ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app Y := by
  apply CartesianMonoidalCategory.hom_ext
  · calc
      (CartesianMonoidalCategory.prodComparison SSet.toTop K L ≫
          (f ⊗ₘ g)) ≫ CartesianMonoidalCategory.fst X Y =
        CartesianMonoidalCategory.prodComparison SSet.toTop K L ≫
          ((f ⊗ₘ g) ≫ CartesianMonoidalCategory.fst X Y) := by
            rw [Category.assoc]
      _ = CartesianMonoidalCategory.prodComparison SSet.toTop K L ≫
          (CartesianMonoidalCategory.fst _ _ ≫ f) := by
            rw [CartesianMonoidalCategory.tensorHom_fst]
      _ = SSet.toTop.map (CartesianMonoidalCategory.fst K L) ≫ f := by
            rw [← Category.assoc,
              CartesianMonoidalCategory.prodComparison_fst]
      _ = SSet.toTop.map
            ((CartesianMonoidalCategory.tensorLeftIsoProd K).hom.app L) ≫
          (Limits.prodComparisonNatTrans SSet.toTop K).app L ≫
          (Limits.prod.functor.map f).app (SSet.toTop.obj L) ≫
          (Limits.prod.functor.obj X).map g ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app Y ≫
          CartesianMonoidalCategory.fst X Y := by
            rw [tensorLeftIsoProd_inv_fst]
            rw [prodFunctor_obj_map_fst]
            rw [prodFunctor_map_app_fst]
            rw [prodComparisonNatTrans_app_fst_assoc]
            rw [← SSet.toTop.map_comp_assoc,
              tensorLeftIsoProd_hom_fst]
  · calc
      (CartesianMonoidalCategory.prodComparison SSet.toTop K L ≫
          (f ⊗ₘ g)) ≫ CartesianMonoidalCategory.snd X Y =
        CartesianMonoidalCategory.prodComparison SSet.toTop K L ≫
          ((f ⊗ₘ g) ≫ CartesianMonoidalCategory.snd X Y) := by
            rw [Category.assoc]
      _ = CartesianMonoidalCategory.prodComparison SSet.toTop K L ≫
          (CartesianMonoidalCategory.snd _ _ ≫ g) := by
            rw [CartesianMonoidalCategory.tensorHom_snd]
      _ = SSet.toTop.map (CartesianMonoidalCategory.snd K L) ≫ g := by
            rw [← Category.assoc,
              CartesianMonoidalCategory.prodComparison_snd]
      _ = SSet.toTop.map
            ((CartesianMonoidalCategory.tensorLeftIsoProd K).hom.app L) ≫
          (Limits.prodComparisonNatTrans SSet.toTop K).app L ≫
          (Limits.prod.functor.map f).app (SSet.toTop.obj L) ≫
          (Limits.prod.functor.obj X).map g ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app Y ≫
          CartesianMonoidalCategory.snd X Y := by
            rw [tensorLeftIsoProd_inv_snd]
            rw [prodFunctor_obj_map_snd]
            rw [prodFunctor_map_app_snd_assoc]
            rw [prodComparisonNatTrans_app_snd_assoc]
            rw [← SSet.toTop.map_comp_assoc,
              tensorLeftIsoProd_hom_snd]

namespace SSet

local instance : SSet.toTop.{u}.OplaxMonoidal :=
  sSetTopAdj.leftAdjointOplaxMonoidal

private theorem toSSetObjI_adjunct :
    SSet.toTop.map SSet.stdSimplex.toSSetObjI.{u} ≫
        sSetTopAdj.counit.app TopCat.I.{u} =
      SSet.stdSimplex.toTopObjIsoI.hom := by
  calc
    SSet.toTop.map SSet.stdSimplex.toSSetObjI.{u} ≫
        sSetTopAdj.counit.app TopCat.I.{u} =
      (sSetTopAdj.homEquiv (Δ[1] : SSet.{u}) TopCat.I.{u}).symm
        SSet.stdSimplex.toSSetObjI :=
          (sSetTopAdj.homEquiv_counit
            (Δ[1] : SSet.{u}) TopCat.I.{u}
            SSet.stdSimplex.toSSetObjI).symm
    _ = SSet.stdSimplex.toTopObjIsoI.hom := by
      unfold SSet.stdSimplex.toSSetObjI
      exact (sSetTopAdj.homEquiv _ _).symm_apply_apply _

/-- The uncurried singular path comparison is the canonical singular image
of interval evaluation through the lax-monoidal product map. -/
theorem singularPathComparison_uncurry_lax
    (X : Type u) [TopologicalSpace X] :
    MonoidalClosed.uncurry (singularPathComparison X) =
      (SSet.stdSimplex.toSSetObjI.{u} ▷
          TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ≫
        μ TopCat.toSSet TopCat.I.{u}
          (TopCat.of C(unitInterval, X)) ≫
        TopCat.toSSet.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app
              (TopCat.of C(unitInterval, X))) ≫
        TopCat.toSSet.map
          ((TopCat.intervalContinuousMapEvaluation X) :
            (Limits.prod.functor.obj TopCat.I.{u}).obj
                (TopCat.of C(unitInterval, X)) ⟶
              TopCat.of X) := by
  let P := TopCat.of C(unitInterval, X)
  let A := TopCat.toSSet.obj P
  let i := SSet.stdSimplex.toSSetObjI.{u}
  let e := (CartesianMonoidalCategory.tensorLeftIsoProd
    TopCat.I.{u}).hom.app P
  let ev : (Limits.prod.functor.obj TopCat.I.{u}).obj P ⟶
      TopCat.of X := TopCat.intervalContinuousMapEvaluation X
  have hAdjunct :
      SSet.toTop.map
          (sSetTopAdj.homEquiv _ _
            (singularPathComparisonAdjunct X)) ≫
          sSetTopAdj.counit.app (TopCat.of X) =
        singularPathComparisonAdjunct X := by
    calc
      SSet.toTop.map
            (sSetTopAdj.homEquiv _ _
              (singularPathComparisonAdjunct X)) ≫
          sSetTopAdj.counit.app (TopCat.of X) =
        (sSetTopAdj.homEquiv _ _).symm
          (sSetTopAdj.homEquiv _ _
            (singularPathComparisonAdjunct X)) :=
              (sSetTopAdj.homEquiv_counit _ _ _).symm
      _ = singularPathComparisonAdjunct X :=
        (sSetTopAdj.homEquiv _ _).symm_apply_apply _
  have hRight :
      SSet.toTop.map
          ((i ▷ A) ≫ μ TopCat.toSSet TopCat.I.{u} P ≫
            TopCat.toSSet.map e ≫ TopCat.toSSet.map ev) ≫
          sSetTopAdj.counit.app (TopCat.of X) =
        singularPathComparisonAdjunct X := by
    simp only [Functor.map_comp, Category.assoc]
    have hEv := sSetTopAdj.counit.naturality ev
    have hE := sSetTopAdj.counit.naturality e
    simp only [Functor.comp_map, Functor.id_map] at hEv hE
    rw [hEv]
    slice_lhs 3 4 => rw [hE]
    have hMu := sSetTopAdj.map_μ_comp_counit_app_tensor
      TopCat.I.{u} P
    change SSet.toTop.map (μ TopCat.toSSet TopCat.I.{u} P) ≫
        sSetTopAdj.counit.app ((tensorLeft TopCat.I.{u}).obj P) = _ at hMu
    simp only [Category.assoc]
    slice_lhs 2 3 =>
      rw [hMu]
    rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
    simp only [Category.assoc]
    slice_lhs 1 2 =>
      rw [CartesianMonoidalCategory.prodComparison_natural_whiskerRight]
    have hi : SSet.toTop.map i ≫
        sSetTopAdj.counit.app TopCat.I.{u} =
          SSet.stdSimplex.toTopObjIsoI.hom := by
      exact toSSetObjI_adjunct
    simp only [Category.assoc]
    slice_lhs 2 3 =>
      rw [← tensorHom_id, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, hi]
    simp only [Category.assoc]
    slice_lhs 1 2 =>
      rw [toTop_tensor_prodComparison]
    simp only [Functor.id_obj]
    slice_lhs 5 6 =>
      change
        (CartesianMonoidalCategory.tensorLeftIsoProd
          TopCat.I.{u}).inv.app P ≫
          (CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app P
      rw [Iso.inv_hom_id_app]
    simp only [Category.id_comp]
    rfl
  apply (sSetTopAdj.homEquiv
    ((Δ[1] : SSet.{u}) ⊗ A) (TopCat.of X)).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [singularPathComparison_uncurry, hAdjunct]
  exact hRight.symm

end SSet
