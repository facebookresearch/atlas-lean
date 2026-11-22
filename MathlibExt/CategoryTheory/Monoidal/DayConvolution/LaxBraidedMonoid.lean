/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import
  MathlibExt.CategoryTheory.Monoidal.DayConvolution.DayFunctorClosedSymmetric

/-!
# Day monoids from lax monoidal functors

A lax monoidal functor determines a monoid for Day convolution. When the
source is braided, the target is symmetric, and the functor is lax braided,
this monoid is commutative.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.DayConvolution
open scoped CategoryTheory.MonoidalCategory.DayFunctor
open scoped ExternalProduct MonObj

namespace CategoryTheory.MonoidalCategory.DayFunctor

open LawfulDayConvolutionMonoidalCategoryStruct

variable {C : Type u₁} [Category.{v₁} C]
variable {V : Type u₂} [Category.{v₂} V]
variable [MonoidalCategory C] [MonoidalCategory V]

variable
    [∀ (F G : C ⥤ V),
      (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} (𝟙_ C)).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} (𝟙_ V))]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod
        (Functor.fromPUnit.{0} (𝟙_ C))) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

private theorem monObjOfLaxMonoidal_one_mul
    (F : C ⥤ V) [F.LaxMonoidal] :
    let μNat : F ⊠ F ⟶ tensor C ⋙ F :=
      { app := fun p ↦ Functor.LaxMonoidal.μ F p.1 p.2
        naturality := by
          rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
          simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
            tensor_map, ← tensorHom_def] using
            Functor.LaxMonoidal.μ_natural F f g }
    (DayFunctor.unitDesc (Functor.LaxMonoidal.ε F) ▷ DayFunctor.mk F) ≫
        DayFunctor.tensorDesc μNat =
      (λ_ (DayFunctor.mk F)).hom := by
  dsimp only
  apply DayFunctor.tensor_hom_ext
  intro X Y
  let M := DayFunctor.mk F
  let one : 𝟙_ (C ⊛⥤ V) ⟶ M :=
    DayFunctor.unitDesc (Functor.LaxMonoidal.ε F)
  let μNat : F ⊠ F ⟶ tensor C ⋙ F :=
    { app := fun p ↦ Functor.LaxMonoidal.μ F p.1 p.2
      naturality := by
        rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
        simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
          tensor_map, ← tensorHom_def] using
          Functor.LaxMonoidal.μ_natural F f g }
  let mul : M ⊗ M ⟶ M := DayFunctor.tensorDesc μNat
  let L :
      (𝟙_ (C ⊛⥤ V)).functor ⋙ tensorRight (F.obj Y) ⟶
        tensorRight Y ⋙ F :=
    { app := fun U ↦
        (DayFunctor.η (𝟙_ (C ⊛⥤ V)) M).app (U, Y) ≫
          (((one ▷ M) ≫ mul).natTrans.app (U ⊗ Y))
      naturality := by
        intro U U' f
        simp only [Functor.comp_map]
        rw [show (tensorRight (F.obj Y)).map
            ((𝟙_ (C ⊛⥤ V)).functor.map f) =
          (𝟙_ (C ⊛⥤ V)).functor.map f ▷ F.obj Y by rfl]
        rw [show (tensorRight Y).map f = f ▷ Y by rfl]
        have hη := (DayFunctor.η (𝟙_ (C ⊛⥤ V)) M).naturality
          ((f, 𝟙 Y) : (U, Y) ⟶ (U', Y))
        simp only [externalProductBifunctor_obj_map, Functor.map_id,
          whiskerLeft_id, Category.comp_id, Functor.comp_map, tensor_map,
          tensorHom_id] at hη
        rw [← Category.assoc, hη, Category.assoc]
        rw [((one ▷ M) ≫ mul).natTrans.naturality (f ▷ Y)]
        dsimp only [M]
        simp only [Category.assoc] }
  let R :
      (𝟙_ (C ⊛⥤ V)).functor ⋙ tensorRight (F.obj Y) ⟶
        tensorRight Y ⋙ F :=
    { app := fun U ↦
        (DayFunctor.η (𝟙_ (C ⊛⥤ V)) M).app (U, Y) ≫
          ((λ_ M).hom.natTrans.app (U ⊗ Y))
      naturality := by
        intro U U' f
        simp only [Functor.comp_map]
        rw [show (tensorRight (F.obj Y)).map
            ((𝟙_ (C ⊛⥤ V)).functor.map f) =
          (𝟙_ (C ⊛⥤ V)).functor.map f ▷ F.obj Y by rfl]
        rw [show (tensorRight Y).map f = f ▷ Y by rfl]
        have hη := (DayFunctor.η (𝟙_ (C ⊛⥤ V)) M).naturality
          ((f, 𝟙 Y) : (U, Y) ⟶ (U', Y))
        simp only [externalProductBifunctor_obj_map, Functor.map_id,
          whiskerLeft_id, Category.comp_id, Functor.comp_map, tensor_map,
          tensorHom_id] at hη
        rw [← Category.assoc, hη, Category.assoc]
        rw [(λ_ M).hom.natTrans.naturality (f ▷ Y)]
        dsimp only [M]
        simp only [Category.assoc] }
  let E : Functor.LeftExtension
      (Functor.fromPUnit.{0} (𝟙_ C))
      (Functor.fromPUnit.{0} (𝟙_ V)) :=
    Functor.LeftExtension.mk (𝟙_ (C ⊛⥤ V)).functor
      (DayFunctor.νNatTrans C V)
  let EY := (Functor.LeftExtension.postcompose₂
    (Functor.fromPUnit.{0} (𝟙_ C))
    (Functor.fromPUnit.{0} (𝟙_ V))
    (tensorRight (F.obj Y))).obj E
  have hE : E.IsPointwiseLeftKanExtension :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit
      C V (C ⊛⥤ V)
  have hEY : EY.IsPointwiseLeftKanExtension :=
    hE.postcompose (tensorRight (F.obj Y))
  let EYC : Functor.LeftExtension
      (Functor.fromPUnit.{0} (𝟙_ C))
      (Functor.fromPUnit.{0} (𝟙_ V) ⋙ tensorRight (F.obj Y)) :=
    Functor.LeftExtension.mk
      ((𝟙_ (C ⊛⥤ V)).functor ⋙ tensorRight (F.obj Y))
      (Functor.whiskerRight (DayFunctor.νNatTrans C V)
          (tensorRight (F.obj Y)) ≫
        (Functor.associator _ _ _).hom)
  let e : EY ≅ EYC :=
    Functor.LeftExtension.postcompose₂ObjMkIso
      (tensorRight (F.obj Y)) (DayFunctor.νNatTrans C V)
  have hEYC : EYC.IsPointwiseLeftKanExtension :=
    (Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso e) hEY
  let _ : EYC.right.IsLeftKanExtension EYC.hom := hEYC.isLeftKanExtension
  have hLR : L = R := by
    apply Functor.hom_ext_of_isLeftKanExtension EYC.right EYC.hom L R
    ext ⟨⟩
    simp only [NatTrans.comp_app]
    dsimp [EYC]
    simp only [Category.comp_id]
    rw [show (DayFunctor.νNatTrans C V).app _ = DayFunctor.ν C V by rfl]
    dsimp only [L, R]
    simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
    have hConv :
        (DayFunctor.η (𝟙_ (C ⊛⥤ V)) M).app (𝟙_ C, Y) ≫
            (one ▷ M).natTrans.app (𝟙_ C ⊗ Y) =
            (one.natTrans.app (𝟙_ C) ▷ F.obj Y) ≫
            (DayFunctor.η M M).app (𝟙_ C, Y) := by
      change
        (convolutionExtensionUnit C V (𝟙_ (C ⊛⥤ V)) M).app (𝟙_ C, Y) ≫
            ((ι C V (C ⊛⥤ V)).map (one ▷ M)).app (𝟙_ C ⊗ Y) =
          (((ι C V (C ⊛⥤ V)).map one).app (𝟙_ C) ▷
              ((ι C V (C ⊛⥤ V)).obj M).obj Y) ≫
            (convolutionExtensionUnit C V M M).app (𝟙_ C, Y)
      exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app
        C V one M (𝟙_ C) Y
    have hUnit : DayFunctor.ν C V ≫ one.natTrans.app (𝟙_ C) =
        Functor.LaxMonoidal.ε F := by
      exact DayFunctor.ν_comp_unitDesc (Functor.LaxMonoidal.ε F)
    have hUnitWhisker :
        (DayFunctor.ν C V ▷ F.obj Y) ≫
            (one.natTrans.app (𝟙_ C) ▷ F.obj Y) =
          Functor.LaxMonoidal.ε F ▷ F.obj Y := by
      rw [← MonoidalCategory.comp_whiskerRight, hUnit]
    have hMul : (DayFunctor.η M M).app (𝟙_ C, Y) ≫
        mul.natTrans.app (𝟙_ C ⊗ Y) =
          Functor.LaxMonoidal.μ F (𝟙_ C) Y := by
      exact DayFunctor.η_comp_tensorDesc_app μNat (𝟙_ C) Y
    have hUnitor :
        (DayFunctor.ν C V ▷ F.obj Y) ≫
            (DayFunctor.η (𝟙_ (C ⊛⥤ V)) M).app (𝟙_ C, Y) ≫
              (λ_ M).hom.natTrans.app (𝟙_ C ⊗ Y) =
          (λ_ (F.obj Y)).hom ≫ F.map (λ_ Y).inv := by
      change
        unitUnit C V (C ⊛⥤ V) ▷ ((ι C V (C ⊛⥤ V)).obj M).obj Y ≫
              (convolutionExtensionUnit C V (𝟙_ (C ⊛⥤ V)) M).app
                (𝟙_ C, Y) ≫
              ((ι C V (C ⊛⥤ V)).map (λ_ M).hom).app (𝟙_ C ⊗ Y) =
          (λ_ (((ι C V (C ⊛⥤ V)).obj M).obj Y)).hom ≫
            ((ι C V (C ⊛⥤ V)).obj M).map (λ_ Y).inv
      exact leftUnitor_hom_unit_app V M Y
    calc
      _ =
          ((DayFunctor.ν C V ▷ F.obj Y) ≫
              (one.natTrans.app (𝟙_ C) ▷ F.obj Y)) ≫
            ((DayFunctor.η M M).app (𝟙_ C, Y) ≫
              mul.natTrans.app (𝟙_ C ⊗ Y)) := by
                slice_lhs 2 3 => rw [hConv]
                simp only [Category.assoc]
      _ = (Functor.LaxMonoidal.ε F ▷ F.obj Y) ≫
            Functor.LaxMonoidal.μ F (𝟙_ C) Y := by rw [hUnitWhisker, hMul]
      _ = (λ_ (F.obj Y)).hom ≫ F.map (λ_ Y).inv := by
        simpa only [tensorHom_def, whiskerLeft_id, Category.comp_id,
          Category.id_comp] using
          Functor.LaxMonoidal.ε_tensorHom_comp_μ F (𝟙 (F.obj Y))
      _ = (DayFunctor.ν C V ▷ F.obj Y) ≫
            (DayFunctor.η (𝟙_ (C ⊛⥤ V)) M).app (𝟙_ C, Y) ≫
              (λ_ M).hom.natTrans.app (𝟙_ C ⊗ Y) := hUnitor.symm
  change L.app X = R.app X
  exact NatTrans.congr_app hLR X

private theorem monObjOfLaxMonoidal_mul_one
    (F : C ⥤ V) [F.LaxMonoidal] :
    let μNat : F ⊠ F ⟶ tensor C ⋙ F :=
      { app := fun p ↦ Functor.LaxMonoidal.μ F p.1 p.2
        naturality := by
          rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
          simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
            tensor_map, ← tensorHom_def] using
            Functor.LaxMonoidal.μ_natural F f g }
    (DayFunctor.mk F ◁ DayFunctor.unitDesc (Functor.LaxMonoidal.ε F)) ≫
        DayFunctor.tensorDesc μNat =
      (ρ_ (DayFunctor.mk F)).hom := by
  dsimp only
  apply DayFunctor.tensor_hom_ext
  intro X Y
  let M := DayFunctor.mk F
  let one : 𝟙_ (C ⊛⥤ V) ⟶ M :=
    DayFunctor.unitDesc (Functor.LaxMonoidal.ε F)
  let μNat : F ⊠ F ⟶ tensor C ⋙ F :=
    { app := fun p ↦ Functor.LaxMonoidal.μ F p.1 p.2
      naturality := by
        rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
        simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
          tensor_map, ← tensorHom_def] using
          Functor.LaxMonoidal.μ_natural F f g }
  let mul : M ⊗ M ⟶ M := DayFunctor.tensorDesc μNat
  let L :
      (𝟙_ (C ⊛⥤ V)).functor ⋙ tensorLeft (F.obj X) ⟶
        tensorLeft X ⋙ F :=
    { app := fun U ↦
        (DayFunctor.η M (𝟙_ (C ⊛⥤ V))).app (X, U) ≫
          (((M ◁ one) ≫ mul).natTrans.app (X ⊗ U))
      naturality := by
        intro U U' f
        simp only [Functor.comp_map]
        rw [show (tensorLeft (F.obj X)).map
            ((𝟙_ (C ⊛⥤ V)).functor.map f) =
          F.obj X ◁ (𝟙_ (C ⊛⥤ V)).functor.map f by rfl]
        rw [show (tensorLeft X).map f = X ◁ f by rfl]
        have hη := (DayFunctor.η M (𝟙_ (C ⊛⥤ V))).naturality
          ((𝟙 X, f) : (X, U) ⟶ (X, U'))
        simp only [externalProductBifunctor_obj_map, Functor.map_id,
          id_whiskerRight, Category.id_comp, Functor.comp_map, tensor_map,
          id_tensorHom] at hη
        rw [← Category.assoc, hη, Category.assoc]
        rw [((M ◁ one) ≫ mul).natTrans.naturality (X ◁ f)]
        dsimp only [M]
        simp only [Category.assoc] }
  let R :
      (𝟙_ (C ⊛⥤ V)).functor ⋙ tensorLeft (F.obj X) ⟶
        tensorLeft X ⋙ F :=
    { app := fun U ↦
        (DayFunctor.η M (𝟙_ (C ⊛⥤ V))).app (X, U) ≫
          ((ρ_ M).hom.natTrans.app (X ⊗ U))
      naturality := by
        intro U U' f
        simp only [Functor.comp_map]
        rw [show (tensorLeft (F.obj X)).map
            ((𝟙_ (C ⊛⥤ V)).functor.map f) =
          F.obj X ◁ (𝟙_ (C ⊛⥤ V)).functor.map f by rfl]
        rw [show (tensorLeft X).map f = X ◁ f by rfl]
        have hη := (DayFunctor.η M (𝟙_ (C ⊛⥤ V))).naturality
          ((𝟙 X, f) : (X, U) ⟶ (X, U'))
        simp only [externalProductBifunctor_obj_map, Functor.map_id,
          id_whiskerRight, Category.id_comp, Functor.comp_map, tensor_map,
          id_tensorHom] at hη
        rw [← Category.assoc, hη, Category.assoc]
        rw [(ρ_ M).hom.natTrans.naturality (X ◁ f)]
        dsimp only [M]
        simp only [Category.assoc] }
  let E : Functor.LeftExtension
      (Functor.fromPUnit.{0} (𝟙_ C))
      (Functor.fromPUnit.{0} (𝟙_ V)) :=
    Functor.LeftExtension.mk (𝟙_ (C ⊛⥤ V)).functor
      (DayFunctor.νNatTrans C V)
  let EX := (Functor.LeftExtension.postcompose₂
    (Functor.fromPUnit.{0} (𝟙_ C))
    (Functor.fromPUnit.{0} (𝟙_ V))
    (tensorLeft (F.obj X))).obj E
  have hE : E.IsPointwiseLeftKanExtension :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit
      C V (C ⊛⥤ V)
  have hEX : EX.IsPointwiseLeftKanExtension :=
    hE.postcompose (tensorLeft (F.obj X))
  let EXC : Functor.LeftExtension
      (Functor.fromPUnit.{0} (𝟙_ C))
      (Functor.fromPUnit.{0} (𝟙_ V) ⋙ tensorLeft (F.obj X)) :=
    Functor.LeftExtension.mk
      ((𝟙_ (C ⊛⥤ V)).functor ⋙ tensorLeft (F.obj X))
      (Functor.whiskerRight (DayFunctor.νNatTrans C V)
          (tensorLeft (F.obj X)) ≫
        (Functor.associator _ _ _).hom)
  let e : EX ≅ EXC :=
    Functor.LeftExtension.postcompose₂ObjMkIso
      (tensorLeft (F.obj X)) (DayFunctor.νNatTrans C V)
  have hEXC : EXC.IsPointwiseLeftKanExtension :=
    (Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso e) hEX
  let _ : EXC.right.IsLeftKanExtension EXC.hom := hEXC.isLeftKanExtension
  have hLR : L = R := by
    apply Functor.hom_ext_of_isLeftKanExtension EXC.right EXC.hom L R
    ext ⟨⟩
    simp only [NatTrans.comp_app]
    dsimp [EXC]
    simp only [Category.comp_id]
    rw [show (DayFunctor.νNatTrans C V).app _ = DayFunctor.ν C V by rfl]
    dsimp only [L, R]
    simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
    have hConv :
        (DayFunctor.η M (𝟙_ (C ⊛⥤ V))).app (X, 𝟙_ C) ≫
            (M ◁ one).natTrans.app (X ⊗ 𝟙_ C) =
            (F.obj X ◁ one.natTrans.app (𝟙_ C)) ≫
            (DayFunctor.η M M).app (X, 𝟙_ C) := by
      change
        (convolutionExtensionUnit C V M (𝟙_ (C ⊛⥤ V))).app (X, 𝟙_ C) ≫
            ((ι C V (C ⊛⥤ V)).map (M ◁ one)).app (X ⊗ 𝟙_ C) =
          (((ι C V (C ⊛⥤ V)).obj M).obj X ◁
              ((ι C V (C ⊛⥤ V)).map one).app (𝟙_ C)) ≫
            (convolutionExtensionUnit C V M M).app (X, 𝟙_ C)
      exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        V M one X (𝟙_ C)
    have hUnit : DayFunctor.ν C V ≫ one.natTrans.app (𝟙_ C) =
        Functor.LaxMonoidal.ε F := by
      exact DayFunctor.ν_comp_unitDesc (Functor.LaxMonoidal.ε F)
    have hUnitWhisker :
        (F.obj X ◁ DayFunctor.ν C V) ≫
            (F.obj X ◁ one.natTrans.app (𝟙_ C)) =
          F.obj X ◁ Functor.LaxMonoidal.ε F := by
      rw [← MonoidalCategory.whiskerLeft_comp, hUnit]
    have hMul : (DayFunctor.η M M).app (X, 𝟙_ C) ≫
        mul.natTrans.app (X ⊗ 𝟙_ C) =
          Functor.LaxMonoidal.μ F X (𝟙_ C) := by
      exact DayFunctor.η_comp_tensorDesc_app μNat X (𝟙_ C)
    have hUnitor :
        (F.obj X ◁ DayFunctor.ν C V) ≫
            (DayFunctor.η M (𝟙_ (C ⊛⥤ V))).app (X, 𝟙_ C) ≫
              (ρ_ M).hom.natTrans.app (X ⊗ 𝟙_ C) =
          (ρ_ (F.obj X)).hom ≫ F.map (ρ_ X).inv := by
      change
        ((ι C V (C ⊛⥤ V)).obj M).obj X ◁ unitUnit C V (C ⊛⥤ V) ≫
              (convolutionExtensionUnit C V M (𝟙_ (C ⊛⥤ V))).app
                (X, 𝟙_ C) ≫
              ((ι C V (C ⊛⥤ V)).map (ρ_ M).hom).app (X ⊗ 𝟙_ C) =
          (ρ_ (((ι C V (C ⊛⥤ V)).obj M).obj X)).hom ≫
            ((ι C V (C ⊛⥤ V)).obj M).map (ρ_ X).inv
      exact rightUnitor_hom_unit_app V M X
    calc
      _ =
          ((F.obj X ◁ DayFunctor.ν C V) ≫
              (F.obj X ◁ one.natTrans.app (𝟙_ C))) ≫
            ((DayFunctor.η M M).app (X, 𝟙_ C) ≫
              mul.natTrans.app (X ⊗ 𝟙_ C)) := by
                slice_lhs 2 3 => rw [hConv]
                simp only [Category.assoc]
      _ = (F.obj X ◁ Functor.LaxMonoidal.ε F) ≫
            Functor.LaxMonoidal.μ F X (𝟙_ C) := by rw [hUnitWhisker, hMul]
      _ = (ρ_ (F.obj X)).hom ≫ F.map (ρ_ X).inv := by
        simpa only [tensorHom_def, id_whiskerRight, Category.comp_id,
          Category.id_comp] using
          Functor.LaxMonoidal.tensorHom_ε_comp_μ F (𝟙 (F.obj X))
      _ = (F.obj X ◁ DayFunctor.ν C V) ≫
            (DayFunctor.η M (𝟙_ (C ⊛⥤ V))).app (X, 𝟙_ C) ≫
              (ρ_ M).hom.natTrans.app (X ⊗ 𝟙_ C) := hUnitor.symm
  change L.app Y = R.app Y
  exact NatTrans.congr_app hLR Y

private theorem monObjOfLaxMonoidal_mul_assoc
    (F : C ⥤ V) [F.LaxMonoidal] :
    let μNat : F ⊠ F ⟶ tensor C ⋙ F :=
      { app := fun p ↦ Functor.LaxMonoidal.μ F p.1 p.2
        naturality := by
          rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
          simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
            tensor_map, ← tensorHom_def] using
            Functor.LaxMonoidal.μ_natural F f g }
    (DayFunctor.tensorDesc μNat ▷ DayFunctor.mk F) ≫
        DayFunctor.tensorDesc μNat =
      (α_ (DayFunctor.mk F) (DayFunctor.mk F) (DayFunctor.mk F)).hom ≫
        (DayFunctor.mk F ◁ DayFunctor.tensorDesc μNat) ≫
          DayFunctor.tensorDesc μNat := by
  dsimp only
  let M := DayFunctor.mk F
  let μNat : F ⊠ F ⟶ tensor C ⋙ F :=
    { app := fun p ↦ Functor.LaxMonoidal.μ F p.1 p.2
      naturality := by
        rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
        simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
          tensor_map, ← tensorHom_def] using
          Functor.LaxMonoidal.μ_natural F f g }
  let mul : M ⊗ M ⟶ M := DayFunctor.tensorDesc μNat
  let lhs : (M ⊗ M) ⊗ M ⟶ M := (mul ▷ M) ≫ mul
  let rhs : (M ⊗ M) ⊗ M ⟶ M :=
    (α_ M M M).hom ≫ (M ◁ mul) ≫ mul
  change lhs = rhs
  apply DayFunctor.tensor_hom_ext
  intro U Z
  let LZ :
      (M ⊗ M).functor ⋙ tensorRight (F.obj Z) ⟶
        tensorRight Z ⋙ F :=
    { app := fun W ↦
        (DayFunctor.η (M ⊗ M) M).app (W, Z) ≫
          lhs.natTrans.app (W ⊗ Z)
      naturality := by
        intro W W' f
        simp only [Functor.comp_map]
        rw [show (tensorRight (F.obj Z)).map ((M ⊗ M).functor.map f) =
          (M ⊗ M).functor.map f ▷ F.obj Z by rfl]
        rw [show (tensorRight Z).map f = f ▷ Z by rfl]
        have hη := (DayFunctor.η (M ⊗ M) M).naturality
          ((f, 𝟙 Z) : (W, Z) ⟶ (W', Z))
        simp only [externalProductBifunctor_obj_map, Functor.map_id,
          whiskerLeft_id, Category.comp_id, Functor.comp_map, tensor_map,
          tensorHom_id] at hη
        rw [← Category.assoc, hη, Category.assoc]
        rw [lhs.natTrans.naturality (f ▷ Z)]
        dsimp only [M]
        simp only [Category.assoc] }
  let RZ :
      (M ⊗ M).functor ⋙ tensorRight (F.obj Z) ⟶
        tensorRight Z ⋙ F :=
    { app := fun W ↦
        (DayFunctor.η (M ⊗ M) M).app (W, Z) ≫
          rhs.natTrans.app (W ⊗ Z)
      naturality := by
        intro W W' f
        simp only [Functor.comp_map]
        rw [show (tensorRight (F.obj Z)).map ((M ⊗ M).functor.map f) =
          (M ⊗ M).functor.map f ▷ F.obj Z by rfl]
        rw [show (tensorRight Z).map f = f ▷ Z by rfl]
        have hη := (DayFunctor.η (M ⊗ M) M).naturality
          ((f, 𝟙 Z) : (W, Z) ⟶ (W', Z))
        simp only [externalProductBifunctor_obj_map, Functor.map_id,
          whiskerLeft_id, Category.comp_id, Functor.comp_map, tensor_map,
          tensorHom_id] at hη
        rw [← Category.assoc, hη, Category.assoc]
        rw [rhs.natTrans.naturality (f ▷ Z)]
        dsimp only [M]
        simp only [Category.assoc] }
  let E : Functor.LeftExtension (tensor C) (F ⊠ F) :=
    Functor.LeftExtension.mk (M ⊗ M).functor (DayFunctor.η M M)
  let EZ := (Functor.LeftExtension.postcompose₂
    (tensor C) (F ⊠ F) (tensorRight (F.obj Z))).obj E
  have hE : E.IsPointwiseLeftKanExtension :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      M M
  have hEZ : EZ.IsPointwiseLeftKanExtension :=
    hE.postcompose (tensorRight (F.obj Z))
  let EZC : Functor.LeftExtension (tensor C)
      ((F ⊠ F) ⋙ tensorRight (F.obj Z)) :=
    Functor.LeftExtension.mk
      ((M ⊗ M).functor ⋙ tensorRight (F.obj Z))
      (Functor.whiskerRight (DayFunctor.η M M)
          (tensorRight (F.obj Z)) ≫
        (Functor.associator _ _ _).hom)
  let e : EZ ≅ EZC :=
    Functor.LeftExtension.postcompose₂ObjMkIso
      (tensorRight (F.obj Z)) (DayFunctor.η M M)
  have hEZC : EZC.IsPointwiseLeftKanExtension :=
    (Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso e) hEZ
  let _ : EZC.right.IsLeftKanExtension EZC.hom := hEZC.isLeftKanExtension
  have hLZRZ : LZ = RZ := by
    apply Functor.hom_ext_of_isLeftKanExtension EZC.right EZC.hom LZ RZ
    ext ⟨X, Y⟩
    simp only [NatTrans.comp_app]
    dsimp [EZC]
    simp only [Category.comp_id]
    dsimp only [LZ, RZ]
    have hOuterL :
        (DayFunctor.η (M ⊗ M) M).app (X ⊗ Y, Z) ≫
            (mul ▷ M).natTrans.app ((X ⊗ Y) ⊗ Z) =
          (mul.natTrans.app (X ⊗ Y) ▷ F.obj Z) ≫
            (DayFunctor.η M M).app (X ⊗ Y, Z) := by
      change
        (convolutionExtensionUnit C V (M ⊗ M) M).app (X ⊗ Y, Z) ≫
            ((ι C V (C ⊛⥤ V)).map (mul ▷ M)).app ((X ⊗ Y) ⊗ Z) =
          (((ι C V (C ⊛⥤ V)).map mul).app (X ⊗ Y) ▷
              ((ι C V (C ⊛⥤ V)).obj M).obj Z) ≫
            (convolutionExtensionUnit C V M M).app (X ⊗ Y, Z)
      exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app
        C V mul M (X ⊗ Y) Z
    have hInnerMul : (DayFunctor.η M M).app (X, Y) ≫
        mul.natTrans.app (X ⊗ Y) = Functor.LaxMonoidal.μ F X Y := by
      exact DayFunctor.η_comp_tensorDesc_app μNat X Y
    have hOuterMul : (DayFunctor.η M M).app (X ⊗ Y, Z) ≫
        mul.natTrans.app ((X ⊗ Y) ⊗ Z) =
          Functor.LaxMonoidal.μ F (X ⊗ Y) Z := by
      exact DayFunctor.η_comp_tensorDesc_app μNat (X ⊗ Y) Z
    have hAssoc :
        ((DayFunctor.η M M).app (X, Y) ▷ F.obj Z) ≫
            (DayFunctor.η (M ⊗ M) M).app (X ⊗ Y, Z) ≫
              (α_ M M M).hom.natTrans.app ((X ⊗ Y) ⊗ Z) =
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
            (F.obj X ◁ (DayFunctor.η M M).app (Y, Z)) ≫
              (DayFunctor.η M (M ⊗ M)).app (X, Y ⊗ Z) ≫
                (M ⊗ (M ⊗ M)).functor.map (α_ X Y Z).inv := by
      change
        ((convolutionExtensionUnit C V M M).app (X, Y) ▷
            ((ι C V (C ⊛⥤ V)).obj M).obj Z) ≫
          (convolutionExtensionUnit C V (M ⊗ M) M).app (X ⊗ Y, Z) ≫
          ((ι C V (C ⊛⥤ V)).map (α_ M M M).hom).app
            ((X ⊗ Y) ⊗ Z) =
        (α_ _ _ _).hom ≫
          (((ι C V (C ⊛⥤ V)).obj M).obj X ◁
            (convolutionExtensionUnit C V M M).app (Y, Z)) ≫
          (convolutionExtensionUnit C V M (M ⊗ M)).app (X, Y ⊗ Z) ≫
          ((ι C V (C ⊛⥤ V)).obj (M ⊗ (M ⊗ M))).map
            (α_ X Y Z).inv
      exact associator_hom_unit_unit V M M M X Y Z
    have hNat := ((M ◁ mul) ≫ mul).natTrans.naturality (α_ X Y Z).inv
    have hNat' :
        (M ⊗ (M ⊗ M)).functor.map (α_ X Y Z).inv ≫
              (M ◁ mul).natTrans.app ((X ⊗ Y) ⊗ Z) ≫
              mul.natTrans.app ((X ⊗ Y) ⊗ Z) =
          (M ◁ mul).natTrans.app (X ⊗ (Y ⊗ Z)) ≫
              mul.natTrans.app (X ⊗ (Y ⊗ Z)) ≫
              F.map (α_ X Y Z).inv := by
      simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app,
        Category.assoc] using hNat
    have hOuterR :
        (DayFunctor.η M (M ⊗ M)).app (X, Y ⊗ Z) ≫
            (M ◁ mul).natTrans.app (X ⊗ (Y ⊗ Z)) =
          (F.obj X ◁ mul.natTrans.app (Y ⊗ Z)) ≫
            (DayFunctor.η M M).app (X, Y ⊗ Z) := by
      change
        (convolutionExtensionUnit C V M (M ⊗ M)).app (X, Y ⊗ Z) ≫
            ((ι C V (C ⊛⥤ V)).map (M ◁ mul)).app (X ⊗ (Y ⊗ Z)) =
          (((ι C V (C ⊛⥤ V)).obj M).obj X ◁
              ((ι C V (C ⊛⥤ V)).map mul).app (Y ⊗ Z)) ≫
            (convolutionExtensionUnit C V M M).app (X, Y ⊗ Z)
      exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        V M mul X (Y ⊗ Z)
    have hInnerMulR : (DayFunctor.η M M).app (Y, Z) ≫
        mul.natTrans.app (Y ⊗ Z) = Functor.LaxMonoidal.μ F Y Z := by
      exact DayFunctor.η_comp_tensorDesc_app μNat Y Z
    have hOuterMulR : (DayFunctor.η M M).app (X, Y ⊗ Z) ≫
        mul.natTrans.app (X ⊗ (Y ⊗ Z)) =
          Functor.LaxMonoidal.μ F X (Y ⊗ Z) := by
      exact DayFunctor.η_comp_tensorDesc_app μNat X (Y ⊗ Z)
    dsimp only [lhs, rhs]
    simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
    calc
      _ =
          (((DayFunctor.η M M).app (X, Y) ≫
              mul.natTrans.app (X ⊗ Y)) ▷ F.obj Z) ≫
            ((DayFunctor.η M M).app (X ⊗ Y, Z) ≫
              mul.natTrans.app ((X ⊗ Y) ⊗ Z)) := by
                slice_lhs 2 3 => rw [hOuterL]
                simp only [Category.assoc]
                rw [← MonoidalCategory.comp_whiskerRight_assoc]
      _ = (Functor.LaxMonoidal.μ F X Y ▷ F.obj Z) ≫
            Functor.LaxMonoidal.μ F (X ⊗ Y) Z := by
              rw [hInnerMul, hOuterMul]
      _ = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
            (F.obj X ◁ Functor.LaxMonoidal.μ F Y Z) ≫
              Functor.LaxMonoidal.μ F X (Y ⊗ Z) ≫
                F.map (α_ X Y Z).inv :=
        Functor.LaxMonoidal.μ_whiskerRight_comp_μ F X Y Z
      _ =
          ((DayFunctor.η M M).app (X, Y) ▷ F.obj Z) ≫
            (DayFunctor.η (M ⊗ M) M).app (X ⊗ Y, Z) ≫
              (α_ M M M).hom.natTrans.app ((X ⊗ Y) ⊗ Z) ≫
                (M ◁ mul).natTrans.app ((X ⊗ Y) ⊗ Z) ≫
                  mul.natTrans.app ((X ⊗ Y) ⊗ Z) := by
        symm
        slice_lhs 1 3 => rw [hAssoc]
        simp only [Category.assoc]
        rw [hNat']
        slice_lhs 3 4 => rw [hOuterR]
        slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp]
        rw [hInnerMulR]
        simp only [Category.assoc]
        slice_lhs 3 4 => rw [hOuterMulR]
  change LZ.app U = RZ.app U
  exact NatTrans.congr_app hLZRZ U

/-- A lax monoidal functor, regarded as a monoid for Day convolution. -/
@[instance_reducible]
noncomputable def monObjOfLaxMonoidal (F : C ⥤ V) [F.LaxMonoidal] :
    MonObj (DayFunctor.mk F) where
  one := DayFunctor.unitDesc (Functor.LaxMonoidal.ε F)
  mul := by
    let μNat : F ⊠ F ⟶ tensor C ⋙ F :=
      { app := fun p ↦ Functor.LaxMonoidal.μ F p.1 p.2
        naturality := by
          rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
          simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
            tensor_map, ← tensorHom_def] using
            Functor.LaxMonoidal.μ_natural F f g }
    exact DayFunctor.tensorDesc μNat
  one_mul := by exact monObjOfLaxMonoidal_one_mul F
  mul_one := by exact monObjOfLaxMonoidal_mul_one F
  mul_assoc := by exact monObjOfLaxMonoidal_mul_assoc F

/-- The Day unit of `monObjOfLaxMonoidal` is the lax-monoidal unit map. -/
theorem monObjOfLaxMonoidal_one_app (F : C ⥤ V) [F.LaxMonoidal] :
    DayFunctor.ν C V ≫
        (monObjOfLaxMonoidal F).one.natTrans.app (𝟙_ C) =
      Functor.LaxMonoidal.ε F := by
  change DayFunctor.ν C V ≫
      (DayFunctor.unitDesc (Functor.LaxMonoidal.ε F)).natTrans.app (𝟙_ C) =
    Functor.LaxMonoidal.ε F
  exact DayFunctor.ν_comp_unitDesc (Functor.LaxMonoidal.ε F)

/-- The Day multiplication of `monObjOfLaxMonoidal` is the lax-monoidal
multiplication map on convolution generators. -/
theorem monObjOfLaxMonoidal_mul_app (F : C ⥤ V) [F.LaxMonoidal]
    (X Y : C) :
    (DayFunctor.η (DayFunctor.mk F) (DayFunctor.mk F)).app (X, Y) ≫
        (monObjOfLaxMonoidal F).mul.natTrans.app (X ⊗ Y) =
      Functor.LaxMonoidal.μ F X Y := by
  let μNat : F ⊠ F ⟶ tensor C ⋙ F :=
    { app := fun p ↦ Functor.LaxMonoidal.μ F p.1 p.2
      naturality := by
        rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
        simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
          tensor_map, ← tensorHom_def] using
          Functor.LaxMonoidal.μ_natural F f g }
  change (DayFunctor.η (DayFunctor.mk F) (DayFunctor.mk F)).app (X, Y) ≫
      (DayFunctor.tensorDesc μNat).natTrans.app (X ⊗ Y) =
    Functor.LaxMonoidal.μ F X Y
  exact DayFunctor.η_comp_tensorDesc_app μNat X Y

private theorem isCommMonObjOfLaxBraided_mul_comm
    [BraidedCategory C] [SymmetricCategory V]
    (F : C ⥤ V) [F.LaxBraided] :
    (β_ (DayFunctor.mk F) (DayFunctor.mk F)).hom ≫
        (monObjOfLaxMonoidal F).mul =
      (monObjOfLaxMonoidal F).mul := by
  let M := DayFunctor.mk F
  let _ : MonObj M := monObjOfLaxMonoidal F
  change (β_ M M).hom ≫ MonObj.mul = MonObj.mul
  apply DayFunctor.tensor_hom_ext
  intro X Y
  let _ : DayConvolution F F :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution C V
      (C ⊛⥤ V) M M
  have hBraid :
      (DayFunctor.η M M).app (X, Y) ≫
          (β_ M M).hom.natTrans.app (X ⊗ Y) =
        (β_ (F.obj X) (F.obj Y)).hom ≫
          (DayFunctor.η M M).app (Y, X) ≫
            (M ⊗ M).functor.map (β_ Y X).hom := by
    change
      (DayConvolution.unit F F).app (X, Y) ≫
          (DayConvolution.braiding F F).hom.app (X ⊗ Y) =
        (β_ (F.obj X) (F.obj Y)).hom ≫
          (DayConvolution.unit F F).app (Y, X) ≫
            (F ⊛ F).map (β_ Y X).hom
    exact DayConvolution.unit_app_braiding_hom_app F F X Y
  have hNat := (MonObj.mul (X := M)).natTrans.naturality (β_ Y X).hom
  have hMulYX : (DayFunctor.η M M).app (Y, X) ≫
      (MonObj.mul (X := M)).natTrans.app (Y ⊗ X) =
        Functor.LaxMonoidal.μ F Y X := by
    simpa only [M] using monObjOfLaxMonoidal_mul_app F Y X
  have hMulXY : (DayFunctor.η M M).app (X, Y) ≫
      (MonObj.mul (X := M)).natTrans.app (X ⊗ Y) =
        Functor.LaxMonoidal.μ F X Y := by
    simpa only [M] using monObjOfLaxMonoidal_mul_app F X Y
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
  slice_lhs 1 2 => rw [hBraid]
  simp only [Category.assoc]
  rw [hNat]
  slice_lhs 2 3 => rw [hMulYX]
  rw [Functor.LaxBraided.braided (F := F) Y X]
  rw [SymmetricCategory.symmetry_assoc]
  exact hMulXY.symm

/-- A lax braided functor determines a commutative Day-convolution monoid. -/
theorem isCommMonObjOfLaxBraided
    [BraidedCategory C] [SymmetricCategory V]
    (F : C ⥤ V) [F.LaxBraided] :
    @IsCommMonObj (C ⊛⥤ V) _ _ _ (DayFunctor.mk F)
      (monObjOfLaxMonoidal F) := by
  let _ : MonObj (DayFunctor.mk F) := monObjOfLaxMonoidal F
  exact { mul_comm := by exact isCommMonObjOfLaxBraided_mul_comm F }

/-- A lax braided functor, bundled as a commutative monoid for Day
convolution. -/
noncomputable def commMonOfLaxBraided
    [BraidedCategory C] [SymmetricCategory V]
    (F : C ⥤ V) [F.LaxBraided] : CommMon (C ⊛⥤ V) where
  X := DayFunctor.mk F
  mon := monObjOfLaxMonoidal F
  comm := isCommMonObjOfLaxBraided F

/-- The Day-convolution multiplication induced by a lax braided functor is
commutative. -/
theorem mul_comm [BraidedCategory C] [SymmetricCategory V]
    (F : C ⥤ V) [F.LaxBraided] :
    (β_ (DayFunctor.mk F) (DayFunctor.mk F)).hom ≫
        (monObjOfLaxMonoidal F).mul =
      (monObjOfLaxMonoidal F).mul := by
  let M := DayFunctor.mk F
  let _ : MonObj M := monObjOfLaxMonoidal F
  let _ : IsCommMonObj M := isCommMonObjOfLaxBraided F
  change (β_ M M).hom ≫ MonObj.mul = MonObj.mul
  exact CategoryTheory.IsCommMonObj.mul_comm M

/-- Componentwise commutativity of the lax-monoidal multiplication, with
the source braiding retained. -/
theorem mul_comm_app [BraidedCategory C] [SymmetricCategory V]
    (F : C ⥤ V) [F.LaxBraided] (X Y : C) :
    (β_ (F.obj X) (F.obj Y)).hom ≫
        Functor.LaxMonoidal.μ F Y X ≫ F.map (β_ Y X).hom =
      Functor.LaxMonoidal.μ F X Y := by
  let M := DayFunctor.mk F
  let _ : MonObj M := monObjOfLaxMonoidal F
  let _ : DayConvolution F F :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution C V
      (C ⊛⥤ V) M M
  have hGlobal : (β_ M M).hom ≫ MonObj.mul = MonObj.mul := by
    simpa only [M] using mul_comm F
  have hApp := congrArg
    (fun q : M ⊗ M ⟶ M ↦
      (DayFunctor.η M M).app (X, Y) ≫ q.natTrans.app (X ⊗ Y))
    hGlobal
  have hBraid :
      (DayFunctor.η M M).app (X, Y) ≫
          (β_ M M).hom.natTrans.app (X ⊗ Y) =
        (β_ (F.obj X) (F.obj Y)).hom ≫
          (DayFunctor.η M M).app (Y, X) ≫
            (M ⊗ M).functor.map (β_ Y X).hom := by
    change
      (DayConvolution.unit F F).app (X, Y) ≫
          (DayConvolution.braiding F F).hom.app (X ⊗ Y) =
        (β_ (F.obj X) (F.obj Y)).hom ≫
          (DayConvolution.unit F F).app (Y, X) ≫
            (F ⊛ F).map (β_ Y X).hom
    exact DayConvolution.unit_app_braiding_hom_app F F X Y
  have hNat := (MonObj.mul (X := M)).natTrans.naturality (β_ Y X).hom
  have hMulYX : (DayFunctor.η M M).app (Y, X) ≫
      (MonObj.mul (X := M)).natTrans.app (Y ⊗ X) =
        Functor.LaxMonoidal.μ F Y X := by
    simpa only [M] using monObjOfLaxMonoidal_mul_app F Y X
  have hMulXY : (DayFunctor.η M M).app (X, Y) ≫
      (MonObj.mul (X := M)).natTrans.app (X ⊗ Y) =
        Functor.LaxMonoidal.μ F X Y := by
    simpa only [M] using monObjOfLaxMonoidal_mul_app F X Y
  have hLeft :
      (DayFunctor.η M M).app (X, Y) ≫
          ((β_ M M).hom ≫ MonObj.mul).natTrans.app (X ⊗ Y) =
        (β_ (F.obj X) (F.obj Y)).hom ≫
          Functor.LaxMonoidal.μ F Y X ≫ F.map (β_ Y X).hom := by
    simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
    slice_lhs 1 2 => rw [hBraid]
    simp only [Category.assoc]
    rw [hNat]
    slice_lhs 2 3 => rw [hMulYX]
  calc
    _ = (DayFunctor.η M M).app (X, Y) ≫
          ((β_ M M).hom ≫ MonObj.mul).natTrans.app (X ⊗ Y) := hLeft.symm
    _ = (DayFunctor.η M M).app (X, Y) ≫
          (MonObj.mul (X := M)).natTrans.app (X ⊗ Y) := hApp
    _ = _ := hMulXY

end CategoryTheory.MonoidalCategory.DayFunctor
