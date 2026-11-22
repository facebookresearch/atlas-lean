/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.Braided
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.Closed

/-!
# Closed symmetric structure on Day functors

This file completes Mathlib's DayFunctor monoidal structure with braided and symmetric instances,
and with the end-based internal Hom already characterized by `DayConvolutionInternalHom`.

All Day tensors, associators, braidings, end projections, evaluations, coevaluations, and triangle
proofs are reused from Mathlib. The construction installs no global choice of `DayConvolution` and
adds no structure to the raw functor category.
-/

public section

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.DayConvolution
open scoped CategoryTheory.MonoidalCategory.DayFunctor
open scoped ExternalProduct

namespace CategoryTheory.MonoidalCategory.DayFunctor

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
      (CostructuredArrow ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) d)
      (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

section Braided

variable [BraidedCategory C] [BraidedCategory V]

/-- The existing Day-convolution braiding makes `DayFunctor C V` braided. -/
noncomputable instance instBraidedCategory : BraidedCategory (C ⊛⥤ V) := by
  letI (F G : C ⊛⥤ V) : DayConvolution F.functor G.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (C ⊛⥤ V) F G
  exact
    { braiding := fun F G ↦
        { hom := ⟨(DayConvolution.braiding F.functor G.functor).hom⟩
          inv := ⟨(DayConvolution.braiding F.functor G.functor).inv⟩
          hom_inv_id := by
            apply DayFunctor.hom_ext
            exact (DayConvolution.braiding F.functor G.functor).hom_inv_id
          inv_hom_id := by
            apply DayFunctor.hom_ext
            exact (DayConvolution.braiding F.functor G.functor).inv_hom_id }
      braiding_naturality_right := by
        intro F G H η
        apply DayFunctor.hom_ext
        change (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
            (F ◁ η) ≫ (DayConvolution.braiding F.functor H.functor).hom =
          (DayConvolution.braiding F.functor G.functor).hom ≫
            (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
              (η ▷ F)
        rw [← id_tensorHom, ← tensorHom_id]
        rw [LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom,
          LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
        exact DayConvolution.braiding_naturality_right F.functor η.natTrans
      braiding_naturality_left := by
        intro F G η H
        apply DayFunctor.hom_ext
        change (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
            (η ▷ H) ≫ (DayConvolution.braiding G.functor H.functor).hom =
          (DayConvolution.braiding F.functor H.functor).hom ≫
            (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
              (H ◁ η)
        rw [← tensorHom_id, ← id_tensorHom]
        rw [LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom,
          LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
        exact DayConvolution.braiding_naturality_left η.natTrans H.functor
      hexagon_forward := by
        intro F G H
        apply DayFunctor.hom_ext
        let bFG : F ⊗ G ⟶ G ⊗ F :=
          ⟨(DayConvolution.braiding F.functor G.functor).hom⟩
        let bFH : F ⊗ H ⟶ H ⊗ F :=
          ⟨(DayConvolution.braiding F.functor H.functor).hom⟩
        change (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
            (α_ F G H).hom ≫ _ ≫
            (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
              (α_ G H F).hom =
          (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
              (bFG ▷ H) ≫
            (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
                (α_ G F H).hom ≫
              (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
                (G ◁ bFH)
        rw [LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_hom_eq_associator_hom,
          LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_hom_eq_associator_hom,
          LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_hom_eq_associator_hom]
        rw [← tensorHom_id, ← id_tensorHom]
        rw [LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom,
          LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
        dsimp [bFG, bFH]
        exact DayConvolution.hexagon_forward F.functor G.functor H.functor
      hexagon_reverse := by
        intro F G H
        apply DayFunctor.hom_ext
        let bGH : G ⊗ H ⟶ H ⊗ G :=
          ⟨(DayConvolution.braiding G.functor H.functor).hom⟩
        let bFH : F ⊗ H ⟶ H ⊗ F :=
          ⟨(DayConvolution.braiding F.functor H.functor).hom⟩
        change (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
            (α_ F G H).inv ≫ _ ≫
            (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
              (α_ H F G).inv =
          (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
              (F ◁ bGH) ≫
            (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
                (α_ F H G).inv ≫
              (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
                (bFH ▷ G)
        have hInv (X Y Z : C ⊛⥤ V) :
            (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
                (α_ X Y Z).inv =
              (DayConvolution.associator X.functor Y.functor Z.functor).inv := by
          let e :
              (LawfulDayConvolutionMonoidalCategoryStruct.ι C V
                  (C ⊛⥤ V)).obj ((X ⊗ Y) ⊗ Z) ≅
                (LawfulDayConvolutionMonoidalCategoryStruct.ι C V
                  (C ⊛⥤ V)).obj (X ⊗ (Y ⊗ Z)) :=
            DayConvolution.associator X.functor Y.functor Z.functor
          change _ = e.inv
          apply (cancel_epi
            ((LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
              (α_ X Y Z).hom)).1
          rw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
          rw [LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_hom_eq_associator_hom]
          exact e.hom_inv_id.symm
        rw [hInv, hInv, hInv]
        rw [← id_tensorHom, ← tensorHom_id]
        rw [LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom,
          LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
        dsimp [bGH, bFH]
        exact DayConvolution.hexagon_reverse F.functor G.functor H.functor }

end Braided

section Symmetric

variable [SymmetricCategory C] [SymmetricCategory V]

/-- The existing involutivity theorem makes the DayFunctor braiding symmetric. -/
noncomputable instance instSymmetricCategory : SymmetricCategory (C ⊛⥤ V) := by
  letI (F G : C ⊛⥤ V) : DayConvolution F.functor G.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (C ⊛⥤ V) F G
  exact
    { symmetry := by
        intro F G
        apply DayFunctor.hom_ext
        exact DayConvolution.symmetry F.functor G.functor }

end Symmetric

section Closed

variable [MonoidalClosed V]
variable [∀ (F G : C ⥤ V) (c : C),
  HasEnd ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]

/-- The end-based right-adjoint candidate to tensoring on the left by `F`. -/
@[expose]
noncomputable def internalHom (F : C ⊛⥤ V) : (C ⊛⥤ V) ⥤ (C ⊛⥤ V) :=
  let obj (G : C ⊛⥤ V) : C ⥤ V :=
    { obj := fun c ↦ end_
        ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c)
      map := fun {_ _} f ↦ end_.map
        (((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f)
      map_id := fun _ ↦ by simp
      map_comp := fun _ _ ↦ by simp }
  let data (G : C ⊛⥤ V) :
      DayConvolutionInternalHom F.functor G.functor (obj G) :=
    { π := fun c j ↦ end_.π
        ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) j
      hπ := fun c _ _ f ↦ end_.condition
        ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) f
      isLimitWedge := fun c ↦ by
        apply IsLimit.ofIsoLimit (limit.isLimit _)
        exact Multifork.isoOfι
          (Multiequalizer.multifork
            (multicospanIndexEnd
              ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c)))
      map_comp_π := fun f j ↦ by
        change end_.map
            (((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f) ≫
              end_.π
                ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj _) j =
          end_.π
              ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj _) j ≫
            ((((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f).app
              (.op j)).app j
        exact end_.map_π
          (((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f) j }
  { obj := fun G ↦ .mk (obj G)
    map := fun {G G'} η ↦ .mk <| (data G).map η.natTrans (data G')
    map_id := fun G ↦ by
      apply DayFunctor.hom_ext
      ext c j
      change ((data G).map (𝟙 G.functor) (data G)).app c ≫
          (data G).π c j = 𝟙 _ ≫ (data G).π c j
      rw [DayConvolutionInternalHom.map_app_comp_π]
      simp only [NatTrans.id_app, Functor.map_id, Category.comp_id,
        Category.id_comp]
    map_comp := fun {G G' G''} η θ ↦ by
      apply DayFunctor.hom_ext
      ext c j
      change ((data G).map (η.natTrans ≫ θ.natTrans) (data G'')).app c ≫
          (data G'').π c j =
        (((data G).map η.natTrans (data G')).app c ≫
            ((data G').map θ.natTrans (data G'')).app c) ≫ (data G'').π c j
      rw [(data G).map_app_comp_π (η.natTrans ≫ θ.natTrans) (data G'') c j]
      rw [Category.assoc]
      rw [(data G').map_app_comp_π θ.natTrans (data G'') c j]
      rw [← Category.assoc]
      rw [(data G).map_app_comp_π η.natTrans (data G') c j]
      simp }

/-- The underlying functor of the end-based Day internal Hom. -/
private noncomputable abbrev internalHomObj (F G : C ⊛⥤ V) : C ⥤ V :=
  ((internalHom F).obj G).functor

/-- The end projections defining the underlying Day internal Hom. -/
private noncomputable abbrev internalHomData (F G : C ⊛⥤ V) :
    DayConvolutionInternalHom F.functor G.functor (internalHomObj F G) where
  π c j := end_.π
    ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) j
  hπ c _ _ f := end_.condition
    ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) f
  isLimitWedge c := by
    apply IsLimit.ofIsoLimit (limit.isLimit _)
    exact Multifork.isoOfι
      (Multiequalizer.multifork
        (multicospanIndexEnd
          ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c)))
  map_comp_π f j := by
    change end_.map
        (((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f) ≫
          end_.π
            ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj _) j =
      end_.π
          ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj _) j ≫
        ((((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f).app
          (.op j)).app j
    exact end_.map_π
      (((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f) j

omit
  [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
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
    (CostructuredArrow ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) d)
    (tensorRight v)]
  [∀ (v : V) (d : C × C), PreservesColimitsOfShape
    (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)] in
/-- Characteristic equation for the action of `internalHom F` on a morphism. -/
theorem internalHomMap (F : C ⊛⥤ V) {G G' : C ⊛⥤ V} (η : G ⟶ G')
    (c j : C) :
    ((internalHom F).map η).natTrans.app c ≫
        end_.π
          ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G'.functor |>.obj c) j =
      end_.π
          ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) j ≫
        (ihom (F.functor.obj j)).map (η.natTrans.app (j ⊗ c)) := by
  change ((internalHomData F G).map η.natTrans (internalHomData F G')).app c ≫
      (internalHomData F G').π c j =
    (internalHomData F G).π c j ≫
      (ihom (F.functor.obj j)).map (η.natTrans.app (j ⊗ c))
  exact (internalHomData F G).map_app_comp_π
    η.natTrans (internalHomData F G') c j

/-- Evaluation for the end-based Day internal Hom. -/
@[expose]
noncomputable def evaluation (F : C ⊛⥤ V) :
    internalHom F ⋙ tensorLeft F ⟶ 𝟭 (C ⊛⥤ V) := by
  letI (X Y : C ⊛⥤ V) : DayConvolution X.functor Y.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (C ⊛⥤ V) X Y
  let endData (G : C ⊛⥤ V) :
      DayConvolutionInternalHom F.functor G.functor (((internalHom F).obj G).functor) :=
    { π := fun c j ↦ end_.π
        ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) j
      hπ := fun c _ _ f ↦ end_.condition
        ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) f
      isLimitWedge := fun c ↦ by
        apply IsLimit.ofIsoLimit (limit.isLimit _)
        exact Multifork.isoOfι
          (Multiequalizer.multifork
            (multicospanIndexEnd
              ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c)))
      map_comp_π := fun f j ↦ by
        change end_.map
            (((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f) ≫
              end_.π
                ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj _) j =
          end_.π
              ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj _) j ≫
            ((((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f).app
              (.op j)).app j
        exact end_.map_π
          (((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f) j }
  exact
    { app := fun G ↦ ⟨(endData G).ev_app⟩
      naturality := by
        intro G G' η
        apply DayFunctor.hom_ext
        change (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
              (F ◁ (internalHom F).map η) ≫
            (internalHomData F G').ev_app =
          (internalHomData F G).ev_app ≫ η.natTrans
        rw [← id_tensorHom]
        rw [LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
        exact (internalHomData F G).ev_naturality_app
          (internalHomData F G') η.natTrans }

/-- Coevaluation for the end-based Day internal Hom. -/
@[expose]
noncomputable def coevaluation (F : C ⊛⥤ V) :
    𝟭 (C ⊛⥤ V) ⟶ tensorLeft F ⋙ internalHom F := by
  letI (X Y : C ⊛⥤ V) : DayConvolution X.functor Y.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (C ⊛⥤ V) X Y
  let endData (G : C ⊛⥤ V) :
      DayConvolutionInternalHom F.functor G.functor (((internalHom F).obj G).functor) :=
    { π := fun c j ↦ end_.π
        ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) j
      hπ := fun c _ _ f ↦ end_.condition
        ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c) f
      isLimitWedge := fun c ↦ by
        apply IsLimit.ofIsoLimit (limit.isLimit _)
        exact Multifork.isoOfι
          (Multiequalizer.multifork
            (multicospanIndexEnd
              ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj c)))
      map_comp_π := fun f j ↦ by
        change end_.map
            (((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f) ≫
              end_.π
                ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj _) j =
          end_.π
              ((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor |>.obj _) j ≫
            ((((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f).app
              (.op j)).app j
        exact end_.map_π
          (((dayConvolutionInternalHomDiagramFunctor F.functor).obj G.functor).map f) j }
  exact
    { app := fun G ↦ ⟨(endData (F ⊗ G)).coev_app⟩
      naturality := by
        intro G G' η
        apply DayFunctor.hom_ext
        change η.natTrans ≫ (internalHomData F (F ⊗ G')).coev_app =
          (internalHomData F (F ⊗ G)).coev_app ≫
            (internalHomData F (F ⊗ G)).map
              ((LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
                (F ◁ η))
              (internalHomData F (F ⊗ G'))
        rw [← id_tensorHom]
        rw [LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
        exact (internalHomData F (F ⊗ G)).coev_naturality_app
          η.natTrans (internalHomData F (F ⊗ G')) }

private theorem left_triangle (F G : C ⊛⥤ V) :
    (tensorLeft F).map ((coevaluation F).app G) ≫
        (evaluation F).app ((tensorLeft F).obj G) =
      𝟙 ((tensorLeft F).obj G) := by
  let (X Y : C ⊛⥤ V) : DayConvolution X.functor Y.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (C ⊛⥤ V) X Y
  apply DayFunctor.hom_ext
  simp only [DayFunctor.comp_natTrans, DayFunctor.id_natTrans]
  change (LawfulDayConvolutionMonoidalCategoryStruct.ι C V (C ⊛⥤ V)).map
        (F ◁ (coevaluation F).app G) ≫
      (internalHomData F (F ⊗ G)).ev_app =
    𝟙 (F.functor ⊛ G.functor)
  rw [← id_tensorHom]
  rw [LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
  exact DayConvolutionInternalHom.left_triangle_components G.functor
    (internalHomData F (F ⊗ G))

private theorem right_triangle (F G : C ⊛⥤ V) :
    (coevaluation F).app ((internalHom F).obj G) ≫
        (internalHom F).map ((evaluation F).app G) =
      𝟙 ((internalHom F).obj G) := by
  let (X Y : C ⊛⥤ V) : DayConvolution X.functor Y.functor :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (C ⊛⥤ V) X Y
  apply DayFunctor.hom_ext
  simp only [DayFunctor.comp_natTrans, DayFunctor.id_natTrans]
  change (internalHomData F (F ⊗ (internalHom F).obj G)).coev_app ≫
      (internalHomData F (F ⊗ (internalHom F).obj G)).map
        (internalHomData F G).ev_app (internalHomData F G) =
    𝟙 (internalHomObj F G)
  exact DayConvolutionInternalHom.right_triangle_components G.functor
    (internalHomData F G) (internalHomData F (F ⊗ (internalHom F).obj G))

/-- Tensoring on the left by `F` is left adjoint to the end-based internal Hom. -/
@[expose]
noncomputable def internalHomAdjunction (F : C ⊛⥤ V) :
    tensorLeft F ⊣ internalHom F where
  unit := coevaluation F
  counit := evaluation F
  left_triangle_components := by exact left_triangle F
  right_triangle_components := by exact right_triangle F

/-- The DayFunctor category is monoidal closed whenever the generated pointwise ends exist. -/
noncomputable instance instMonoidalClosed : MonoidalClosed (C ⊛⥤ V) where
  closed F :=
    { rightAdj := internalHom F
      adj := internalHomAdjunction F }

end Closed

end CategoryTheory.MonoidalCategory.DayFunctor
