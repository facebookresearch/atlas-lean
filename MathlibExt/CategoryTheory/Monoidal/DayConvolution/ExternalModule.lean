/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.MonoidLax
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.KanExtension
public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Descent of complete external module actions through Day convolution

The action is an ordinary natural transformation on the two original index
variables. Its external unit and associativity laws retain the index unitors
and associator. The Day action is its actual left Kan extension descent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uI vI uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped ExternalProduct CategoryTheory.MonObj

namespace CategoryTheory.MonoidalCategory.DayFunctor.ExternalModule

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [∀ F G : I ⥤ V, (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (X : V) (i : I), PreservesColimitsOfShape (CostructuredArrow (tensor I) i) (tensorLeft X)]
  [∀ (X : V) (i : I), PreservesColimitsOfShape (CostructuredArrow (tensor I) i) (tensorRight X)]
  [∀ (X : V) (i : I),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) i) (tensorLeft X)]
  [∀ (X : V) (i : I),
    PreservesColimitsOfShape (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) i) (tensorRight X)]
  [∀ (X : V) (i : I × I),
    PreservesColimitsOfShape (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) i)
      (tensorRight X)]
  [∀ (X : V) (i : I × I),
    PreservesColimitsOfShape (CostructuredArrow ((tensor I).prod (𝟭 I)) i) (tensorRight X)]

variable (S : DayFunctor I V) [MonObj S]

/-- Complete external module data on the original index and value categories. -/
structure Data where
  /-- The unchanged indexed objects and maps. -/
  diagram : I ⥤ V
  /-- The complete two-variable coefficient action. -/
  action : S.functor ⊠ diagram ⟶ tensor I ⋙ diagram
  /-- The external unit acts through both original unitors. -/
  unit (n : I) :
    ((DayFunctor.ν I V ≫ η[S].natTrans.app (𝟙_ I)) ▷ diagram.obj n) ≫
      action.app (𝟙_ I, n) = (λ_ (diagram.obj n)).hom ≫ diagram.map (λ_ n).inv
  /-- External associativity uses the actual scalar multiplication and index associator. -/
  assoc (a b n : I) :
    (((DayFunctor.η S S).app (a, b) ≫ μ[S].natTrans.app (a ⊗ b)) ▷ diagram.obj n) ≫
      action.app (a ⊗ b, n) =
    (α_ (S.functor.obj a) (S.functor.obj b) (diagram.obj n)).hom ≫
      (S.functor.obj a ◁ action.app (b, n)) ≫ action.app (a, b ⊗ n) ≫
      diagram.map (α_ a b n).inv

namespace Data

variable {S}

/-- The same underlying diagram with its existing Day wrapper. -/
abbrev sequence (d : Data S) : DayFunctor I V := DayFunctor.mk d.diagram

/-- The entire external action descends through the actual Day universal property. -/
def smul (d : Data S) : S ⊗ d.sequence ⟶ d.sequence := DayFunctor.tensorDesc d.action

/-- Every full Day generator retains the original external coefficient action. -/
theorem smul_generator (d : Data S) (a n : I) :
    (DayFunctor.η S d.sequence).app (a, n) ≫ d.smul.natTrans.app (a ⊗ n) =
      d.action.app (a, n) :=
  DayFunctor.η_comp_tensorDesc_app (F := S) (G := d.sequence) (H := d.sequence) d.action a n

/-- The full descended action has its actual internal module-unit equation. -/
theorem one_smul (d : Data S) :
    η[S] ▷ d.sequence ≫ d.smul = (λ_ d.sequence).hom := by
  apply DayFunctor.hom_ext
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := (𝟙_ (DayFunctor I V) ⊗ d.sequence).functor)
    (α := DayFunctor.η (𝟙_ (DayFunctor I V)) d.sequence)
  let _ : ((𝟙_ (DayFunctor I V)).functor ⊠ d.sequence.functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft (𝟙_ (DayFunctor I V)).functor
        (DayFunctor.νNatTrans I V) d.sequence.functor) :=
    (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft
      (𝟙_ (DayFunctor I V)).functor (DayFunctor.νNatTrans I V) d.sequence.functor
      (LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit
        I V (DayFunctor I V))).isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := (𝟙_ (DayFunctor I V)).functor ⊠ d.sequence.functor)
    (α := ExternalProduct.extensionUnitLeft (𝟙_ (DayFunctor I V)).functor
      (DayFunctor.νNatTrans I V) d.sequence.functor)
  ext ⟨u, n⟩
  rcases u with ⟨u⟩
  rcases u with ⟨⟩
  dsimp [ExternalProduct.extensionUnitLeft, DayFunctor.νNatTrans]
  simp only [whiskerLeft_id, Category.comp_id]
  have hw : (DayFunctor.η (𝟙_ (DayFunctor I V)) d.sequence).app (𝟙_ I, n) ≫
      (η[S] ▷ d.sequence).natTrans.app ((𝟙_ I) ⊗ n) =
    (η[S].natTrans.app (𝟙_ I) ▷ d.diagram.obj n) ≫
      (DayFunctor.η S d.sequence).app (𝟙_ I, n) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      I V η[S] d.sequence (𝟙_ I) n
  slice_lhs 2 3 => rw [hw]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [smul_generator]
  slice_lhs 1 2 => rw [← comp_whiskerRight]
  have hu := d.unit n
  have hl : DayFunctor.ν I V ▷ d.diagram.obj n ≫
      (DayFunctor.η (𝟙_ (DayFunctor I V)) d.sequence).app (𝟙_ I, n) ≫
      (λ_ d.sequence).hom.natTrans.app ((𝟙_ I) ⊗ n) =
    (λ_ (d.diagram.obj n)).hom ≫ d.diagram.map (λ_ n).inv :=
    LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app V d.sequence n
  exact hu.trans hl.symm

/-- The complete external associativity equation gives the actual internal module equation. -/
theorem mul_smul (d : Data S) :
    μ[S] ▷ d.sequence ≫ d.smul = (α_ S S d.sequence).hom ≫ S ◁ d.smul ≫ d.smul := by
  apply DayFunctor.hom_ext
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := ((S ⊗ S) ⊗ d.sequence).functor)
    (α := DayFunctor.η (S ⊗ S) d.sequence)
  let _ : ((S ⊗ S).functor ⊠ d.sequence.functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft (S ⊗ S).functor (DayFunctor.η S S) d.sequence.functor) :=
    (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft
      (S ⊗ S).functor (DayFunctor.η S S) d.sequence.functor
      (LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
        S S)).isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := (S ⊗ S).functor ⊠ d.sequence.functor)
    (α := ExternalProduct.extensionUnitLeft
      (S ⊗ S).functor (DayFunctor.η S S) d.sequence.functor)
  ext ⟨⟨a, b⟩, n⟩
  dsimp [ExternalProduct.extensionUnitLeft]
  simp only [whiskerLeft_id, Category.comp_id]
  have hw : (DayFunctor.η (S ⊗ S) d.sequence).app (a ⊗ b, n) ≫
      (μ[S] ▷ d.sequence).natTrans.app ((a ⊗ b) ⊗ n) =
    (μ[S].natTrans.app (a ⊗ b) ▷ d.diagram.obj n) ≫
      (DayFunctor.η S d.sequence).app (a ⊗ b, n) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      I V μ[S] d.sequence (a ⊗ b) n
  slice_lhs 2 3 => rw [hw]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [smul_generator]
  slice_lhs 1 2 => rw [← comp_whiskerRight]
  have ha : (DayFunctor.η S S).app (a, b) ▷ d.diagram.obj n ≫
      (DayFunctor.η (S ⊗ S) d.sequence).app (a ⊗ b, n) ≫
      (α_ S S d.sequence).hom.natTrans.app ((a ⊗ b) ⊗ n) =
    (α_ (S.functor.obj a) (S.functor.obj b) (d.diagram.obj n)).hom ≫
      (S.functor.obj a ◁ (DayFunctor.η S d.sequence).app (b, n)) ≫
      (DayFunctor.η S (S ⊗ d.sequence)).app (a, b ⊗ n) ≫
      (S ⊗ (S ⊗ d.sequence)).functor.map (α_ a b n).inv := by
    simpa only [DayFunctor.η] using!
      LawfulDayConvolutionMonoidalCategoryStruct.associator_hom_unit_unit V S S d.sequence a b n
  slice_rhs 1 3 => rw [ha]
  simp only [Category.assoc]
  slice_rhs 4 5 => rw [(S ◁ d.smul).natTrans.naturality (α_ a b n).inv]
  slice_rhs 5 6 => rw [d.smul.natTrans.naturality (α_ a b n).inv]
  have hm : (DayFunctor.η S (S ⊗ d.sequence)).app (a, b ⊗ n) ≫
      (S ◁ d.smul).natTrans.app (a ⊗ (b ⊗ n)) =
    (S.functor.obj a ◁ d.smul.natTrans.app (b ⊗ n)) ≫
      (DayFunctor.η S d.sequence).app (a, b ⊗ n) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      V S d.smul a (b ⊗ n)
  slice_rhs 3 4 => rw [hm]
  simp only [Category.assoc]
  slice_rhs 4 5 => rw [smul_generator]
  slice_rhs 2 3 => rw [← whiskerLeft_comp, smul_generator]
  simpa only [Category.assoc] using d.assoc a b n

/-- The complete descended action is a genuine module on the unchanged Day carrier. -/
def toModule (d : Data S) : Mod (DayFunctor I V) S where
  X := d.sequence
  mod := { smul := d.smul, one_smul := d.one_smul, mul_smul := d.mul_smul }

/-- The module constructor retains every original full action coefficient. -/
theorem toModule_generator (d : Data S) (a n : I) :
    (DayFunctor.η S d.toModule.X).app (a, n) ≫
      d.toModule.mod.smul.natTrans.app (a ⊗ n) = d.action.app (a, n) := d.smul_generator a n

end Data

end CategoryTheory.MonoidalCategory.DayFunctor.ExternalModule
