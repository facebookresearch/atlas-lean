/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.IndexKanComposition
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SelectedDayInstances
import MathlibExt.CategoryTheory.Monoidal.Sequence.TensorPower
import MathlibExt.CategoryTheory.Operad.FinBijDegreeInclusion
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.MonoidLax
import MathlibExt.CategoryTheory.Monoidal.Mod.Functor
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# The original topological sequential/symmetric induction presentation

Symmetrization is the actual left Kan extension from the ordered degree
index to the finite-bijection index. Its coefficients carry the full regular
permutation action. The tensor algebra map to the original sphere monoid
and balanced extension of scalars give the sequential/symmetric left adjoint.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison

attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided
  originalSymmetricSequenceSymmetric

local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

export CategoryTheory.Operad.SmallFinBijGroupoid
  (card degreeInclusion degreeInclusion_original degreeInclusion_obj
    degreeArrowEquality degreeInclusion_map_finite finiteArrow_ext
    degreeInclusion_associator degreeInclusion_leftUnitor degreeInclusion_rightUnitor
    degreeInclusion_associator_inv degreeInclusion_leftUnitor_inv degreeInclusion_rightUnitor_inv
    degreeUnitIso degreeTensorIso degreeInclusionCoreMonoidal degreeInclusionMonoidal)

attribute [local instance] degreeInclusionMonoidal

alias day_tensor_generator := CategoryTheory.MonoidalCategory.DayFunctor.tensorHom_η
alias dayMonoid_hom_of_coefficients :=
  CategoryTheory.MonoidalCategory.DayFunctor.Monoid.isMonHom_of_coefficients
alias day_scalar_action_pair := CategoryTheory.MonoidalCategory.DayFunctor.scalarAction_η

namespace CoefficientRestriction
universe uV vV
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The original complete ordinary degree restriction before the coefficient category is selected. -/
def R : DayFunctor I V ⥤ DayFunctor N V where
  obj X :=
    DayFunctor.mk
      { obj a := X.functor.obj (degreeInclusion.obj a)
        map f := X.functor.map (degreeInclusion.map f)
        map_id a := (degreeInclusion ⋙ X.functor).map_id a
        map_comp f g := (degreeInclusion ⋙ X.functor).map_comp f g }
  map f :=
    { natTrans :=
        { app a := f.natTrans.app (degreeInclusion.obj a)
          naturality a b g := f.natTrans.naturality (degreeInclusion.map g) } }

omit [SymmetricCategory V] [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The directly stored restriction has the entire original composite functor data. -/
theorem R_original : R (V := V) =
    (DayFunctor.equiv I V).functor ⋙ (whiskeringLeft N I V).obj degreeInclusion ⋙
      (DayFunctor.equiv N V).inverse := rfl

omit [SymmetricCategory V] [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Every original restricted diagram has the identical full precomposition. -/
theorem R_diagram (X : DayFunctor I V) : (R.obj X).functor = degreeInclusion ⋙ X.functor := rfl

omit [SymmetricCategory V] [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Every original restricted arrow has the identical coefficient component. -/
theorem R_map_component {X Y : DayFunctor I V} (f : X ⟶ Y) (a : N) :
    (R.map f).natTrans.app a = f.natTrans.app (degreeInclusion.obj a) := rfl

/-- The original full degree comparison determines the restriction pair before any coefficient data. -/
def pairComponent (X Y : DayFunctor I V) (a b : N) :
    (R.obj X).functor.obj a ⊗ (R.obj Y).functor.obj b ⟶
      (R.obj (X ⊗ Y)).functor.obj (a ⊗ b) :=
  (DayFunctor.η X Y).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
    (X ⊗ Y).functor.map (degreeTensorIso a b).hom

/-- The complete original pair transformation at every ordered index. -/
def pair (X Y : DayFunctor I V) :
    (R.obj X).functor ⊠ (R.obj Y).functor ⟶ tensor N ⋙ (R.obj (X ⊗ Y)).functor where
  app p := pairComponent X Y p.1 p.2
  naturality := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ f
    have ha : a = a' := Discrete.ext (Discrete.eq_of_hom f.1)
    have hb : b = b' := Discrete.ext (Discrete.eq_of_hom f.2)
    subst a'
    subst b'
    have hf : f = 𝟙 (a, b) := by ext <;> exact Discrete.hom_eq
    cases hf
    exact (congrArg (fun q => q ≫ pairComponent X Y a b)
      (((R.obj X).functor ⊠ (R.obj Y).functor).map_id (a, b))).trans
      ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
        (congrArg (fun q => pairComponent X Y a b ≫ q)
          ((tensor N ⋙ (R.obj (X ⊗ Y)).functor).map_id (a, b)).symm)))

/-- The actual original pair descends through the same Day Kan extension. -/
def tensorator (X Y : DayFunctor I V) : R.obj X ⊗ R.obj Y ⟶ R.obj (X ⊗ Y) :=
  DayFunctor.tensorDesc (pair X Y)

omit [SymmetricCategory V] in
/-- Every complete Day generator has the original full restriction pair. -/
theorem tensorator_pair (X Y : DayFunctor I V) (a b : N) :
    (DayFunctor.η (R.obj X) (R.obj Y)).app (a, b) ≫ (tensorator X Y).natTrans.app (a ⊗ b) =
      pairComponent X Y a b := DayFunctor.η_comp_tensorDesc_app (pair X Y) a b

omit [SymmetricCategory V] in
/-- The original degree tensorator contributes its actual identity map at every pair. -/
theorem pairComponent_original (X Y : DayFunctor I V) (a b : N) :
    pairComponent X Y a b = (DayFunctor.η X Y).app (degreeInclusion.obj a, degreeInclusion.obj b) := by
  have h : (X ⊗ Y).functor.map (degreeTensorIso a b).hom =
      𝟙 ((X ⊗ Y).functor.obj (degreeInclusion.obj a ⊗ degreeInclusion.obj b)) :=
    (X ⊗ Y).functor.map_id _
  exact (congrArg (fun q => (DayFunctor.η X Y).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫ q) h).trans
    (Category.comp_id _)

/-- The original ordered powers and symmetric powers use the same coefficient object. -/
def A (K : V) : DayFunctor N V := CategoryTheory.Sequence.tensorPowerSequence K

omit [SymmetricCategory V] [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The shared original ordered-power constructor retains the whole tensor-power sequence. -/
theorem A_original (K : V) : A K = CategoryTheory.Sequence.tensorPowerSequence K := rfl

/-- The original symmetric tensor-power diagram. -/
def S (K : V) : DayFunctor I V :=
  DayFunctor.mk (Operad.SmallFinBijGroupoid.tensorPowerFunctor K)

omit [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The shared original symmetric-power constructor retains every original map and coefficient. -/
theorem S_original (K : V) : S K = DayFunctor.mk (Operad.SmallFinBijGroupoid.tensorPowerFunctor K) := rfl

/-- The original ordered sphere inclusion before the actual coefficient category is selected. -/
def inclusion (K : V) : A K ⟶ R.obj (S K) where
  natTrans :=
    { app a := 𝟙 (TensorPower.tensorPowObj K (CategoryTheory.Sequence.degree a))
      naturality := by
        intro a b f
        have hab : a = b := Discrete.ext (Discrete.eq_of_hom f)
        subst b
        have hf : f = 𝟙 a := Discrete.hom_eq
        cases hf
        exact (congrArg (fun q => q ≫ 𝟙 _) ((A K).functor.map_id a)).trans
          ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
            (congrArg (fun q => 𝟙 _ ≫ q) ((R.obj (S K)).functor.map_id a).symm))) }

/-- The full original restriction pair formula for every original coefficient and action. -/
theorem originalActionPair (K : V) (X : DayFunctor I V) (s : S K ⊗ X ⟶ X) (a b : N) :
    (DayFunctor.η (A K) (R.obj X)).app (a, b) ≫
      ((inclusion K ▷ R.obj X) ≫ tensorator (S K) X ≫ R.map s).natTrans.app (a ⊗ b) =
    (DayFunctor.η (S K) X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      s.natTrans.app (degreeInclusion.obj (a ⊗ b)) := by
  have h := PointedCGWH.Spectra.SequentialSymmetricInductionComparison.day_scalar_action_pair
    (inclusion K) (tensorator (S K) X ≫ R.map s) a b
  have hi : ((inclusion K).natTrans.app a ⊗ₘ 𝟙 ((R.obj X).functor.obj b)) =
      𝟙 ((R.obj (S K)).functor.obj a ⊗ (R.obj X).functor.obj b) :=
    MonoidalCategory.id_tensorHom_id _ _
  have hcomp : (tensorator (S K) X ≫ R.map s).natTrans.app (a ⊗ b) =
      (tensorator (S K) X).natTrans.app (a ⊗ b) ≫ (R.map s).natTrans.app (a ⊗ b) := rfl
  exact h.trans ((congrArg (fun q => q ≫
      (DayFunctor.η (R.obj (S K)) (R.obj X)).app (a, b) ≫
        (tensorator (S K) X ≫ R.map s).natTrans.app (a ⊗ b)) hi).trans
    ((Category.id_comp _).trans
      ((congrArg (fun q => (DayFunctor.η (R.obj (S K)) (R.obj X)).app (a, b) ≫ q) hcomp).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ (R.map s).natTrans.app (a ⊗ b)) (tensorator_pair (S K) X a b)).trans
            ((congrArg (fun q => q ≫ (R.map s).natTrans.app (a ⊗ b)) (pairComponent_original (S K) X a b)).trans
              (congrArg (fun q => (DayFunctor.η (S K) X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫ q)
                (R_map_component s (a ⊗ b)))))))))
/-- The original full restricted action with all component data stored before selecting the coefficient category. -/
def action (K : V) (X : DayFunctor I V) (s : S K ⊗ X ⟶ X) : A K ⊗ R.obj X ⟶ R.obj X where
  natTrans :=
    { app a := (inclusion K ▷ R.obj X).natTrans.app a ≫
        (tensorator (S K) X).natTrans.app a ≫ s.natTrans.app (degreeInclusion.obj a)
      naturality := ((inclusion K ▷ R.obj X) ≫ tensorator (S K) X ≫ R.map s).natTrans.naturality }

/-- The directly stored action is the complete original three-map action. -/
theorem action_original (K : V) (X : DayFunctor I V) (s : S K ⊗ X ⟶ X) :
    action K X s = (inclusion K ▷ R.obj X) ≫ tensorator (S K) X ≫ R.map s := rfl

/-- Every original action component retains the same full original ordered pair. -/
theorem action_pair (K : V) (X : DayFunctor I V) (s : S K ⊗ X ⟶ X) (a b : N) :
    (DayFunctor.η (A K) (R.obj X)).app (a, b) ≫ (action K X s).natTrans.app (a ⊗ b) =
      (DayFunctor.η (S K) X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
        s.natTrans.app (degreeInclusion.obj (a ⊗ b)) :=
  originalActionPair K X s a b
end CoefficientRestriction


/-- The entire original ordinary left Kan functor gives free symmetrization. -/
def G : CategoryTheory.Sequence PointedCGWH.{u, v} ⥤ SymmetricSequence.{u, v} :=
  (DayFunctor.equiv N PointedCGWH.{u, v}).functor ⋙ degreeInclusion.lan ⋙
    (DayFunctor.equiv I PointedCGWH.{u, v}).inverse

/-- The original right adjoint forgets every permutation and keeps each degree. -/
def U : SymmetricSequence.{u, v} ⥤ CategoryTheory.Sequence PointedCGWH.{u, v} :=
  CoefficientRestriction.R (V := PointedCGWH.{u, v})

/-- Symmetrization and full sequence restriction are the original Kan adjunction. -/
def sequenceAdjunction : G.{u, v} ⊣ U.{u, v} :=
  (((DayFunctor.equiv N PointedCGWH.{u, v}).toAdjunction).comp (degreeInclusion.lanAdjunction PointedCGWH.{u, v})).comp
    (DayFunctor.equiv I PointedCGWH.{u, v}).symm.toAdjunction

/-- The underlying diagram of `G` is the same entire chosen ordinary left Kan extension. -/
theorem G_diagram (X : CategoryTheory.Sequence PointedCGWH.{u, v}) :
    (G.obj X).functor = degreeInclusion.leftKanExtension X.functor := rfl

/-- The right adjoint keeps the whole original diagram at the ordered degree inclusion. -/
theorem U_diagram (Y : SymmetricSequence.{u, v}) :
    (U.obj Y).functor = degreeInclusion ⋙ Y.functor := rfl

/-- Every original restriction morphism has its identical coefficient component. -/
theorem U_map_component {X Y : SymmetricSequence.{u, v}} (f : X ⟶ Y) (n : N) :
    (U.map f).natTrans.app n = f.natTrans.app (degreeInclusion.obj n) := rfl

/-- The original ordered restriction tensorator on a complete pair of coefficient levels. -/
def restrictionPairComponent (X Y : SymmetricSequence.{u, v}) (a b : N) :
    (U.obj X).functor.obj a ⊗ (U.obj Y).functor.obj b ⟶
      (U.obj (X ⊗ Y)).functor.obj (a ⊗ b) :=
  CoefficientRestriction.pairComponent X Y a b

/-- The original pair tensorator respects every ordered index arrow. -/
def restrictionPair (X Y : SymmetricSequence.{u, v}) :
    (U.obj X).functor ⊠ (U.obj Y).functor ⟶ tensor N ⋙ (U.obj (X ⊗ Y)).functor :=
  CoefficientRestriction.pair X Y

/-- The actual Day restriction tensorator is induced by the full ordered pair transformation. -/
def Uμ (X Y : SymmetricSequence.{u, v}) : U.obj X ⊗ U.obj Y ⟶ U.obj (X ⊗ Y) :=
  CoefficientRestriction.tensorator X Y

/-- The original restriction tensorator retains every native ordered pair generator. -/
@[reassoc]
theorem Uμ_pair (X Y : SymmetricSequence.{u, v}) (a b : N) :
    (DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ≫ (Uμ X Y).natTrans.app (a ⊗ b) =
      restrictionPairComponent X Y a b := DayFunctor.η_comp_tensorDesc_app (restrictionPair X Y) a b

/-- The original degree-zero unit coefficient of restriction. -/
def restrictionUnitComponent : 𝟙_ PointedCGWH.{u, v} ⟶
    (U.obj (𝟙_ SymmetricSequence.{u, v})).functor.obj (𝟙_ N) :=
  DayFunctor.ν I PointedCGWH.{u, v} ≫
    (𝟙_ SymmetricSequence.{u, v}).functor.map degreeUnitIso.hom

/-- The actual ordered Day unit map induced by the original degree-zero coefficient. -/
def Uε : 𝟙_ (CategoryTheory.Sequence PointedCGWH.{u, v}) ⟶
    U.obj (𝟙_ SymmetricSequence.{u, v}) := DayFunctor.unitDesc restrictionUnitComponent

/-- The complete original unit map retains its original coefficient generator. -/
@[reassoc]
theorem Uε_unit : DayFunctor.ν N PointedCGWH.{u, v} ≫ Uε.natTrans.app (𝟙_ N) =
    restrictionUnitComponent := DayFunctor.ν_comp_unitDesc restrictionUnitComponent

/-- Every original symmetric coefficient map commutes with the complete ordered left pair map. -/
@[reassoc]
theorem restrictionPair_natural_left {X Y : SymmetricSequence.{u, v}} (f : X ⟶ Y)
    (Z : SymmetricSequence.{u, v}) (a b : N) :
    (f.natTrans.app (degreeInclusion.obj a) ▷ Z.functor.obj (degreeInclusion.obj b)) ≫
      restrictionPairComponent Y Z a b =
    restrictionPairComponent X Z a b ≫ (f ▷ Z).natTrans.app (degreeInclusion.obj (a ⊗ b)) := by
  have hη : (DayFunctor.η X Z).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      (f ▷ Z).natTrans.app (degreeInclusion.obj a ⊗ degreeInclusion.obj b) =
      (f.natTrans.app (degreeInclusion.obj a) ▷ Z.functor.obj (degreeInclusion.obj b)) ≫
        (DayFunctor.η Y Z).app (degreeInclusion.obj a, degreeInclusion.obj b) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      I PointedCGWH.{u, v} f Z (degreeInclusion.obj a) (degreeInclusion.obj b)
  have hn := (f ▷ Z).natTrans.naturality (degreeTensorIso a b).hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (Y ⊗ Z).functor.map (degreeTensorIso a b).hom) hη.symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun g => (DayFunctor.η X Z).app
          (degreeInclusion.obj a, degreeInclusion.obj b) ≫ g) hn.symm)))

/-- Every original symmetric coefficient map commutes with the complete ordered right pair map. -/
@[reassoc]
theorem restrictionPair_natural_right (X : SymmetricSequence.{u, v})
    {Y Z : SymmetricSequence.{u, v}} (f : Y ⟶ Z) (a b : N) :
    (X.functor.obj (degreeInclusion.obj a) ◁ f.natTrans.app (degreeInclusion.obj b)) ≫
      restrictionPairComponent X Z a b =
    restrictionPairComponent X Y a b ≫ (X ◁ f).natTrans.app (degreeInclusion.obj (a ⊗ b)) := by
  have hη : (DayFunctor.η X Y).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      (X ◁ f).natTrans.app (degreeInclusion.obj a ⊗ degreeInclusion.obj b) =
      (X.functor.obj (degreeInclusion.obj a) ◁ f.natTrans.app (degreeInclusion.obj b)) ≫
        (DayFunctor.η X Z).app (degreeInclusion.obj a, degreeInclusion.obj b) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      PointedCGWH.{u, v} X f (degreeInclusion.obj a) (degreeInclusion.obj b)
  have hn := (X ◁ f).natTrans.naturality (degreeTensorIso a b).hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (X ⊗ Z).functor.map (degreeTensorIso a b).hom) hη.symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun g => (DayFunctor.η X Y).app
          (degreeInclusion.obj a, degreeInclusion.obj b) ≫ g) hn.symm)))

/-- The whole left naturality of the original restriction tensorator retains every coefficient map. -/
theorem Uμ_natural_left {X Y : SymmetricSequence.{u, v}} (f : X ⟶ Y)
    (Z : SymmetricSequence.{u, v}) :
    U.map f ▷ U.obj Z ≫ Uμ Y Z = Uμ X Z ≫ U.map (f ▷ Z) := by
  apply DayFunctor.tensor_hom_ext
  intro a b
  change (DayFunctor.η (U.obj X) (U.obj Z)).app (a, b) ≫
      (U.map f ▷ U.obj Z).natTrans.app (a ⊗ b) ≫ (Uμ Y Z).natTrans.app (a ⊗ b) =
    (DayFunctor.η (U.obj X) (U.obj Z)).app (a, b) ≫ (Uμ X Z).natTrans.app (a ⊗ b) ≫
      (U.map (f ▷ Z)).natTrans.app (a ⊗ b)
  have hη : (DayFunctor.η (U.obj X) (U.obj Z)).app (a, b) ≫
      (U.map f ▷ U.obj Z).natTrans.app (a ⊗ b) =
      (f.natTrans.app (degreeInclusion.obj a) ▷ Z.functor.obj (degreeInclusion.obj b)) ≫
        (DayFunctor.η (U.obj Y) (U.obj Z)).app (a, b) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      N PointedCGWH.{u, v} (U.map f) (U.obj Z) a b
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (Uμ Y Z).natTrans.app (a ⊗ b)) hη).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g =>
          (f.natTrans.app (degreeInclusion.obj a) ▷ Z.functor.obj (degreeInclusion.obj b)) ≫ g)
          (Uμ_pair Y Z a b)).trans
            ((restrictionPair_natural_left f Z a b).trans
              ((congrArg (fun g => g ≫ (U.map (f ▷ Z)).natTrans.app (a ⊗ b))
                (Uμ_pair X Z a b).symm).trans (Category.assoc _ _ _))))))

/-- The whole right naturality of the original restriction tensorator retains every coefficient map. -/
theorem Uμ_natural_right (X : SymmetricSequence.{u, v}) {Y Z : SymmetricSequence.{u, v}} (f : Y ⟶ Z) :
    U.obj X ◁ U.map f ≫ Uμ X Z = Uμ X Y ≫ U.map (X ◁ f) := by
  apply DayFunctor.tensor_hom_ext
  intro a b
  change (DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ≫
      (U.obj X ◁ U.map f).natTrans.app (a ⊗ b) ≫ (Uμ X Z).natTrans.app (a ⊗ b) =
    (DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ≫ (Uμ X Y).natTrans.app (a ⊗ b) ≫
      (U.map (X ◁ f)).natTrans.app (a ⊗ b)
  have hη : (DayFunctor.η (U.obj X) (U.obj Y)).app (a, b) ≫
      (U.obj X ◁ U.map f).natTrans.app (a ⊗ b) =
      (X.functor.obj (degreeInclusion.obj a) ◁ f.natTrans.app (degreeInclusion.obj b)) ≫
        (DayFunctor.η (U.obj X) (U.obj Z)).app (a, b) :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      PointedCGWH.{u, v} (U.obj X) (U.map f) a b
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (Uμ X Z).natTrans.app (a ⊗ b)) hη).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g =>
          (X.functor.obj (degreeInclusion.obj a) ◁ f.natTrans.app (degreeInclusion.obj b)) ≫ g)
          (Uμ_pair X Z a b)).trans
            ((restrictionPair_natural_right X f a b).trans
              ((congrArg (fun g => g ≫ (U.map (X ◁ f)).natTrans.app (a ⊗ b))
                (Uμ_pair X Y a b).symm).trans (Category.assoc _ _ _))))))

/-- The original ordered pair comparison has the unchanged native Day coefficient map. -/
theorem restrictionPairComponent_eq (X Y : SymmetricSequence.{u, v}) (a b : N) :
    restrictionPairComponent X Y a b =
      (DayFunctor.η X Y).app (degreeInclusion.obj a, degreeInclusion.obj b) := by
  have h : (X ⊗ Y).functor.map (degreeTensorIso a b).hom =
      𝟙 ((X ⊗ Y).functor.obj (degreeInclusion.obj a ⊗ degreeInclusion.obj b)) :=
    (X ⊗ Y).functor.map_id (degreeInclusion.obj a ⊗ degreeInclusion.obj b)
  exact (congrArg (fun g =>
    (DayFunctor.η X Y).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫ g) h).trans
      (Category.comp_id _)

/-- The degree-zero restriction coefficient is the same entire original symmetric Day unit map. -/
theorem restrictionUnitComponent_eq : restrictionUnitComponent.{u, v} =
    DayFunctor.ν I PointedCGWH.{u, v} := by
  have h : (𝟙_ SymmetricSequence.{u, v}).functor.map degreeUnitIso.hom =
      𝟙 ((𝟙_ SymmetricSequence.{u, v}).functor.obj (𝟙_ I)) :=
    (𝟙_ SymmetricSequence.{u, v}).functor.map_id (𝟙_ I)
  exact (congrArg (fun g => DayFunctor.ν I PointedCGWH.{u, v} ≫ g) h).trans (Category.comp_id _)

/-- The complete original ordered pair maps preserve the native Day associator. -/
theorem restrictionPair_associativity (X Y Z : SymmetricSequence.{u, v}) (a b c : N) :
    (restrictionPairComponent X Y a b ▷ Z.functor.obj (degreeInclusion.obj c)) ≫
      restrictionPairComponent (X ⊗ Y) Z (a ⊗ b) c ≫
        (α_ X Y Z).hom.natTrans.app (degreeInclusion.obj ((a ⊗ b) ⊗ c)) =
    (α_ (X.functor.obj (degreeInclusion.obj a)) (Y.functor.obj (degreeInclusion.obj b))
      (Z.functor.obj (degreeInclusion.obj c))).hom ≫
      (X.functor.obj (degreeInclusion.obj a) ◁ restrictionPairComponent Y Z b c) ≫
        restrictionPairComponent X (Y ⊗ Z) a (b ⊗ c) ≫
          (U.obj (X ⊗ (Y ⊗ Z))).functor.map (α_ a b c).inv := by
  let ja := degreeInclusion.obj a
  let jb := degreeInclusion.obj b
  let jc := degreeInclusion.obj c
  have hl : (restrictionPairComponent X Y a b ▷ Z.functor.obj jc) ≫
      restrictionPairComponent (X ⊗ Y) Z (a ⊗ b) c ≫
        (α_ X Y Z).hom.natTrans.app ((ja ⊗ jb) ⊗ jc) =
      ((DayFunctor.η X Y).app (ja, jb) ▷ Z.functor.obj jc) ≫
        (DayFunctor.η (X ⊗ Y) Z).app (ja ⊗ jb, jc) ≫
          (α_ X Y Z).hom.natTrans.app ((ja ⊗ jb) ⊗ jc) :=
    congrArg₂ (fun
      (f : X.functor.obj ja ⊗ Y.functor.obj jb ⟶ (X ⊗ Y).functor.obj (ja ⊗ jb))
      (g : (X ⊗ Y).functor.obj (ja ⊗ jb) ⊗ Z.functor.obj jc ⟶
        ((X ⊗ Y) ⊗ Z).functor.obj ((ja ⊗ jb) ⊗ jc)) =>
      (f ▷ Z.functor.obj jc) ≫ g ≫ (α_ X Y Z).hom.natTrans.app ((ja ⊗ jb) ⊗ jc))
      (restrictionPairComponent_eq X Y a b) (restrictionPairComponent_eq (X ⊗ Y) Z (a ⊗ b) c)
  have hmap : (U.obj (X ⊗ (Y ⊗ Z))).functor.map (α_ a b c).inv =
      (X ⊗ (Y ⊗ Z)).functor.map (α_ ja jb jc).inv :=
    congrArg (X ⊗ (Y ⊗ Z)).functor.map (degreeInclusion_associator_inv a b c)
  have hr₁ : (α_ (X.functor.obj ja) (Y.functor.obj jb) (Z.functor.obj jc)).hom ≫
      (X.functor.obj ja ◁ restrictionPairComponent Y Z b c) ≫
        restrictionPairComponent X (Y ⊗ Z) a (b ⊗ c) ≫
          (U.obj (X ⊗ (Y ⊗ Z))).functor.map (α_ a b c).inv =
    (α_ (X.functor.obj ja) (Y.functor.obj jb) (Z.functor.obj jc)).hom ≫
      (X.functor.obj ja ◁ (DayFunctor.η Y Z).app (jb, jc)) ≫
        (DayFunctor.η X (Y ⊗ Z)).app (ja, jb ⊗ jc) ≫
          (U.obj (X ⊗ (Y ⊗ Z))).functor.map (α_ a b c).inv :=
    congrArg₂ (fun
      (f : Y.functor.obj jb ⊗ Z.functor.obj jc ⟶ (Y ⊗ Z).functor.obj (jb ⊗ jc))
      (g : X.functor.obj ja ⊗ (Y ⊗ Z).functor.obj (jb ⊗ jc) ⟶
        (X ⊗ (Y ⊗ Z)).functor.obj (ja ⊗ (jb ⊗ jc))) =>
      (α_ (X.functor.obj ja) (Y.functor.obj jb) (Z.functor.obj jc)).hom ≫
        (X.functor.obj ja ◁ f) ≫ g ≫ (U.obj (X ⊗ (Y ⊗ Z))).functor.map (α_ a b c).inv)
      (restrictionPairComponent_eq Y Z b c) (restrictionPairComponent_eq X (Y ⊗ Z) a (b ⊗ c))
  have hr₂ := congrArg (fun g =>
    (α_ (X.functor.obj ja) (Y.functor.obj jb) (Z.functor.obj jc)).hom ≫
      (X.functor.obj ja ◁ (DayFunctor.η Y Z).app (jb, jc)) ≫
        (DayFunctor.η X (Y ⊗ Z)).app (ja, jb ⊗ jc) ≫ g) hmap
  have h := LawfulDayConvolutionMonoidalCategoryStruct.associator_hom_unit_unit
    PointedCGWH.{u, v} X Y Z ja jb jc
  exact hl.trans (h.trans (hr₁.trans hr₂).symm)

/-- The full original pair maps preserve the native empty-left-block unit map. -/
theorem restrictionPair_left_unit (X : SymmetricSequence.{u, v}) (a : N) :
    (restrictionUnitComponent ▷ X.functor.obj (degreeInclusion.obj a)) ≫
      restrictionPairComponent (𝟙_ SymmetricSequence.{u, v}) X (𝟙_ N) a ≫
        (λ_ X).hom.natTrans.app (degreeInclusion.obj ((𝟙_ N) ⊗ a)) =
    (λ_ (X.functor.obj (degreeInclusion.obj a))).hom ≫ (U.obj X).functor.map (λ_ a).inv := by
  let ja := degreeInclusion.obj a
  have hl : (restrictionUnitComponent ▷ X.functor.obj ja) ≫
      restrictionPairComponent (𝟙_ SymmetricSequence.{u, v}) X (𝟙_ N) a ≫
        (λ_ X).hom.natTrans.app ((𝟙_ I) ⊗ ja) =
      (DayFunctor.ν I PointedCGWH.{u, v} ▷ X.functor.obj ja) ≫
        (DayFunctor.η (𝟙_ SymmetricSequence.{u, v}) X).app ((𝟙_ I), ja) ≫
          (λ_ X).hom.natTrans.app ((𝟙_ I) ⊗ ja) :=
    congrArg₂ (fun
      (f : 𝟙_ PointedCGWH.{u, v} ⟶ (𝟙_ SymmetricSequence.{u, v}).functor.obj (𝟙_ I))
      (g : (𝟙_ SymmetricSequence.{u, v}).functor.obj (𝟙_ I) ⊗ X.functor.obj ja ⟶
        ((𝟙_ SymmetricSequence.{u, v}) ⊗ X).functor.obj ((𝟙_ I) ⊗ ja)) =>
      (f ▷ X.functor.obj ja) ≫ g ≫ (λ_ X).hom.natTrans.app ((𝟙_ I) ⊗ ja))
      restrictionUnitComponent_eq (restrictionPairComponent_eq _ X (𝟙_ N) a)
  have hr : (λ_ (X.functor.obj ja)).hom ≫ (U.obj X).functor.map (λ_ a).inv =
      (λ_ (X.functor.obj ja)).hom ≫ X.functor.map (λ_ ja).inv :=
    congrArg (fun g => (λ_ (X.functor.obj ja)).hom ≫ X.functor.map g)
      (degreeInclusion_leftUnitor_inv a)
  have h := LawfulDayConvolutionMonoidalCategoryStruct.leftUnitor_hom_unit_app
    PointedCGWH.{u, v} X ja
  exact hl.trans (h.trans hr.symm)

/-- The full original pair maps preserve the native empty-right-block unit map. -/
theorem restrictionPair_right_unit (X : SymmetricSequence.{u, v}) (a : N) :
    (X.functor.obj (degreeInclusion.obj a) ◁ restrictionUnitComponent) ≫
      restrictionPairComponent X (𝟙_ SymmetricSequence.{u, v}) a (𝟙_ N) ≫
        (ρ_ X).hom.natTrans.app (degreeInclusion.obj (a ⊗ (𝟙_ N))) =
    (ρ_ (X.functor.obj (degreeInclusion.obj a))).hom ≫ (U.obj X).functor.map (ρ_ a).inv := by
  let ja := degreeInclusion.obj a
  have hl : (X.functor.obj ja ◁ restrictionUnitComponent) ≫
      restrictionPairComponent X (𝟙_ SymmetricSequence.{u, v}) a (𝟙_ N) ≫
        (ρ_ X).hom.natTrans.app (ja ⊗ (𝟙_ I)) =
      (X.functor.obj ja ◁ DayFunctor.ν I PointedCGWH.{u, v}) ≫
        (DayFunctor.η X (𝟙_ SymmetricSequence.{u, v})).app (ja, (𝟙_ I)) ≫
          (ρ_ X).hom.natTrans.app (ja ⊗ (𝟙_ I)) :=
    congrArg₂ (fun
      (f : 𝟙_ PointedCGWH.{u, v} ⟶ (𝟙_ SymmetricSequence.{u, v}).functor.obj (𝟙_ I))
      (g : X.functor.obj ja ⊗ (𝟙_ SymmetricSequence.{u, v}).functor.obj (𝟙_ I) ⟶
        (X ⊗ (𝟙_ SymmetricSequence.{u, v})).functor.obj (ja ⊗ (𝟙_ I))) =>
      (X.functor.obj ja ◁ f) ≫ g ≫ (ρ_ X).hom.natTrans.app (ja ⊗ (𝟙_ I)))
      restrictionUnitComponent_eq (restrictionPairComponent_eq X _ a (𝟙_ N))
  have hr : (ρ_ (X.functor.obj ja)).hom ≫ (U.obj X).functor.map (ρ_ a).inv =
      (ρ_ (X.functor.obj ja)).hom ≫ X.functor.map (ρ_ ja).inv :=
    congrArg (fun g => (ρ_ (X.functor.obj ja)).hom ≫ X.functor.map g)
      (degreeInclusion_rightUnitor_inv a)
  have h := LawfulDayConvolutionMonoidalCategoryStruct.rightUnitor_hom_unit_app
    PointedCGWH.{u, v} X ja
  exact hl.trans (h.trans hr.symm)

/-- The actual original Kan coefficient before applying the Day wrapper. -/
def coefficientSource (X : CategoryTheory.Sequence PointedCGWH.{u, v}) (n : N) (m : I)
    (σ : degreeInclusion.obj n ⟶ m) :
    X.functor.obj n ⟶ (degreeInclusion.leftKanExtension X.functor).obj m :=
  (degreeInclusion.leftKanExtensionUnit X.functor).app n ≫
    (degreeInclusion.leftKanExtension X.functor).map σ

/-- Every full original permutation acts on the same unwrapped Kan coefficient. -/
@[reassoc]
theorem coefficientSource_permutation (X : CategoryTheory.Sequence PointedCGWH.{u, v}) (n : N)
    {m k : I} (σ : degreeInclusion.obj n ⟶ m) (τ : m ⟶ k) :
    coefficientSource X n m σ ≫ (degreeInclusion.leftKanExtension X.functor).map τ =
      coefficientSource X n k (σ ≫ τ) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f => (degreeInclusion.leftKanExtensionUnit X.functor).app n ≫ f)
      ((degreeInclusion.leftKanExtension X.functor).map_comp σ τ).symm)

/-- Every original coefficient transformation acts on the identical unwrapped Kan coefficient. -/
@[reassoc]
theorem coefficientSource_naturality {X Y : CategoryTheory.Sequence PointedCGWH.{u, v}}
    (f : X ⟶ Y) (n : N) (m : I) (σ : degreeInclusion.obj n ⟶ m) :
    coefficientSource X n m σ ≫ ((degreeInclusion.lan).map f.natTrans).app m =
      f.natTrans.app n ≫ coefficientSource Y n m σ := by
  have hu : f.natTrans.app n ≫ (degreeInclusion.leftKanExtensionUnit Y.functor).app n =
      (degreeInclusion.leftKanExtensionUnit X.functor).app n ≫
        ((degreeInclusion.lan).map f.natTrans).app (degreeInclusion.obj n) :=
    congrArg (fun t => t.app n) (degreeInclusion.lanUnit.naturality f.natTrans)
  have hn : (degreeInclusion.leftKanExtension X.functor).map σ ≫
      ((degreeInclusion.lan).map f.natTrans).app m =
      ((degreeInclusion.lan).map f.natTrans).app (degreeInclusion.obj n) ≫
        (degreeInclusion.leftKanExtension Y.functor).map σ :=
    ((degreeInclusion.lan).map f.natTrans).naturality σ
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (degreeInclusion.leftKanExtensionUnit X.functor).app n ≫ t) hn).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ (degreeInclusion.leftKanExtension Y.functor).map σ) hu.symm)))

/-- The original coefficient injection at an arbitrary full permutation label. -/
def coefficient (X : CategoryTheory.Sequence PointedCGWH.{u, v}) (n : N) (m : I)
    (σ : degreeInclusion.obj n ⟶ m) :
    X.functor.obj n ⟶ (G.obj X).functor.obj m := coefficientSource X n m σ

/-- Every full permutation acts by postcomposing the original coefficient label. -/
@[reassoc]
theorem coefficient_permutation (X : CategoryTheory.Sequence PointedCGWH.{u, v}) (n : N)
    {m k : I} (σ : degreeInclusion.obj n ⟶ m) (τ : m ⟶ k) :
    coefficient X n m σ ≫ (G.obj X).functor.map τ = coefficient X n k (σ ≫ τ) :=
  coefficientSource_permutation X n σ τ

/-- The original coefficient injection respects every ordered coefficient transformation. -/
@[reassoc]
theorem coefficient_naturality {X Y : CategoryTheory.Sequence PointedCGWH.{u, v}} (f : X ⟶ Y)
    (n : N) (m : I) (σ : degreeInclusion.obj n ⟶ m) :
    coefficient X n m σ ≫ (G.map f).natTrans.app m =
      f.natTrans.app n ≫ coefficient Y n m σ := coefficientSource_naturality f n m σ

/-- The full fibre of symmetrization is the discrete set of original permutation labels. -/
def fibreFunctor (m : I) : Discrete (card m.of.len ⟶ m) ⥤
    CostructuredArrow degreeInclusion m where
  obj σ := CostructuredArrow.mk (Y := CategoryTheory.Sequence.index m.of.len) σ.as
  map {σ τ} f := by
    have h : σ = τ := Discrete.ext (Discrete.eq_of_hom f)
    subst τ
    exact 𝟙 _
  map_id _ := by
    apply CostructuredArrow.hom_ext
    exact Discrete.hom_eq
  map_comp _ _ := by
    apply CostructuredArrow.hom_ext
    exact Discrete.hom_eq

/-- No balancing relation identifies distinct original labels in the degree fibre. -/
def fibreFullyFaithful (m : I) : (fibreFunctor m).FullyFaithful where
  preimage {σ τ} f := by
    have hf : f.left = 𝟙 (CategoryTheory.Sequence.index m.of.len) := Discrete.hom_eq
    have hw := CostructuredArrow.w f
    change degreeInclusion.map f.left ≫ τ.as = σ.as at hw
    have hi : degreeInclusion.map f.left = 𝟙 (card m.of.len) :=
      (congrArg (fun g : CategoryTheory.Sequence.index m.of.len ⟶
          CategoryTheory.Sequence.index m.of.len => degreeInclusion.map g) hf).trans
        (degreeInclusion.map_id (CategoryTheory.Sequence.index m.of.len))
    have hlabel : τ.as = σ.as := (Category.id_comp τ.as).symm.trans
      ((congrArg (fun g : card m.of.len ⟶ card m.of.len => g ≫ τ.as)
        hi.symm).trans hw)
    exact Discrete.eqToHom hlabel.symm
  map_preimage _ := by
    apply CostructuredArrow.hom_ext
    exact Discrete.hom_eq
  preimage_map _ := Discrete.hom_eq

/-- Every original finite-degree costructured arrow is represented by its full permutation label. -/
theorem fibreEssSurj (m : I) : (fibreFunctor m).EssSurj :=
  ⟨fun q => by
    obtain ⟨n, f, rfl⟩ := CostructuredArrow.mk_surjective q
    have hn : CategoryTheory.Sequence.degree n = m.of.len := by
      have h := Fintype.card_congr (smallFiniteBijection f)
      change Fintype.card (Fin (CategoryTheory.Sequence.degree n)) = Fintype.card (Fin m.of.len) at h
      simpa only [Fintype.card_fin] using h
    have he : n = CategoryTheory.Sequence.index m.of.len :=
      (CategoryTheory.Sequence.index_degree n).symm.trans
        (congrArg CategoryTheory.Sequence.index hn)
    subst n
    exact ⟨⟨f⟩, ⟨Iso.refl _⟩⟩⟩

/-- The coefficient fibre equivalence retains the entire original discrete-label functor. -/
theorem fibreIsEquivalence (m : I) : (fibreFunctor m).IsEquivalence where
  faithful := (fibreFullyFaithful m).faithful
  full := (fibreFullyFaithful m).full
  essSurj := fibreEssSurj m

/-- The actual coefficient fibre is equivalent to the full permutation-label set. -/
def fibreEquivalence (m : I) : Discrete (card m.of.len ⟶ m) ≌
    CostructuredArrow degreeInclusion m :=
  @Functor.asEquivalence _ _ _ _ (fibreFunctor m) (fibreIsEquivalence m)

/-- The entire forward equivalence is the original native coefficient fibre functor. -/
theorem fibreEquivalence_functor (m : I) : (fibreEquivalence m).functor = fibreFunctor m := rfl

/-- Along the actual full fibre every coefficient is the unchanged ordered level. -/
def fibreDiagramIso (X : CategoryTheory.Sequence PointedCGWH.{u, v}) (m : I) :
    fibreFunctor m ⋙ CostructuredArrow.proj degreeInclusion m ⋙ X.functor ≅
      Discrete.functor (fun _ : card m.of.len ⟶ m =>
        X.functor.obj (CategoryTheory.Sequence.index m.of.len)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro σ τ f
    change X.functor.map ((fibreFunctor m).map f).left ≫ (𝟙 _) = (𝟙 _) ≫ (𝟙 _)
    have hf : ((fibreFunctor m).map f).left = 𝟙 (CategoryTheory.Sequence.index m.of.len) :=
      Discrete.hom_eq
    have hmap : X.functor.map ((fibreFunctor m).map f).left =
        𝟙 (X.functor.obj (CategoryTheory.Sequence.index m.of.len)) :=
      (congrArg (fun g : CategoryTheory.Sequence.index m.of.len ⟶
          CategoryTheory.Sequence.index m.of.len => X.functor.map g) hf).trans
        (X.functor.map_id (CategoryTheory.Sequence.index m.of.len))
    exact congrArg (fun g => g ≫ (𝟙 (X.functor.obj (CategoryTheory.Sequence.index m.of.len)))) hmap)

/-- The original ordinary Kan extension is the actual freely based permutation smash. -/
def coefficientSourceIso (X : CategoryTheory.Sequence PointedCGWH.{u, v}) (m : I) :
    (degreeInclusion.leftKanExtension X.functor).obj m ≅
      discreteSmashObj.{u, v, 0} (card m.of.len ⟶ m)
        (X.functor.obj (CategoryTheory.Sequence.index m.of.len)) := by
  let D := CostructuredArrow.proj degreeInclusion m ⋙ X.functor
  let h := degreeInclusion.isPointwiseLeftKanExtensionLeftKanExtensionUnit X.functor m
  have hD : IsColimit ((colimit.cocone D).whisker (fibreFunctor m)) :=
    (colimit.isColimit D).whiskerEquivalence (fibreEquivalence m)
  let hS := discreteSmashCofanIsColimit.{u, v, 0} (card m.of.len ⟶ m)
    (X.functor.obj (CategoryTheory.Sequence.index m.of.len))
  exact h.isoColimit ≪≫ IsColimit.coconePointsIsoOfNatIso hD hS (fibreDiagramIso X m)

/-- The full native symmetrization retains the original coefficient-smash presentation. -/
def coefficientIso (X : CategoryTheory.Sequence PointedCGWH.{u, v}) (m : I) :
    (G.obj X).functor.obj m ≅ discreteSmashObj.{u, v, 0} (card m.of.len ⟶ m)
      (X.functor.obj (CategoryTheory.Sequence.index m.of.len)) := coefficientSourceIso X m

/-- The coefficient comparison sends every original Kan generator to its discrete smash inclusion. -/
@[reassoc]
theorem coefficientIso_coefficient (X : CategoryTheory.Sequence PointedCGWH.{u, v}) (m : I)
    (σ : card m.of.len ⟶ m) :
    coefficient X (CategoryTheory.Sequence.index m.of.len) m σ ≫ (coefficientIso X m).hom =
      discreteSmashIncl.{u, v, 0} (card m.of.len ⟶ m)
        (X.functor.obj (CategoryTheory.Sequence.index m.of.len)) σ := by
  let D := CostructuredArrow.proj degreeInclusion m ⋙ X.functor
  let h := degreeInclusion.isPointwiseLeftKanExtensionLeftKanExtensionUnit X.functor m
  let hD : IsColimit ((colimit.cocone D).whisker (fibreFunctor m)) :=
    (colimit.isColimit D).whiskerEquivalence (fibreEquivalence m)
  let hS := discreteSmashCofanIsColimit.{u, v, 0} (card m.of.len ⟶ m)
    (X.functor.obj (CategoryTheory.Sequence.index m.of.len))
  let k := IsColimit.coconePointsIsoOfNatIso hD hS (fibreDiagramIso X m)
  have hKan : coefficientSource X (CategoryTheory.Sequence.index m.of.len) m σ ≫
      h.isoColimit.hom = colimit.ι D ((fibreFunctor m).obj (Discrete.mk σ)) :=
    (Category.assoc _ _ _).trans (h.ι_isoColimit_hom ((fibreFunctor m).obj (Discrete.mk σ)))
  have hSmash :=
    IsColimit.comp_coconePointsIsoOfNatIso_hom hD hS (fibreDiagramIso X m) (Discrete.mk σ)
  change colimit.ι D ((fibreFunctor m).obj (Discrete.mk σ)) ≫ k.hom =
    (𝟙 (X.functor.obj (CategoryTheory.Sequence.index m.of.len))) ≫
      discreteSmashIncl.{u, v, 0} (card m.of.len ⟶ m)
        (X.functor.obj (CategoryTheory.Sequence.index m.of.len)) σ at hSmash
  change coefficientSource X (CategoryTheory.Sequence.index m.of.len) m σ ≫
    (h.isoColimit.hom ≫ k.hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ k.hom) hKan).trans (hSmash.trans (Category.id_comp _)))

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
