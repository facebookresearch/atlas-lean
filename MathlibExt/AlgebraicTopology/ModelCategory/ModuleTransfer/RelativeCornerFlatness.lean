/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.NaturalTransformationCorner.ColimitClosure
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorFreePushoutProduct
public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.GeneratingCornerFlatness
public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.FreeCellFlatness
public import MathlibExt.CategoryTheory.MorphismProperty.CoproductClosure
public import MathlibExt.CategoryTheory.SmallObject.Closure

/-!
# Relative flatness from generating pushout products

In a closed symmetric model category, a generator condition requires the
pushout product of a weak equivalence with an `I`-arrow to be weak. Under
h-monoidality, filtered-colimit stability of weak equivalences and a
small-object argument for free-`I` at a regular cardinal whose left class
is the module cofibrations, every cofibrant left module is relatively flat.
Closure of the natural-transformation corner property under transfinite
composition and retracts transfers the condition from generators to
cofibrations. For a weak monoid morphism and module model structures detected
by their forgetful functors, it yields a Quillen equivalence between extension
and restriction of scalars.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.RelativeCornerFlatness

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  {A : C} [MonObj A] [HasColimitsOfSize.{0, 0} C]

/-- The original tensor natural transformation uses the same two right coefficients. -/
abbrev comparison {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :=
  CategoryTheory.Mod.RightLeftTensor.leftTensorNatural f

omit [MonoidalClosed C] in
theorem relativeMap_inl {N N' : RightModuleFree.Carrier A} (f : N ⟶ N')
    {i j : Arrow (Mod C A)} (s : i ⟶ j) :
    pushout.inl ((comparison f).app i.left) ((CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N).map i.hom) ≫
        (((CategoryTheory.Mod.RightLeftTensor.relativePushoutProduct (A := A)).obj (Arrow.mk f)).map s).left =
      (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N').map s.left ≫
        pushout.inl ((comparison f).app j.left)
          ((CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N).map j.hom) := by
  exact (Functor.PushoutObjObj.ofHasPushout
    (CategoryTheory.Mod.RightLeftTensor.tensorCurried (A := A)) f i.hom).isPushout.inl_desc _ _ _

omit [MonoidalClosed C] in
theorem relativeMap_inr {N N' : RightModuleFree.Carrier A} (f : N ⟶ N')
    {i j : Arrow (Mod C A)} (s : i ⟶ j) :
    pushout.inr ((comparison f).app i.left) ((CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N).map i.hom) ≫
        (((CategoryTheory.Mod.RightLeftTensor.relativePushoutProduct (A := A)).obj (Arrow.mk f)).map s).left =
      (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N).map s.right ≫
        pushout.inr ((comparison f).app j.left)
          ((CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N).map j.hom) := by
  exact (Functor.PushoutObjObj.ofHasPushout
    (CategoryTheory.Mod.RightLeftTensor.tensorCurried (A := A)) f i.hom).isPushout.inr_desc _ _ _

omit [MonoidalClosed C] in
/-- The natural-transformation corner functor is the existing literal relative Leibniz functor. -/
theorem relativeCornerFunctor_eq {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :
    HomotopicalAlgebra.NaturalTransformationCorner.functor (comparison f) =
      (CategoryTheory.Mod.RightLeftTensor.relativePushoutProduct (A := A)).obj (Arrow.mk f) := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    rfl
  case h_map =>
    intro i j s
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply Arrow.hom_ext
    · change HomotopicalAlgebra.NaturalTransformationCorner.domainMap (comparison f) s =
        (((CategoryTheory.Mod.RightLeftTensor.relativePushoutProduct (A := A)).obj (Arrow.mk f)).map s).left
      apply pushout.hom_ext
      · rw [HomotopicalAlgebra.NaturalTransformationCorner.domainMap_inl (comparison f) s, relativeMap_inl f s]
      · rw [HomotopicalAlgebra.NaturalTransformationCorner.domainMap_inr (comparison f) s, relativeMap_inr f s]
    · rfl

/-- The actual parametrized adjunction earns every original source-universe colimit preservation. -/
theorem relativeCornerFunctor_preservesColimits [HasPullbacks (Mod C A)]
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :
    PreservesColimitsOfSize.{w, w} (HomotopicalAlgebra.NaturalTransformationCorner.functor (comparison f)) := by
  rw [relativeCornerFunctor_eq f]
  exact CategoryTheory.Mod.RightLeftTensor.relativePushoutProduct_preservesColimits (Arrow.mk f)

section InitialCorner

variable {D : Type uD} [Category.{vD} D] [HasInitial D]
  {P Q : D ⥤ C} (α : P ⟶ Q)
  [PreservesColimitsOfSize.{0, 0} P] [PreservesColimitsOfSize.{0, 0} Q]

/-- The entire original initial-source corner is the actual tensor comparison arrow. -/
def initialCornerArrowIso (M : D) :
    Arrow.mk (HomotopicalAlgebra.NaturalTransformationCorner.corner α (Arrow.mk (initial.to M))) ≅
      Arrow.mk (α.app M) := by
  let : IsIso (α.app (⊥_ D)) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj P) (initialIsInitial.isInitialObj Q) _
  let r := pushout.inr (α.app (⊥_ D)) (P.map (initial.to M))
  let : IsIso r :=
    (IsPushout.of_hasPushout (α.app (⊥_ D)) (P.map (initial.to M))).isIso_inr_of_isIso
  refine Arrow.isoMk (asIso r).symm (Iso.refl _) ?_
  change (asIso r).inv ≫ α.app M =
    HomotopicalAlgebra.NaturalTransformationCorner.corner α (Arrow.mk (initial.to M)) ≫ 𝟙 _
  rw [Category.comp_id]
  exact (Iso.inv_comp_eq (asIso r)).mpr
    (HomotopicalAlgebra.NaturalTransformationCorner.inr_corner_mk α (initial.to M)).symm

end InitialCorner

section Generators

variable [ModelCategory C] [SymmetricCategory C]

/-- The sharp base generator criterion keeps both arbitrary original weak-map endpoints. -/
def GeneratingPushoutProductFlatness (I : MorphismProperty C) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), weakEquivalences C f →
    ∀ {K L : C} (i : K ⟶ L), I i → weakEquivalences C (Arrow.mk f □ Arrow.mk i).hom

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- The original two-endpoint coefficient certificate and h-monoidality give the sharp base corner criterion. -/
theorem generatingFlatness_of_original_coefficients (I : MorphismProperty C)
    (hI : I ≤ cofibrations C) (hMono : HMonoidality C)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness I) :
    GeneratingPushoutProductFlatness I := by
  intro X Y f hf K L i hi
  exact HomotopicalAlgebra.ModuleTransfer.GeneratingCornerFlatness.generatingPushoutProduct_weak
    I hI hMono hFlat f hf i hi

omit [MonoidalClosed C] in
/-- Every original free-I arrow has its whole weak relative corner and both actual h-cofibration images. -/
theorem original_freeI_le_guarded (I : MorphismProperty C)
    (hI : I ≤ cofibrations C) (hMono : HMonoidality C)
    (hFlat : GeneratingPushoutProductFlatness I)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (hf : weakEquivalences C f.hom) :
    HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I ≤
      HomotopicalAlgebra.NaturalTransformationCorner.guardedProperty (comparison f) := by
  have hTensor : ∀ (T : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L),
      I i → hCofibrations C (T.X ◁ i) :=
    fun T {K L} i hi => HomotopicalAlgebra.ModuleTransfer.GeneratingCornerFlatness.leftTensor_hCof hMono i (hI i hi) T.X
  have hP := HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI_generators_h I (hCofibrations C) hTensor N
  have hQ := HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI_generators_h I (hCofibrations C) hTensor N'
  intro K L i hi
  refine ⟨?_, hP i hi, hQ i hi⟩
  cases hi with
  | @map X Y g h =>
    have e := CategoryTheory.Mod.RightLeftTensor.relativeFreePushoutProductIso f g
    rw [← relativeCornerFunctor_eq f] at e
    exact ((weakEquivalences C).arrow_mk_iso_iff e).mpr (hFlat f.hom hf g h)

end Generators

section RelativeCells

variable [ModelCategory C] [SymmetricCategory C]
  [HasColimitsOfSize.{w, w} C] [ModelCategory (Mod C A)]
  [(weakEquivalences C).IsStableUnderFilteredColimits.{w, w}]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

local instance cellModuleColimits : HasColimitsOfSize.{w, w} (Mod C A) := Mod.hasColimits.{w} A

/-- Every original relative free-I history has its whole weak corner, with arbitrary original endpoints. -/
theorem corner_weak_of_original_relativeCells (I : MorphismProperty C)
    (hI : I ≤ cofibrations C) (hMono : HMonoidality C)
    (hFlat : GeneratingPushoutProductFlatness I)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (hf : weakEquivalences C f.hom)
    {X Y : Mod C A} {g : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun (_ : J) =>
      (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I).homFamily) g) :
    weakEquivalences C (HomotopicalAlgebra.NaturalTransformationCorner.corner (comparison f) (Arrow.mk g)) := by
  let α := comparison f
  let K := HomotopicalAlgebra.NaturalTransformationCorner.guardedProperty α
  let : IsLeftProper C := hMono.isLeftProper
  let : (hCofibrations C).IsMultiplicative :=
    HomotopicalAlgebra.HCofibrationFilteredColimits.hCof_isMultiplicative hMono
  let : PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N) :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N
  let : PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N') :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N'
  let : PreservesColimitsOfSize.{0, 0} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N) :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N
  let : PreservesColimitsOfSize.{0, 0} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N') :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N'
  let : PreservesColimitsOfSize.{w, w} (HomotopicalAlgebra.NaturalTransformationCorner.functor α) :=
    relativeCornerFunctor_preservesColimits f
  let : K.RespectsIso := HomotopicalAlgebra.NaturalTransformationCorner.guardedProperty_respectsIso α
  let : K.IsStableUnderCobaseChange :=
    HomotopicalAlgebra.NaturalTransformationCorner.guardedProperty_isStableUnderCobaseChange α
  let : K.IsStableUnderTransfiniteComposition.{w} :=
    HomotopicalAlgebra.NaturalTransformationCorner.guardedProperty_isStableUnderTransfiniteComposition α
  let : K.IsStableUnderCoproducts.{w} :=
    MorphismProperty.isStableUnderCoproducts_of_cobase_transfinite K
  let : PreservesWellOrderContinuousOfShape J (𝟭 (Mod C A)) :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  have hGen : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I ≤ K :=
    original_freeI_le_guarded I hI hMono hFlat f hf
  have hCell : K g := by
    have h := HomotopicalAlgebra.RelativeCellComplex.map_mem_of_le
      (𝟭 (Mod C A)) (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI I) K hGen c
    simpa only [Functor.id_map] using h
  exact hCell.1

end RelativeCells

section OriginalCells

variable [ModelCategory C] [SymmetricCategory C]
  [HasColimitsOfSize.{w, w} C] [ModelCategory (Mod C A)]
  [(weakEquivalences C).IsStableUnderFilteredColimits.{w, w}]

local instance originalModuleColimits : HasColimitsOfSize.{w, w} (Mod C A) := Mod.hasColimits.{w} A

variable (I : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [(HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I).IsCardinalForSmallObjectArgument κ]

include κ in
/-- The entire weak saturation of the original free-I class has weak relative corners for all source cofibrations. -/
theorem corner_weak_of_original_cofibration
    (hCof : cofibrations (Mod C A) = (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I).rlp.llp)
    (hI : I ≤ cofibrations C) (hMono : HMonoidality C)
    (hFlat : GeneratingPushoutProductFlatness I)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (hf : weakEquivalences C f.hom)
    {X Y : Mod C A} (g : X ⟶ Y) (hg : cofibrations (Mod C A) g) :
    weakEquivalences C (HomotopicalAlgebra.NaturalTransformationCorner.corner (comparison f) (Arrow.mk g)) := by
  have hLeft : (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I).rlp.llp g := by
    rw [← hCof]
    exact hg
  let : HasLiftingProperty g
      (CategoryTheory.SmallObject.πObj (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI I) κ g) :=
    hLeft _ (CategoryTheory.SmallObject.rlp_πObj (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI I) κ g)
  let r : RetractArrow g
      (CategoryTheory.SmallObject.ιObj (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI I) κ g) :=
    RetractArrow.ofLeftLiftingProperty
      (CategoryTheory.SmallObject.ιObj_πObj (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI I) κ g)
  have hCell : weakEquivalences C (HomotopicalAlgebra.NaturalTransformationCorner.corner (comparison f)
      (Arrow.mk (CategoryTheory.SmallObject.ιObj (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI I) κ g))) :=
    corner_weak_of_original_relativeCells I hI hMono hFlat f hf
      (CategoryTheory.SmallObject.relativeCellComplexιObj
        (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI I) κ g)
  exact HomotopicalAlgebra.NaturalTransformationCorner.corner_weak_of_sourceRetract (comparison f) r hCell

/-- The complete original free-I history has its weak relative corner, with the unchanged caller cardinal. -/
theorem originalCell_corner_weak
    (hI : I ≤ cofibrations C) (hMono : HMonoidality C)
    (hFlat : GeneratingPushoutProductFlatness I)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (hf : weakEquivalences C f.hom)
    (M : Mod C A) :
    weakEquivalences C (HomotopicalAlgebra.NaturalTransformationCorner.corner (comparison f)
      (Arrow.mk (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.initialCellInclusion I κ M))) := by
  let α := comparison f
  let K := HomotopicalAlgebra.NaturalTransformationCorner.guardedProperty α
  let : IsLeftProper C := hMono.isLeftProper
  let : (hCofibrations C).IsMultiplicative :=
    HomotopicalAlgebra.HCofibrationFilteredColimits.hCof_isMultiplicative hMono
  let : PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N) :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N
  let : PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N') :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N'
  let : PreservesColimitsOfSize.{0, 0} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N) :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N
  let : PreservesColimitsOfSize.{0, 0} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N') :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N'
  let : PreservesColimitsOfSize.{w, w} (HomotopicalAlgebra.NaturalTransformationCorner.functor α) :=
    relativeCornerFunctor_preservesColimits f
  let : K.RespectsIso := HomotopicalAlgebra.NaturalTransformationCorner.guardedProperty_respectsIso α
  let : K.IsStableUnderCobaseChange :=
    HomotopicalAlgebra.NaturalTransformationCorner.guardedProperty_isStableUnderCobaseChange α
  let : K.IsStableUnderTransfiniteComposition.{w} :=
    HomotopicalAlgebra.NaturalTransformationCorner.guardedProperty_isStableUnderTransfiniteComposition α
  let : K.IsStableUnderCoproducts.{w} :=
    MorphismProperty.isStableUnderCoproducts_of_cobase_transfinite K
  have hGen : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I ≤ K :=
    original_freeI_le_guarded I hI hMono hFlat f hf
  have hCell : K (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.initialCellInclusion I κ M) := by
    let : PreservesWellOrderContinuousOfShape κ.ord.ToType (𝟭 (Mod C A)) :=
      { preservesColimitsOfShape := fun _ _ => by infer_instance }
    have h := HomotopicalAlgebra.RelativeCellComplex.map_mem_of_le
      (𝟭 (Mod C A)) (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI I) K hGen
      (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.initialCellComplex I κ M)
    simpa only [Functor.id_map] using h
  exact hCell.1

/-- The original initial-source corner comparison identifies the full cell module tensor map. -/
theorem originalCell_comparison_weak
    (hI : I ≤ cofibrations C) (hMono : HMonoidality C)
    (hFlat : GeneratingPushoutProductFlatness I)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (hf : weakEquivalences C f.hom)
    (M : Mod C A) :
    weakEquivalences C ((comparison f).app
      (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.initialCellObject I κ M)) := by
  let : PreservesColimitsOfSize.{0, 0} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N) :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N
  let : PreservesColimitsOfSize.{0, 0} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N') :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N'
  have h := originalCell_corner_weak I κ hI hMono hFlat f hf M
  have he : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.initialCellInclusion I κ M =
      initial.to (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.initialCellObject I κ M) :=
    initialIsInitial.hom_ext _ _
  rw [he] at h
  exact ((weakEquivalences C).arrow_mk_iso_iff
    (initialCornerArrowIso (comparison f)
      (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.initialCellObject I κ M))).mp
      h

include κ in
/-- Every cofibrant original left module is relatively flat through its exact original free-I source retract. -/
theorem relativeFlat_of_original_freeI_pushoutProducts
    (hCof : cofibrations (Mod C A) = (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I).rlp.llp)
    (hI : I ≤ cofibrations C) (hMono : HMonoidality C)
    (hFlat : GeneratingPushoutProductFlatness I)
    (M : Mod C A) [IsCofibrant M] : HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M := by
  intro N N' f hf
  change weakEquivalences C ((comparison f).app M)
  exact HomotopicalAlgebra.ModuleTransfer.CellComparison.comparison_of_retract (weakEquivalences C) (comparison f)
    (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.initialSourceRetract I κ hCof M)
    (originalCell_comparison_weak I κ hI hMono hFlat f hf M)

include κ in
/-- The conventional coefficient/h-monoidal/weak-colimit source data earn full original module relative flatness. -/
theorem relativeFlat_of_original_coefficients
    (hCof : cofibrations (Mod C A) = (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I).rlp.llp)
    (hI : I ≤ cofibrations C) (hMono : HMonoidality C)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness I)
    (M : Mod C A) [IsCofibrant M] : HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M :=
  relativeFlat_of_original_freeI_pushoutProducts I κ hCof hI hMono
    (generatingFlatness_of_original_coefficients I hI hMono hFlat) M

end OriginalCells

section Scalar

variable [ModelCategory C] [SymmetricCategory C]
  [HasColimitsOfSize.{w, w} C] [ModelCategory (Mod C A)]
  [(weakEquivalences C).IsStableUnderFilteredColimits.{w, w}]
  {B : C} [MonObj B] [ModelCategory (Mod C B)]
  [PreservesColimitsOfSize.{0, 0} (tensorLeft B)]
  (I : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [(HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I).IsCardinalForSmallObjectArgument κ]

include κ in
/-- The whole conventional free-I producer and original actual scalar unit give the full Quillen equivalence. -/
theorem isQuillenEquivalence_of_original_corner_saturation
    (hWA : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hWB : weakEquivalences (Mod C B) = (weakEquivalences C).inverseImage (Mod.forget (D := C) B))
    (hFA : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (hFB : fibrations (Mod C B) = (fibrations C).inverseImage (Mod.forget (D := C) B))
    (hCof : cofibrations (Mod C A) = (HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.freeI (A := A) I).rlp.llp)
    (hI : I ≤ cofibrations C) (hMono : HMonoidality C)
    (hFlat : HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness.GeneratingCoefficientFlatness I)
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p) :
    (Mod.ExtensionOfScalars.adjunction p).IsQuillenEquivalence := by
  apply HomotopicalAlgebra.ModuleTransfer.WeakScalar.isQuillenEquivalenceOfRelativeFlatness hWA hWB hFA hFB p hp
  intro M hM
  let : IsCofibrant M := hM
  intro N N' f hf
  exact relativeFlat_of_original_coefficients I κ hCof hI hMono hFlat M f hf

end Scalar
end HomotopicalAlgebra.ModuleTransfer.RelativeCornerFlatness
