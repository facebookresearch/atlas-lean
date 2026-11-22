/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.RightLeftTensorFree
public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.WeakScalar
public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.CellComparison
public import MathlibExt.CategoryTheory.SmallObject.Image

/-!
# Relative flatness from free module cells

The small-object argument for `freeI I` at a regular cardinal constructs a
cell module and a retract onto each cofibrant left module when its left
class equals the module cofibrations. Generating coefficient flatness,
the stated coproduct, pushout and ordinal-colimit comparison closures,
and the tensor-class conditions imply relative flatness of these modules.
Right coefficient endpoints are arbitrary. For a weak monoid morphism,
this yields a scalar Quillen equivalence when weak equivalences and
fibrations in both module models are created by their forgetful functors.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty CategoryTheory.SmallObject HomotopicalAlgebra
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [ModelCategory C]

/-- Flatness is tested on the two actual coefficient objects of each original generator. -/
def GeneratingCoefficientFlatness (I : MorphismProperty C) : Prop :=
  ∀ {Y Z : C} (f : Y ⟶ Z), weakEquivalences C f →
    ∀ {K L : C} (i : K ⟶ L), I i →
      weakEquivalences C (f ▷ K) ∧ weakEquivalences C (f ▷ L)

variable {A : C} [MonObj A] [HasColimitsOfSize.{0, 0} C]

/-- The generator class is the literal image of the original I under actual Mod.free. -/
abbrev freeI (I : MorphismProperty C) : MorphismProperty (Mod C A) := I.strictMap (Mod.free A)

/-- The whole right coefficient map determines the original comparison on all left modules. -/
abbrev comparison {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') :=
  CategoryTheory.Mod.RightLeftTensor.leftTensorNatural f

omit [ModelCategory C] in
theorem comparison_original {N N' : RightModuleFree.Carrier A}
    (f : N ⟶ N') (M : Mod C A) :
    (comparison f).app M = (CategoryTheory.Mod.RightLeftTensor.rightTensorFunctor M).map f := rfl

/-- Original coefficient flatness supplies both free-I endpoint comparisons via the entire free Arrow iso. -/
theorem freeI_comparison_endpoints (I : MorphismProperty C)
    (hFlat : GeneratingCoefficientFlatness I)
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (hf : weakEquivalences C f.hom) :
    ∀ {K L : Mod C A} (i : K ⟶ L), freeI (A := A) I i →
      weakEquivalences C ((comparison f).app K) ∧ weakEquivalences C ((comparison f).app L) := by
  intro K L i hi
  cases hi with
  | map h =>
    obtain ⟨hK, hL⟩ := hFlat f.hom hf _ h
    constructor
    · exact ((weakEquivalences C).arrow_mk_iso_iff
        (CategoryTheory.Mod.RightLeftTensor.freeCoefficientArrowIso f _)).mpr hK
    · exact ((weakEquivalences C).arrow_mk_iso_iff
        (CategoryTheory.Mod.RightLeftTensor.freeCoefficientArrowIso f _)).mpr hL

omit [ModelCategory C] in
/-- A specified actual tensor-generator condition supplies the free module generator images. -/
theorem freeI_generators_h (I H : MorphismProperty C) [H.RespectsIso]
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), I i → H (N.X ◁ i))
    (N : RightModuleFree.Carrier A) :
    freeI (A := A) I ≤ H.inverseImage (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N) := by
  intro K L i hi
  cases hi with
  | map h =>
    exact (H.arrow_mk_iso_iff (CategoryTheory.Mod.RightLeftTensor.freeGeneratorArrowIso N _)).mpr (hTensor N _ h)

section OriginalCells

variable [MonoidalClosed C] [HasColimitsOfSize.{w, w} C] [ModelCategory (Mod C A)]

local instance module_colimits : HasColimitsOfSize.{w, w} (Mod C A) := Mod.hasColimits.{w} A

variable (I : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [(freeI (A := A) I).IsCardinalForSmallObjectArgument κ]

/-- The caller's original free-I factor object, at exactly the supplied cardinal and original bottom. -/
def initialCellObject (M : Mod C A) : Mod C A :=
  SmallObject.obj (freeI I) κ (initial.to M)

/-- The inclusion of the actual original free-I small-object stage. -/
def initialCellInclusion (M : Mod C A) : (⊥_ (Mod C A)) ⟶ initialCellObject I κ M :=
  SmallObject.ιObj (freeI I) κ (initial.to M)

/-- The original right map from the free-I stage to its chosen endpoint. -/
def initialCellProjection (M : Mod C A) : initialCellObject I κ M ⟶ M :=
  SmallObject.πObj (freeI I) κ (initial.to M)

omit [ModelCategory C] [HasColimitsOfSize.{0, 0} C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C] in
/-- Both factors retain the unchanged original initial arrow. -/
theorem initialCell_factor (M : Mod C A) :
    initialCellInclusion I κ M ≫ initialCellProjection I κ M = initial.to M :=
  SmallObject.ιObj_πObj (freeI I) κ (initial.to M)

/-- Every label, source/target cofan, attaching map and limit cocone is the original free-I SOA history. -/
def initialCellComplex (M : Mod C A) :
    RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) => (freeI (A := A) I).homFamily)
      (initialCellInclusion I κ M) :=
  SmallObject.relativeCellComplexιObj (freeI I) κ (initial.to M)

omit [ModelCategory C] [HasColimitsOfSize.{0, 0} C] in
/-- The cofibrant original module lifts against the actual free-I right factor. -/
def initialArrowRetract
    (hCof : cofibrations (Mod C A) = (freeI (A := A) I).rlp.llp)
    (M : Mod C A) [IsCofibrant M] :
    RetractArrow (initial.to M) (initialCellInclusion I κ M) := by
  have hLeft : (freeI (A := A) I).rlp.llp (initial.to M) := by
    rw [← hCof]
    exact mem_cofibrations (initial.to M)
  let : HasLiftingProperty (initial.to M) (initialCellProjection I κ M) :=
    hLeft _ (SmallObject.rlp_πObj (freeI I) κ (initial.to M))
  exact RetractArrow.ofLeftLiftingProperty (initialCell_factor I κ M)

omit [ModelCategory C] [HasColimitsOfSize.{0, 0} C] in
/-- The entire lifting-derived source split, with the original projection, is the module retract. -/
def initialSourceRetract
    (hCof : cofibrations (Mod C A) = (freeI (A := A) I).rlp.llp)
    (M : Mod C A) [IsCofibrant M] : Retract M (initialCellObject I κ M) where
  i := (initialArrowRetract I κ hCof M).i.right
  r := (initialArrowRetract I κ hCof M).r.right
  retract := by
    exact congrArg (fun g => g.right) (initialArrowRetract I κ hCof M).retract

omit [ModelCategory C] [HasColimitsOfSize.{0, 0} C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C] in
theorem initialSourceRetract_projection
    (hCof : cofibrations (Mod C A) = (freeI (A := A) I).rlp.llp)
    (M : Mod C A) [IsCofibrant M] :
    (initialSourceRetract I κ hCof M).r = initialCellProjection I κ M := rfl

omit [HasColimitsOfSize.{w, w} C] in
/-- The actual original cell module comparison is weak, including every successor and limit. -/
theorem initialCell_comparison_weak
    (H : MorphismProperty C) [H.RespectsIso]
    (cl : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{u, v, w, w} (weakEquivalences C) H)
    (hFlat : GeneratingCoefficientFlatness I)
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), I i → H (N.X ◁ i))
    {N N' : RightModuleFree.Carrier A} (f : N ⟶ N') (hf : weakEquivalences C f.hom)
    (M : Mod C A) : weakEquivalences C ((comparison f).app (initialCellObject I κ M)) := by
  let : PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N) :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N
  let : PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N') :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N'
  let : PreservesColimitsOfSize.{0, 0} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N) :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N
  let : PreservesColimitsOfSize.{0, 0} (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N') :=
    CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor_preservesColimits N'
  have hInitial : weakEquivalences C ((comparison f).app (⊥_ (Mod C A))) := by
    let : IsIso ((comparison f).app (⊥_ (Mod C A))) :=
      isIso_of_isInitial
        (initialIsInitial.isInitialObj (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N))
        (initialIsInitial.isInitialObj (CategoryTheory.Mod.RightLeftTensor.leftTensorFunctor N')) _
    exact (weakEquivalences C).of_isIso _
  exact HomotopicalAlgebra.ModuleTransfer.CellComparison.comparison_of_relativeCells (weakEquivalences C) H cl (freeI I)
    (comparison f) (freeI_generators_h I H hTensor N) (freeI_generators_h I H hTensor N')
    (freeI_comparison_endpoints I hFlat f hf) (initialCellComplex I κ M) hInitial

include κ in
omit [HasColimitsOfSize.{w, w} C] in
/-- Every cofibrant original left module is relatively flat, with arbitrary right coefficient endpoints. -/
theorem relativeFlat_of_original_freeICells
    (hCof : cofibrations (Mod C A) = (freeI (A := A) I).rlp.llp)
    (H : MorphismProperty C) [H.RespectsIso]
    (cl : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{u, v, w, w} (weakEquivalences C) H)
    (hFlat : GeneratingCoefficientFlatness I)
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), I i → H (N.X ◁ i))
    (M : Mod C A) [IsCofibrant M] : HomotopicalAlgebra.ModuleTransfer.WeakScalar.RelativeFlat M := by
  intro N N' f hf
  change weakEquivalences C ((comparison f).app M)
  exact HomotopicalAlgebra.ModuleTransfer.CellComparison.comparison_of_retract (weakEquivalences C) (comparison f)
    (initialSourceRetract I κ hCof M) (initialCell_comparison_weak I κ H cl hFlat hTensor f hf M)

end OriginalCells

section Scalar

variable [MonoidalClosed C] [HasColimitsOfSize.{w, w} C]
  {B : C} [MonObj B] [ModelCategory (Mod C A)] [ModelCategory (Mod C B)]
  (I : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [(freeI (A := A) I).IsCardinalForSmallObjectArgument κ]

include κ in
omit [HasColimitsOfSize.{w, w} C] in
/-- The genuine cell producer, actual tensor-unit Arrow and created classes give full weak scalar invariance. -/
theorem isQuillenEquivalence_of_original_freeICells
    (hWA : weakEquivalences (Mod C A) = (weakEquivalences C).inverseImage (Mod.forget (D := C) A))
    (hWB : weakEquivalences (Mod C B) = (weakEquivalences C).inverseImage (Mod.forget (D := C) B))
    (hFA : fibrations (Mod C A) = (fibrations C).inverseImage (Mod.forget (D := C) A))
    (hFB : fibrations (Mod C B) = (fibrations C).inverseImage (Mod.forget (D := C) B))
    (hCof : cofibrations (Mod C A) = (freeI (A := A) I).rlp.llp)
    (H : MorphismProperty C) [H.RespectsIso]
    (cl : HomotopicalAlgebra.ModuleTransfer.CellComparison.Closure.{u, v, w, w} (weakEquivalences C) H)
    (hFlat : GeneratingCoefficientFlatness I)
    (hTensor : ∀ (N : RightModuleFree.Carrier A) {K L : C} (i : K ⟶ L), I i → H (N.X ◁ i))
    (p : A ⟶ B) [IsMonHom p] (hp : weakEquivalences C p) :
    (Mod.ExtensionOfScalars.adjunction p).IsQuillenEquivalence := by
  apply HomotopicalAlgebra.ModuleTransfer.WeakScalar.isQuillenEquivalenceOfRelativeFlatness hWA hWB hFA hFB p hp
  intro M hM
  let : IsCofibrant M := hM
  intro N N' f hf
  exact relativeFlat_of_original_freeICells I κ hCof H cl hFlat hTensor M f hf

end Scalar
end HomotopicalAlgebra.ModuleTransfer.FreeCellFlatness
