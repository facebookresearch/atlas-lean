/-
Copyright (c) 2026 @toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.NativeRelativeCellColimits
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Original native small-object trees and cofibration retracts

The tree is constructed from `SmallObject.relativeCellComplexιObj` for the
same original family and cardinal. Its endpoint is the same native middle
object, and its root arrow is the same native left factor. Lifting against
the same native right factor gives an identity-on-source Arrow retract for
every original generated left map. Actual base cofibrant generation supplies
this membership for every original base cofibration.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.SmallObject.NativeSmallObjectPresentation

open CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  (I : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] [I.IsCardinalForSmallObjectArgument κ]

/-- The original native SOA family, retaining every original whole Arrow value. -/
abbrev generatorArrows : I.toSet → Arrow C := Subtype.val

/-- The original native occurrence order, instantiated explicitly for its original homFamily. -/
instance nativeCellsPartialOrder {X Y : C} (f : X ⟶ Y) :
    PartialOrder (SmallObject.relativeCellComplexιObj I κ f).Cells :=
  NativeRelativeCells.occurrencePartialOrder (s := generatorArrows I)
    (SmallObject.relativeCellComplexιObj I κ f)

/-- The complete cell tree of the ORIGINAL native left factor at the original cardinal. -/
def nativeTree {X Y : C} (f : X ⟶ Y) :
    CellTree (generatorArrows I) X
      (P := (SmallObject.relativeCellComplexιObj I κ f).Cells) := by
  letI : HasPushouts C := SmallObject.hasPushouts I κ
  exact NativeRelativeCells.tree (SmallObject.relativeCellComplexιObj I κ f)

@[simp]
theorem nativeTree_hom {X Y : C} (f : X ⟶ Y) :
    (nativeTree I κ f).hom = SmallObject.ιObj I κ f := rfl

@[simp]
theorem nativeTree_endpoint {X Y : C} (f : X ⟶ Y) :
    (nativeTree I κ f).endpointObj = Under.mk (SmallObject.ιObj I κ f) := rfl

/-- Every actual native occurrence retains its original native family label. -/
@[simp]
theorem nativeTree_label {X Y : C} (f : X ⟶ Y)
    (a : (SmallObject.relativeCellComplexιObj I κ f).Cells) :
    (nativeTree I κ f).label a = a.i := rfl

/-- Every native occurrence's whole original cell arrow belongs to the original family. -/
theorem nativeTree_cell_mem {X Y : C} (f : X ⟶ Y)
    (a : (SmallObject.relativeCellComplexιObj I κ f).Cells) :
    I ((generatorArrows I) ((nativeTree I κ f).label a)).hom := a.i.2

/-- The original endpoint cell inclusion is exactly the original native inclusion function. -/
@[reassoc]
theorem nativeTree_cell_inclusion {X Y : C} (f : X ⟶ Y)
    (a : (SmallObject.relativeCellComplexιObj I κ f).Cells) :
    (nativeTree I κ f).cell a ≫ ((nativeTree I κ f).inclusion a).right = a.ι := by
  let : HasPushouts C := SmallObject.hasPushouts I κ
  exact NativeRelativeCells.vertexCell_incl (SmallObject.relativeCellComplexιObj I κ f) a

/-- The whole original left-factor presentation fixes its actual source and endpoint. -/
def nativePresentation {X Y : C} (f : X ⟶ Y) :
    CellTree.Presentation (s := generatorArrows I)
      (P := (SmallObject.relativeCellComplexιObj I κ f).Cells)
      (SmallObject.ιObj I κ f) where
  tree := nativeTree I κ f
  endpointIso := Iso.refl _

/-- The original square used to make a retract of this SAME native cellular factor. -/
abbrev retractSquare {X Y : C} (f : X ⟶ Y) :
    CommSq (SmallObject.ιObj I κ f) f (SmallObject.πObj I κ f) (𝟙 Y) :=
  ⟨by rw [Category.comp_id, SmallObject.ιObj_πObj]⟩

/-- The canonical Arrow retract fixes the original source on both maps. -/
def arrowRetract {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    RetractArrow f (nativeTree I κ f).hom := by
  letI : HasLiftingProperty f (SmallObject.πObj I κ f) := hf _ (SmallObject.rlp_πObj I κ f)
  exact RetractArrow.ofLeftLiftingProperty
    (f := f) (i := SmallObject.ιObj I κ f) (p := SmallObject.πObj I κ f)
    (SmallObject.ιObj_πObj I κ f)

/-- The lift is the target component of the canonical original Arrow retract. -/
def retractLift {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) : Y ⟶ SmallObject.obj I κ f :=
  (arrowRetract I κ f hf).i.right

@[reassoc]
theorem retractLift_left {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    f ≫ retractLift I κ f hf = (nativeTree I κ f).hom := by
  change f ≫ retractLift I κ f hf = SmallObject.ιObj I κ f
  have h : (𝟙 X) ≫ SmallObject.ιObj I κ f = f ≫ retractLift I κ f hf :=
    (arrowRetract I κ f hf).i.w
  exact h.symm.trans (Category.id_comp (SmallObject.ιObj I κ f))

@[reassoc]
theorem retractLift_right {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    retractLift I κ f hf ≫ SmallObject.πObj I κ f = 𝟙 Y :=
  (arrowRetract I κ f hf).retract_right

/-- The whole original generated-left arrow is a retract under its arbitrary original root. -/
def underRetract {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    Retract (Under.mk f) (nativeTree I κ f).endpointObj where
  i := Under.homMk (retractLift I κ f hf) (retractLift_left I κ f hf)
  r := Under.homMk (SmallObject.πObj I κ f) (SmallObject.ιObj_πObj I κ f)
  retract := by
    apply Under.UnderMorphism.ext
    exact retractLift_right I κ f hf

/-- The original endpoint idempotent, produced from the actual original retract maps. -/
abbrev endpointIdempotent {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    (nativeTree I κ f).endpointObj ⟶ (nativeTree I κ f).endpointObj :=
  (underRetract I κ f hf).r ≫ (underRetract I κ f hf).i

/-- Its idempotent equation uses the actual original split, with no supplied desired law. -/
theorem endpointIdempotent_comp {X Y : C} (f : X ⟶ Y) (hf : I.rlp.llp f) :
    endpointIdempotent I κ f hf ≫ endpointIdempotent I κ f hf =
      endpointIdempotent I κ f hf := by
  let R := underRetract I κ f hf
  change (R.r ≫ R.i) ≫ (R.r ≫ R.i) = R.r ≫ R.i
  calc
    _ = R.r ≫ (R.i ≫ (R.r ≫ R.i)) := Category.assoc _ _ _
    _ = R.r ≫ ((R.i ≫ R.r) ≫ R.i) :=
      congrArg (fun m => R.r ≫ m) (Category.assoc R.i R.r R.i).symm
    _ = R.r ≫ (𝟙 (Under.mk f) ≫ R.i) :=
      congrArg (fun m => R.r ≫ (m ≫ R.i)) R.retract
    _ = _ := congrArg (fun m => R.r ≫ m) (Category.id_comp R.i)

end CategoryTheory.SmallObject.NativeSmallObjectPresentation

namespace HomotopicalAlgebra.CofibrantGenerationData

open CategoryTheory CategoryTheory.MorphismProperty
open CategoryTheory.SmallObject.NativeSmallObjectPresentation

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The ACTUAL original base cofibration is in the original I-generated left class. -/
theorem originalCofibration_left {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    d.I.rlp.llp f := by
  rw [d.I_rlp, trivialFibrations_llp]
  exact hf

/-- Every ACTUAL original base cofibration has a tree of its OWN original native left factor. -/
def originalCofibrationUnderRetract {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    Retract (Under.mk f)
      (nativeTree d.I κ f).endpointObj := by
  letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  exact underRetract d.I κ f (originalCofibration_left d f hf)

/-- The same actual original base cofibration has the full identity-on-source Arrow retract. -/
def originalCofibrationArrowRetract {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    RetractArrow f (nativeTree d.I κ f).hom := by
  letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  exact arrowRetract d.I κ f (originalCofibration_left d f hf)

end HomotopicalAlgebra.CofibrantGenerationData
