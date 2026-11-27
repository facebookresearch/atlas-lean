/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Codex
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellTreeGoodification
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalSplitFiltrationConstruction
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.NativeSmallObjectPresentation
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeWeakSaturation
public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.CompactBaseGenerators

/-!
# Good compact-cell trees of the actual original coefficient cofibrations

The original small-object tree and its actual source-fixed retract are refined,
split using the constructed original support history and compact birth charts,
and refined again. The final endpoint cocone is at the original target under
the original source. Only original cell ends are compact; the whole source,
target and vertex carriers stay arbitrary. No completed good tree, support
history, compact chart or endpoint comparison is an input to the producer.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe w t u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra HomotopicalAlgebra.FunctorInjective

namespace CategoryTheory.SmallObject.OriginalCofibrationGoodTree

section OriginalRetract

variable {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}
  {E F : Under X}

/-- The full actual retract under X gives a whole Arrow retract with both source maps the
identity. -/
def sourceFixedArrowRetract (R : Retract (Under.mk f) E) : RetractArrow f E.hom where
  i := Arrow.homMk (𝟙 X) R.i.right (by
    change 𝟙 X ≫ E.hom = f ≫ R.i.right
    rw [Category.id_comp]
    exact (Under.w R.i).symm)
  r := Arrow.homMk (𝟙 X) R.r.right (by
    change 𝟙 X ≫ f = E.hom ≫ R.r.right
    rw [Category.id_comp]
    exact (Under.w R.r).symm)
  retract := by
    ext
    · exact Category.id_comp _
    · exact congrArg Under.Hom.right R.retract

/-- The actual original inclusion square retains identity on the original source. -/
theorem sourceFixedArrowRetract_inclusion_source (R : Retract (Under.mk f) E) :
    (sourceFixedArrowRetract R).i.left = 𝟙 X := rfl

/-- The actual original projection square retains identity on the original source. -/
theorem sourceFixedArrowRetract_projection_source (R : Retract (Under.mk f) E) :
    (sourceFixedArrowRetract R).r.left = 𝟙 X := rfl

/-- The entire original target inclusion is retained by the source-fixed Arrow retract. -/
theorem sourceFixedArrowRetract_inclusion_target (R : Retract (Under.mk f) E) :
    (sourceFixedArrowRetract R).i.right = R.i.right := rfl

/-- The entire original target projection is retained by the source-fixed Arrow retract. -/
theorem sourceFixedArrowRetract_projection_target (R : Retract (Under.mk f) E) :
    (sourceFixedArrowRetract R).r.right = R.r.right := rfl

end OriginalRetract

section OriginalEndpoint

variable {C : Type u} [Category.{v} C]
  {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C} {X Y : C}
  (T : CellTree s X (P := P)) {f : X ⟶ Y} (e : T.endpointObj ≅ Under.mk f)

/-- The transported endpoint uses the same vertex cocone legs followed by the actual comparison. -/
abbrev retainedEndpointCocone : Cocone T.diagram where
  pt := Under.mk f
  ι :=
    { app p := T.inclusion p ≫ e.hom
      naturality a b h := by
        change T.diagram.map h ≫ (T.inclusion b ≫ e.hom) =
          (T.inclusion a ≫ e.hom) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, T.endpoint.cocone.w h] }

/-- The actual whole-tree UP transports to the original target through the constructed
comparison. -/
def retainedEndpointIsColimit : IsColimit (retainedEndpointCocone T e) :=
  IsColimit.ofIsoColimit T.endpoint.isColimit (Cocone.ext e (fun _ => rfl))

/-- Retain the complete tree fields and install its actual endpoint cocone at the original arrow
f. -/
def retainOriginalEndpoint : CellTree s X (P := P) :=
  { T with endpoint :=
      { cocone := retainedEndpointCocone T e
        isColimit := retainedEndpointIsColimit T e } }

/-- The entire vertex diagram and all its maps survive endpoint retention literally. -/
theorem retainOriginalEndpoint_diagram : (retainOriginalEndpoint T e).diagram = T.diagram := rfl

/-- All actual original predecessor cocones and their UPs survive endpoint retention literally. -/
theorem retainOriginalEndpoint_predecessor :
    (retainOriginalEndpoint T e).predecessor = T.predecessor := rfl

/-- The resulting root-to-endpoint arrow is literally the actual original f. -/
theorem retainOriginalEndpoint_hom : (retainOriginalEndpoint T e).hom = f := rfl

/-- Every original vertex inclusion retains its full endpoint comparison map. -/
theorem retainOriginalEndpoint_inclusion (p : P) :
    (retainOriginalEndpoint T e).inclusion p = T.inclusion p ≫ e.hom := rfl

/-- The selected cells and all predecessor bounds stay good after retaining the original
endpoint. -/
theorem retainOriginalEndpoint_good (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (good : T.IsGood chi) : (retainOriginalEndpoint T e).IsGood chi where
  presentable_source p := good.presentable_source p
  presentable_target p := good.presentable_target p
  predecessor_lt p := good.predecessor_lt p

end OriginalEndpoint

section Output

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X Y : C} (f : X ⟶ Y)

/-- An actual produced good compact-cell tree, with its original root, target and complete
cocones. -/
structure Data where
  /-- Only the actual vertex carrier is in the working universe. -/
  index : Type w
  /-- The actual good refining order on the produced birth labels. -/
  order : PartialOrder index
  /-- The original actual compact scalar birth arrows. -/
  cells : index → Arrow C
  /-- The complete original-root tree, including all predecessor and endpoint UPs. -/
  tree : @CellTree C _ index order index cells X
  /-- The actual chosen lower cocones derived by the final goodification. -/
  lowerData : @LowerSetColimitData index order.toPreorder (Under X) _ tree.diagram
  /-- The original birth labels are retained literally. -/
  label_eq : @CellTree.label C _ index order index cells X tree = id
  /-- The actual original target arrow is the final chosen endpoint object. -/
  endpoint_eq : @CellTree.endpointObj C _ index order index cells X tree = Under.mk f
  /-- Every individual predecessor has the selected bound and all cell ends are compact. -/
  good : @CellTree.IsGood C _ index order index cells X tree chi _
  /-- Every actual birth arrow is an original scalar cofibration with compact original ends. -/
  cell_mem : ∀ p, compactBaseCofibrationArrows C chi (cells p)

end Output

section OutputMaps

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  {chi : Cardinal.{w}} [Fact chi.IsRegular] {X Y : C} {f : X ⟶ Y}
  (H : Data chi f)

/-- The produced tree has its actual complete presentation of the same original arrow. -/
abbrev Data.presentation :
    letI := H.order
    CellTree.Presentation (s := H.cells) (P := H.index) f := by
  letI := H.order
  exact ⟨H.tree, eqToIso H.endpoint_eq⟩

/-- The whole forward endpoint comparison retains the actual original source arrow. -/
theorem Data.root :
    letI := H.order
    H.tree.hom ≫ (eqToIso H.endpoint_eq).hom.right = f :=
  Under.w (eqToIso H.endpoint_eq).hom

/-- The whole inverse endpoint comparison retains the same actual original source arrow. -/
theorem Data.inverse_root :
    letI := H.order
    f ≫ (eqToIso H.endpoint_eq).inv.right = H.tree.hom :=
  Under.w (eqToIso H.endpoint_eq).inv

/-- Every produced actual scalar cell is an original coefficient cofibration. -/
theorem Data.cell_cofibration (p : H.index) : cofibrations C (H.cells p).hom :=
  (H.cell_mem p).1

/-- Every produced actual scalar cell source is compact at the same selected rank. -/
theorem Data.cell_source_presentable (p : H.index) :
    IsCardinalPresentable (H.cells p).left chi := (H.cell_mem p).2.1

/-- Every produced actual scalar cell target is compact at the same selected rank. -/
theorem Data.cell_target_presentable (p : H.index) :
    IsCardinalPresentable (H.cells p).right chi := (H.cell_mem p).2.2

end OutputMaps

section ActualCompactCells

open OriginalSplitFiltrationConstruction OriginalIdempotentSupportHistory
  OriginalIdempotentLowerSupport

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {P : Type w} [PartialOrder P] [WellFoundedLT P]
  {alpha : Type t} {s : alpha → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (q : T.endpointObj ⟶ T.endpointObj) (hq : q ≫ q = q)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)
  (hCell : ∀ p : P, cofibrations C (s (T.label p)).hom)

include hCell in
/-- Every actual chosen compact birth chart is a scalar cofibration, derived from the original
cells. -/
theorem compactCells_cofibration (p : HistoryIndex (P := P)) :
    cofibrations C (compactCells T L q hq chi hUncountable good p).hom := by
  let _ : (cofibrations C).IsStableUnderTransfiniteComposition.{w} := by
    rw [← trivialFibrations_llp C]
    infer_instance
  exact BoundedDifferenceSplitChart.scalar_memForInclusion T L
    (before T L q hq chi hUncountable good p) (after T L q hq chi hUncountable good p)
    (beforeToAfter T L q hq chi hUncountable good p) chi good
    (birth_difference_bounded T L q hq chi hUncountable good p) (cofibrations C) hCell
    (birthChart T L q hq chi hUncountable good p).beta
    (birthChart T L q hq chi hUncountable good p).cell.hom
    (birthChart T L q hq chi hUncountable good p).scalarRetract

end ActualCompactCells

section ActualRetractConstruction

open OriginalGoodification OriginalSplitFiltrationConstruction
  OriginalIdempotentSupportHistory

variable {C : Type u} [cCategory : Category.{v} C] [ModelCategory C]
  {P : Type w} [pOrder : PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  {X Y : C} (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [regular : Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hUncountable : Cardinal.aleph0 < chi)
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)
  (hCell : ∀ p : P, cofibrations C (s (O.label p)).hom)
  (f : X ⟶ Y) (R : Retract (Under.mk f) O.endpointObj)

/-- The actual original tree and retract construct a full good compact-cell presentation of f. -/
def fromOriginalCellTree : Data chi f := by
  letI cColimits : HasColimitsOfSize.{w, w} C := inferInstance
  let G := cellTreeGoodification O M chi hSource hTarget
  let firstOrder := @CellTreeGoodification.order P pOrder C cCategory cColimits
    alpha s X O M chi regular G
  let T := @CellTreeGoodification.tree P pOrder C cCategory cColimits
    alpha s X O M chi regular G
  let L := @CellTreeGoodification.lowerData P pOrder C cCategory cColimits
    alpha s X O M chi regular G
  let e := @CellTreeGoodification.endpointIso P pOrder C cCategory cColimits
    alpha s X O M chi regular G
  let R' : Retract (Under.mk f) T.endpointObj := R.trans (Retract.ofIso e.symm)
  have good : @CellTree.IsGood C cCategory P firstOrder alpha s X T chi _ :=
    @CellTreeGoodification.good P pOrder C cCategory cColimits
      alpha s X O M chi regular G
  have labels : @CellTree.label C cCategory P firstOrder alpha s X T =
      @CellTree.label C cCategory P pOrder alpha s X O := by
    funext p
    exact @CellTreeGoodification.labels P pOrder C cCategory cColimits
      alpha s X O M chi regular G p
  letI : PartialOrder P := firstOrder
  letI : WellFoundedLT P := T.wellFoundedLT
  have hCell' : ∀ p : P, cofibrations C (s (T.label p)).hom := by
    intro p
    rw [congrFun labels p]
    exact hCell p
  let q := R'.r ≫ R'.i
  let hq := OriginalRetractSplitIso.idempotent_idempotent R'.i R'.r R'.retract
  let cells := compactCells T L q hq chi hUncountable good
  let historyOrder : PartialOrder (HistoryIndex (P := P)) := inferInstance
  let S := originalSplitTree T L chi hUncountable good R'.i R'.r R'.retract
  have hSource' : ∀ p, IsCardinalPresentable (cells (S.label p)).left chi := by
    intro p
    exact originalSplitTree_cell_source_presentable T L chi hUncountable good
      R'.i R'.r R'.retract p
  have hTarget' : ∀ p, IsCardinalPresentable (cells (S.label p)).right chi := by
    intro p
    exact originalSplitTree_cell_target_presentable T L chi hUncountable good
      R'.i R'.r R'.retract p
  let M' := S.lowerData
  let G' := cellTreeGoodification S M' chi hSource' hTarget'
  let secondOrder := @CellTreeGoodification.order (HistoryIndex (P := P)) historyOrder
    C cCategory cColimits (HistoryIndex (P := P)) cells X S M' chi regular G'
  let T' := @CellTreeGoodification.tree (HistoryIndex (P := P)) historyOrder
    C cCategory cColimits (HistoryIndex (P := P)) cells X S M' chi regular G'
  let L' := @CellTreeGoodification.lowerData (HistoryIndex (P := P)) historyOrder
    C cCategory cColimits (HistoryIndex (P := P)) cells X S M' chi regular G'
  let e' : T'.endpointObj ≅ Under.mk f :=
    @CellTreeGoodification.endpointIso (HistoryIndex (P := P)) historyOrder
      C cCategory cColimits (HistoryIndex (P := P)) cells X S M' chi regular G'
  have good' := @CellTreeGoodification.good (HistoryIndex (P := P)) historyOrder
    C cCategory cColimits (HistoryIndex (P := P)) cells X S M' chi regular G'
  have labels' : @CellTree.label C cCategory (HistoryIndex (P := P)) secondOrder
      (HistoryIndex (P := P)) cells X T' = id := by
    funext p
    exact @CellTreeGoodification.labels (HistoryIndex (P := P)) historyOrder
      C cCategory cColimits (HistoryIndex (P := P)) cells X S M' chi regular G' p
  exact
    { index := HistoryIndex (P := P)
      order := secondOrder
      cells := cells
      tree := @retainOriginalEndpoint C cCategory (HistoryIndex (P := P)) secondOrder
        (HistoryIndex (P := P)) cells X Y T' f e'
      lowerData := L'
      label_eq := labels'
      endpoint_eq := rfl
      good := @retainOriginalEndpoint_good C cCategory (HistoryIndex (P := P)) secondOrder
        (HistoryIndex (P := P)) cells X Y T' f e' chi regular good'
      cell_mem := fun p =>
        ⟨compactCells_cofibration T L q hq chi hUncountable good hCell' p,
          originalSplitTree_cell_source_presentable T L chi hUncountable good
            R'.i R'.r R'.retract p,
          originalSplitTree_cell_target_presentable T L chi hUncountable good
            R'.i R'.r R'.retract p⟩ }

end ActualRetractConstruction

end CategoryTheory.SmallObject.OriginalCofibrationGoodTree

namespace HomotopicalAlgebra.CofibrantGenerationData

open CategoryTheory.SmallObject CategoryTheory.SmallObject.NativeSmallObjectPresentation
  CategoryTheory.SmallObject.OriginalCofibrationGoodTree
  CategoryTheory.SmallObject.OriginalSplitFiltrationConstruction

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {kappa : Cardinal.{w}} [Fact kappa.IsRegular] [OrderBot kappa.ord.ToType]
  (d : CofibrantGenerationData C kappa)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (hUncountable : Cardinal.aleph0 < chi)
  (hSource : ∀ i : d.I.toSet, IsCardinalPresentable i.1.left chi)
  (hTarget : ∀ i : d.I.toSet, IsCardinalPresentable i.1.right chi)

/-- The original coefficient model and its OWN native I factor construct a good tree of original
f. -/
def originalCofibrationGoodTree {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    Data chi f := by
  letI : d.I.IsCardinalForSmallObjectArgument kappa := d.I_smallObject
  let O := nativeTree d.I kappa f
  let Ra := d.originalCofibrationArrowRetract f hf
  have hsource : Ra.i.left = 𝟙 X := rfl
  let R : Retract (Under.mk f) O.endpointObj :=
    { i := arrowInclusion O f Ra hsource
      r := arrowProjection O f Ra hsource
      retract := arrowSplit O f Ra hsource }
  exact fromOriginalCellTree O O.lowerData chi hUncountable
    (fun p => hSource (O.label p)) (fun p => hTarget (O.label p))
    (fun p => CompactBaseGeneratorData.originalI_cofibration d (O.label p)) f R

include hUncountable hSource hTarget in
/-- Every actual original scalar cofibration has a full good compact-cell tree at the selected
rank. -/
theorem exists_originalCofibrationGoodTree {X Y : C} (f : X ⟶ Y)
    (hf : cofibrations C f) : Nonempty (Data chi f) :=
  ⟨d.originalCofibrationGoodTree chi hUncountable hSource hTarget f hf⟩

end HomotopicalAlgebra.CofibrantGenerationData

namespace HomotopicalAlgebra.FunctorInjective

open CategoryTheory.SmallObject.OriginalCofibrationGoodTree

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] {S : Type w} [SmallCategory S] (s : D ≌ S)

/-- Use the SAME constructed rank profile and original generator maps for every original
cofibration. -/
def sameProfileOriginalCofibrationGoodTree (b : BoundedConstruction d kappaLP s)
    {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) : Data b.cardinal f := by
  letI : IsCardinalLocallyPresentable C b.cardinal := b.profile.baseLocallyPresentable
  exact d.originalCofibrationGoodTree b.cardinal b.profile.uncountable
    b.profile.sourceI b.profile.targetI f hf

/-- The actual original base/index data select the rank and construct the full good tree
internally. -/
def constructedOriginalCofibrationGoodTree {X Y : C} (f : X ⟶ Y)
    (hf : cofibrations C f) : Data (boundedConstruction d kappaLP s).cardinal f :=
  sameProfileOriginalCofibrationGoodTree d kappaLP s (boundedConstruction d kappaLP s) f hf

/-- The internally produced rank supports an actual good presentation of every original
cofibration. -/
theorem exists_constructedOriginalCofibrationGoodTree {X Y : C} (f : X ⟶ Y)
    (hf : cofibrations C f) :
    Nonempty (Data (boundedConstruction d kappaLP s).cardinal f) :=
  ⟨constructedOriginalCofibrationGoodTree d kappaLP s f hf⟩

end HomotopicalAlgebra.FunctorInjective
