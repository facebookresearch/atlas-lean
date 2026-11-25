/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.Presentable.OriginalDiagramCardinalScale
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Tactic.NormNum

/-!
# Original cardinal-selection semantic clients

The concrete original root has cardinality exactly the selected chi, so it is
not chi-presentable. Its actual two-source-value fold cell has a nonmonomorphic
original endpoint map. Both original I and J labels remain, including unused J.
The empty tree uses its own same-rank nonpresentable root. Nonthin and infinite
original indices, whole lower maps and independent universes remain visible.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w uD vD uC vC uI uJ uP

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  CategoryTheory.Presentable.OriginalDiagramCardinalScale

namespace OriginalDiagramCardinalScaleExamples

/-- The actual original two-value fold generator. -/
def fold : Fin 2 ⟶ PUnit.{1} := ↾fun _ => PUnit.unit

/-- The entire original first family retains its original fold label. -/
def I (_ : PUnit.{1}) : Arrow (Type) := Arrow.mk fold

/-- The unused original second family still retains its actual endpoint bounds. -/
def J (_ : PUnit.{1}) : Arrow (Type) := Arrow.mk (↾fun _ : PUnit.{1} => (0 : Fin 2))

/-- The actual nonthin original index has its genuine original size dictionaries. -/
local instance nonthinIndex : Small.{0} WalkingParallelPair := inferInstance

local instance nonthinIndexLocallySmall : LocallySmall.{0} WalkingParallelPair := inferInstance

local instance baseRegular : Fact (originalBaseRank (C := Type)).IsRegular :=
  originalBaseRank_regular (C := Type)

local instance baseLP : IsCardinalLocallyPresentable (Type) (originalBaseRank (C := Type)) :=
  originalBaseRank_locallyPresentable (C := Type)

/-- Every actual bound is selected internally for the original nonthin index and both families. -/
def profile : Profile (originalBaseRank (C := Type)) (D := WalkingParallelPair) I J PUnit.{1} 0 :=
  scaleFromLocallyPresentable (D := WalkingParallelPair) I J PUnit.{1} 0

local instance profileRegular : Fact profile.chi.IsRegular := profile.regular

/-- The actual original root has cardinality exactly the same selected cardinal. -/
def originalRoot : Type := profile.chi.ord.ToType

/-- The constructed original root is not compact at the construction's actual selected rank. -/
theorem originalRoot_noncompact : ¬ IsCardinalPresentable originalRoot profile.chi := by
  intro h
  have hBound := (Types.isCardinalPresentable_iff profile.chi).1 h
  simp only [originalRoot, hasCardinalLT_iff_cardinal_mk_lt,
    Cardinal.mk_toType, Cardinal.card_ord] at hBound
  exact (lt_irrefl profile.chi) hBound

/-- The actual two source values embed into the original same-cardinality root. -/
def rootEmbedding : Fin 2 ↪ originalRoot :=
  Classical.choice ((Cardinal.le_def (Fin 2) originalRoot).1 (by
    change Cardinal.mk (Fin 2) ≤ Cardinal.mk profile.chi.ord.ToType
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact Cardinal.mk_le_aleph0.trans profile.uncountable.le))

/-- The original attaching function preserves both distinct original source values. -/
def originalAttach : Fin 2 ⟶ originalRoot := ↾rootEmbedding

/-- The original endpoint is the actual native pushout, on the same original root. -/
def originalEndpoint : Type := pushout originalAttach fold

/-- The whole original root-to-endpoint function is the native original pushout inclusion. -/
def originalArrow : originalRoot ⟶ originalEndpoint := pushout.inl originalAttach fold

/-- The whole original target-cell function is the same native target inclusion. -/
def originalCell : PUnit.{1} ⟶ originalEndpoint := pushout.inr originalAttach fold

/-- A genuine actual one-cell tree under the original nonpresentable root. -/
def originalTree : CellTree (combinedFamily I J) originalRoot (P := PUnit.{1}) :=
  CellTree.ofPushout (combinedFamily I J) originalRoot (Sum.inl PUnit.unit)
    originalAttach originalArrow originalCell (IsPushout.of_hasPushout originalAttach fold)

/-- The same actual original fold is genuinely nonmonomorphic. -/
theorem fold_nonmono : ¬ Mono fold := by
  intro h
  have hi := (mono_iff_injective fold).1 h
  have he : (0 : Fin 2) = 1 := hi rfl
  norm_num at he

/-- The original whole endpoint function is also genuinely nonmonomorphic. -/
theorem originalArrow_nonmono : ¬ Mono originalArrow := by
  intro h
  have hi := (mono_iff_injective originalArrow).1 h
  have hc : originalAttach ≫ originalArrow = fold ≫ originalCell :=
    pushout.condition
  have h0 := congrArg (fun f : Fin 2 ⟶ originalEndpoint => f (0 : Fin 2)) hc
  have h1 := congrArg (fun f : Fin 2 ⟶ originalEndpoint => f (1 : Fin 2)) hc
  have he : originalArrow (originalAttach (0 : Fin 2)) =
      originalArrow (originalAttach (1 : Fin 2)) := h0.trans h1.symm
  have hSource : (0 : Fin 2) = 1 := rootEmbedding.injective (hi he)
  norm_num at hSource

/-- The actual constructor chooses its rank and constructs every original compact-root value. -/
def result :
    SelectedCompactRoot (originalBaseRank (C := Type)) (D := WalkingParallelPair)
      I J originalTree 0 :=
  compactRootFromLocallyPresentable (D := WalkingParallelPair) I J originalTree 0

local instance resultRegular : Fact result.profile.chi.IsRegular := result.profile.regular

/-- The selection remains the same original profile independently of the root and cell maps. -/
theorem result_profile : result.profile = profile := rfl

/-- Every unused original J target has the selected-rank presentability proof as well. -/
theorem unused_J_target : IsCardinalPresentable (J PUnit.unit).right profile.chi :=
  profile.target_presentable (Sum.inr PUnit.unit)

/-- The whole new label function retains the same original I label. -/
theorem result_labels : result.presentation.tree.label = originalTree.label :=
  result.presentation.label_eq

/-- The actual selected new root is compact, while its original root is not. -/
theorem result_root_presentable : IsCardinalPresentable result.presentation.root profile.chi :=
  result.presentation.root_presentable

/-- The actual new endpoint is compact with no compactness assumption on the old root. -/
theorem result_endpoint_presentable :
    IsCardinalPresentable result.presentation.tree.endpointObj.right profile.chi :=
  result.presentation.endpoint_presentable

/-- Every actual new lower piece is presentable at that same original selected rank. -/
theorem result_lower_presentable (B : LowerSet PUnit.{1}) :
    IsCardinalPresentable (result.presentation.lower.obj B).right profile.chi :=
  result.presentation.lower_presentable B

/-- Every original lower pair retains its entire original forward map. -/
theorem result_lower_map (B E : LowerSet PUnit.{1}) (h : B ≤ E) :
    (Under.pushout result.presentation.rootMap).map (result.presentation.lower.map h) ≫
        (result.presentation.lowerComparison originalTree.lowerData).hom.app E =
      (result.presentation.lowerComparison originalTree.lowerData).hom.app B ≫
        originalTree.lowerData.map h :=
  result.lower_map originalTree.lowerData B E h

/-- Every original lower pair retains its entire original inverse map. -/
theorem result_lower_map_inv (B E : LowerSet PUnit.{1}) (h : B ≤ E) :
    originalTree.lowerData.map h ≫
        (result.presentation.lowerComparison originalTree.lowerData).inv.app E =
      (result.presentation.lowerComparison originalTree.lowerData).inv.app B ≫
        (Under.pushout result.presentation.rootMap).map (result.presentation.lower.map h) :=
  result.lower_map_inv originalTree.lowerData B E h

/-- The original native predecessor point is still the identity under the original root. -/
def originalPredecessorIso (p : PUnit.{1}) :
    originalTree.predecessorObj p ≅ Under.mk (𝟙 originalRoot) := eqToIso rfl

/-- The actual new attaching coefficient returns to the same native original predecessor. -/
def attachingCoefficient (p : PUnit.{1}) :
    (result.presentation.tree.predecessorObj p).right ⟶ originalRoot :=
  pushout.inl (result.presentation.tree.predecessorObj p).hom result.presentation.rootMap ≫
    (result.presentation.predecessorComparison p).hom.right ≫ (originalPredecessorIso p).hom.right

/-- The whole new attaching function interpreted at the actual original coefficient point. -/
def returnedAttach (p : PUnit.{1}) : Fin 2 ⟶ originalRoot :=
  result.presentation.tree.attaching p ≫ attachingCoefficient p

/-- Both original attaching values are retained through the actual whole-function field. -/
theorem returnedAttach_eq (p : PUnit.{1}) : returnedAttach p = originalAttach := by
  let g := result.presentation.tree.attaching p
  let u := pushout.inl (result.presentation.tree.predecessorObj p).hom result.presentation.rootMap
  let e := (result.presentation.predecessorComparison p).hom.right
  let z := (originalPredecessorIso p).hom.right
  have h := congrFun result.presentation.attaching_function p
  change g ≫ u ≫ e = 𝟙 (Fin 2) ≫ originalTree.attaching p at h
  have hPost := congrArg (fun f : Fin 2 ⟶ (originalTree.predecessorObj p).right => f ≫ z)
    (h.trans (Category.id_comp _))
  have hAssoc : (g ≫ u ≫ e) ≫ z = g ≫ u ≫ e ≫ z :=
    (Category.assoc g (u ≫ e) z).trans
      (congrArg (fun f => g ≫ f) (Category.assoc u e z))
  change g ≫ u ≫ e ≫ z = originalAttach
  exact hAssoc.symm.trans hPost

/-- The complete actual attaching map retains both finite source values separately. -/
theorem returnedAttach_value (p : PUnit.{1}) (b : Fin 2) :
    returnedAttach p b = rootEmbedding b :=
  congrArg (fun f : Fin 2 ⟶ originalRoot => f b) (returnedAttach_eq p)

/-- The original distinct attaching values stay distinct in the actual returned new source map. -/
theorem returnedAttach_distinct (p : PUnit.{1}) :
    result.presentation.tree.attaching p (0 : Fin 2) ≠
      result.presentation.tree.attaching p (1 : Fin 2) := by
  intro h
  have he := congrArg (attachingCoefficient p) h
  have h0 := returnedAttach_value p (0 : Fin 2)
  have h1 := returnedAttach_value p (1 : Fin 2)
  have hs : rootEmbedding (0 : Fin 2) = rootEmbedding (1 : Fin 2) :=
    h0.symm.trans (he.trans h1)
  have heq : (0 : Fin 2) = 1 := rootEmbedding.injective hs
  norm_num at heq

/-- The original selected vertex is the same whole native quotient point. -/
def originalVertexIso (p : PUnit.{1}) :
    originalTree.vertex p ≅ Under.mk originalArrow := eqToIso rfl

/-- The actual new target coefficient returns to the same native original quotient. -/
def cellCoefficient (p : PUnit.{1}) :
    (result.presentation.tree.vertex p).right ⟶ originalEndpoint :=
  pushout.inl (result.presentation.tree.vertex p).hom result.presentation.rootMap ≫
    (result.presentation.comparison.hom.app p).right ≫ (originalVertexIso p).hom.right

/-- The whole new target-cell function interpreted at that same original coefficient point. -/
def returnedCell (p : PUnit.{1}) : PUnit.{1} ⟶ originalEndpoint :=
  result.presentation.tree.cell p ≫ cellCoefficient p

/-- The entire target-cell function is the same actual original native inclusion. -/
theorem returnedCell_eq (p : PUnit.{1}) : returnedCell p = originalCell := by
  let k := result.presentation.tree.cell p
  let u := pushout.inl (result.presentation.tree.vertex p).hom result.presentation.rootMap
  let e := (result.presentation.comparison.hom.app p).right
  let z := (originalVertexIso p).hom.right
  have h := congrFun result.presentation.cell_function p
  change k ≫ u ≫ e = 𝟙 PUnit.{1} ≫ originalTree.cell p at h
  have hPost := congrArg (fun f : PUnit.{1} ⟶ (originalTree.vertex p).right => f ≫ z)
    (h.trans (Category.id_comp _))
  have hAssoc : (k ≫ u ≫ e) ≫ z = k ≫ u ≫ e ≫ z :=
    (Category.assoc k (u ≫ e) z).trans
      (congrArg (fun f => k ≫ f) (Category.assoc u e z))
  change k ≫ u ≫ e ≫ z = originalCell
  exact hAssoc.symm.trans hPost

/-- Every actual original target value is retained separately. -/
theorem returnedCell_value (p b : PUnit.{1}) : returnedCell p b = originalCell b :=
  congrArg (fun f : PUnit.{1} ⟶ originalEndpoint => f b) (returnedCell_eq p)

/-- Every original root value retains the whole actual endpoint map in the forward direction. -/
theorem endpointRoot_value (x : originalRoot) :
    (pushout.inr result.presentation.tree.hom result.presentation.rootMap ≫
      result.presentation.endpointComparison.hom.right) x = originalArrow x :=
  congrArg (fun f : originalRoot ⟶ originalEndpoint => f x)
    (Under.w result.presentation.endpointComparison.hom)

/-- Every original root value retains the whole actual endpoint map in the inverse direction. -/
theorem endpointRoot_value_inv (x : originalRoot) :
    (originalArrow ≫ result.presentation.endpointComparison.inv.right) x =
      pushout.inr result.presentation.tree.hom result.presentation.rootMap x :=
  congrArg (fun f : originalRoot ⟶ pushout result.presentation.tree.hom
    result.presentation.rootMap => f x) (Under.w result.presentation.endpointComparison.inv)

/-- The whole original endpoint and both actual root maps form the same genuine pushout. -/
theorem result_endpoint_pushout :
    IsPushout result.presentation.tree.hom result.presentation.rootMap
      (pushout.inl result.presentation.tree.hom result.presentation.rootMap ≫
        result.presentation.endpointComparison.hom.right) originalArrow :=
  result.presentation.endpoint_isPushout

/-- The empty-tree profile is selected independently of its own arbitrary original root. -/
def emptyProfile :
    Profile (originalBaseRank (C := Type)) (D := WalkingParallelPair) I J PEmpty.{1} 0 :=
  scaleFromLocallyPresentable (D := WalkingParallelPair) I J PEmpty.{1} 0

local instance emptyRegular : Fact emptyProfile.chi.IsRegular := emptyProfile.regular

/-- The empty tree also uses an actual original root at exactly its own selected cardinal. -/
def emptyRoot : Type := emptyProfile.chi.ord.ToType

/-- The actual empty tree keeps its complete native identity endpoint and empty colimit UP. -/
def emptyTree : CellTree (combinedFamily I J) emptyRoot (P := PEmpty.{1}) :=
  CellTree.empty (combinedFamily I J) emptyRoot

/-- The empty original root is not presentable at that same selected cardinal. -/
theorem emptyRoot_noncompact : ¬ IsCardinalPresentable emptyRoot emptyProfile.chi := by
  intro h
  have hBound := (Types.isCardinalPresentable_iff emptyProfile.chi).1 h
  simp only [emptyRoot, hasCardinalLT_iff_cardinal_mk_lt,
    Cardinal.mk_toType, Cardinal.card_ord] at hBound
  exact (lt_irrefl emptyProfile.chi) hBound

/-- The actual empty original endpoint is not presentable either. -/
theorem emptyEndpoint_noncompact :
    ¬ IsCardinalPresentable emptyTree.endpointObj.right emptyProfile.chi :=
  emptyRoot_noncompact

/-- The full constructor handles the actual empty original carrier and nonpresentable root. -/
def emptyResult :
    SelectedCompactRoot (originalBaseRank (C := Type)) (D := WalkingParallelPair) I J emptyTree 0 :=
  compactRootFromLocallyPresentable (D := WalkingParallelPair) I J emptyTree 0

local instance emptyResultRegular : Fact emptyResult.profile.chi.IsRegular :=
  emptyResult.profile.regular

/-- Empty-tree cardinal selection retains the same independently constructed original profile. -/
theorem emptyResult_profile : emptyResult.profile = emptyProfile := rfl

/-- The actual new whole empty endpoint is compact while the original one remains noncompact. -/
theorem emptyResult_endpoint_presentable :
    IsCardinalPresentable emptyResult.presentation.tree.endpointObj.right emptyProfile.chi :=
  emptyResult.presentation.endpoint_presentable

/-- The empty result retains its entire native root-adjoined colimit, including its true UP. -/
def emptyAdjoined : ColimitCocone (UnderColimits.adjoinedDiagram
    (Y := emptyResult.presentation.tree.diagram)) :=
  UnderColimits.adjoinedColimit emptyResult.presentation.tree.endpoint

/-- The genuine empty-tree root-adjoined star leg is the actual new endpoint root function. -/
theorem emptyAdjoined_star : emptyAdjoined.cocone.ι.app WithInitial.star =
    emptyResult.presentation.tree.hom :=
  UnderColimits.adjoined_star emptyResult.presentation.tree.endpoint.cocone

/-- The infinite original index retains its actual object, Hom and coefficient size proofs. -/
local instance infiniteIndex : Small.{0} (Discrete ℕ) := inferInstance

local instance infiniteIndexLocallySmall : LocallySmall.{0} (Discrete ℕ) := inferInstance

/-- The actual infinite original index and total infinite cell carrier share the produced rank. -/
def infiniteProfile : Profile (originalBaseRank (C := Type)) (D := Discrete ℕ) I J ℕ 0 :=
  scaleFromLocallyPresentable (D := Discrete ℕ) I J ℕ 0

/-- Every actual original natural-number cell belongs to the same total-carrier bound. -/
theorem infinite_cell_bound : HasCardinalLT ℕ infiniteProfile.chi := infiniteProfile.cell_bound

/-- Every actual original infinite-index Arrow is bounded as a whole original carrier. -/
theorem infinite_arrow_bound : HasCardinalLT (Arrow (Discrete ℕ)) infiniteProfile.chi :=
  infiniteProfile.arrow_bound

/-- Every actual lower subset of the infinite original cell carrier retains its full object bound.
-/
theorem infinite_lower_object_bound (B : LowerSet ℕ) : HasCardinalLT B infiniteProfile.chi :=
  infiniteProfile.lower_object_bound B

/-- Every actual Arrow of every infinite-carrier lower subset is bounded as well. -/
theorem infinite_lower_arrow_bound (B : LowerSet ℕ) :
    HasCardinalLT (Arrow B) infiniteProfile.chi := infiniteProfile.lower_arrow_bound B

/-- Every literal infinite-carrier increment retains the same total original bound. -/
theorem infinite_increment_bound (B E : LowerSet ℕ) :
    HasCardinalLT (CellTree.Increment B E) infiniteProfile.chi :=
  infiniteProfile.increment_bound B E

/-- The whole original nonthin-diagram criterion is derived for every original diagram action. -/
theorem nonthin_component_criterion (F : WalkingParallelPair ⥤ Type) :
    IsCardinalPresentable F profile.chi ↔
      ∀ d : WalkingParallelPair, IsCardinalPresentable (F.obj d) profile.chi :=
  profile.presentable_iff_components F

end OriginalDiagramCardinalScaleExamples
