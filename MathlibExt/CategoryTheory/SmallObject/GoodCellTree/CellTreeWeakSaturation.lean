/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRootBaseChange
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeIncrement
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Weak saturation of the actual original cell-tree endpoint

The filtration uses the selected colimits on literal lower subsets of the
original vertex carrier. Successors attach their original generator and limits
use the original filtered-union colimits. The root and endpoint are unchanged.
-/

@[expose] public section

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.CellTreeWeakSaturation

open Limits LowerSetColimits CompactRootBaseChange

variable {C : Type u} [Category.{v} C] {P : Type w} [PartialOrder P]
  {α : Type t} {s : α → Arrow C} {X : C}

section Filtration

variable [WellFoundedLT P] (T : CellTree s X (P := P))
  (M : LowerSetColimitData T.diagram)

attribute [local instance] constructionIndexWellFounded constructionIndexSuccOrder

/-- The original lower prefixes indexed by their actual well-order extension. -/
abbrev prefixFunctor : ConstructionIndex P ⥤ LowerSet P := originalPrefix_mono.functor

/-- Every stage is the actual selected colimit under the original root. -/
abbrev diagramUnder : ConstructionIndex P ⥤ Under X := prefixFunctor (P := P) ⋙ M.functor

/-- The same original selected-piece diagram in the coefficient category. -/
abbrev diagram : ConstructionIndex P ⥤ C := diagramUnder T M ⋙ Under.forget X

/-- The genuine strict stage prefix retains its literal original lower sets. -/
abbrev limitPrefixes (γ : ConstructionIndex P) : Set.Iio γ ⥤ LowerSet P :=
  (Set.principalSegIio γ).monotone.functor ⋙ prefixFunctor (P := P)

/-- Original labels in a limit stage are exactly the union of earlier prefixes. -/
theorem limitUnion_eq (γ : ConstructionIndex P) (hγ : Order.IsSuccLimit γ) :
    LowerSetColimitData.filteredUnion (limitPrefixes (P := P) γ) = originalPrefix γ := by
  ext a
  change a ∈ (⨆ δ : Set.Iio γ, originalPrefix δ.1) ↔ a ∈ originalPrefix γ
  rw [LowerSet.mem_iSup_iff]
  exact (originalPrefix_limit_membership γ hγ a).symm

/-- The actual original union colimit gives the strict-prefix universal property. -/
def limitIsColimitUnder (γ : ConstructionIndex P) (hγ : Order.IsSuccLimit γ) :
    IsColimit ((Set.principalSegIio γ).cocone (diagramUnder T M)) := by
  letI : Nonempty (Set.Iio γ) := ⟨⟨⊥, hγ.bot_lt⟩⟩
  letI : IsFiltered (Set.Iio γ) := inferInstance
  let B := limitPrefixes (P := P) γ
  let e : M.obj (LowerSetColimitData.filteredUnion B) ≅ M.obj (originalPrefix γ) :=
    M.functor.mapIso (eqToIso (limitUnion_eq (P := P) γ hγ))
  exact IsColimit.ofIsoColimit (M.isColimitFilteredCocone (B := B)) (Cocone.ext e (by
    intro δ
    change M.map _ ≫ M.map _ = M.map _
    rw [M.map_comp]))

/-- Forgetting the original root preserves these actual connected limit cocones. -/
theorem isWellOrderContinuous : (diagram T M).IsWellOrderContinuous where
  nonempty_isColimit γ hγ := by
    let : Nonempty (Set.Iio γ) := ⟨⟨⊥, hγ.bot_lt⟩⟩
    let : IsFiltered (Set.Iio γ) := inferInstance
    let : IsConnected (Set.Iio γ) := inferInstance
    exact ⟨isColimitOfPreserves (Under.forget X) (limitIsColimitUnder T M γ hγ)⟩

/-- The actual initial selected piece compares with the original identity under X. -/
def botIsoUnder : (diagramUnder T M).obj ⊥ ≅ Under.mk (𝟙 X) :=
  M.functor.mapIso (eqToIso (originalPrefix_bot (P := P))) ≪≫ T.emptyLowerIso M

/-- The actual final selected piece compares with the recorded whole endpoint. -/
def topIsoUnder : (diagramUnder T M).obj ⊤ ≅ T.endpointObj :=
  M.functor.mapIso (eqToIso (originalPrefix_top (P := P))) ≪≫ T.endpointIso M

/-- The original source comparison in the coefficient category. -/
def botIso : (diagram T M).obj ⊥ ≅ X := (Under.forget X).mapIso (botIsoUnder T M)

/-- The endpoint comparison keeps the caller's actual endpoint object. -/
def topIso : (diagram T M).obj ⊤ ≅ T.endpointObj.right :=
  (Under.forget X).mapIso (topIsoUnder T M)

/-- All actual stage legs to the unchanged original endpoint. -/
def endpoint : diagram T M ⟶ (Functor.const _).obj T.endpointObj.right where
  app γ := (diagram T M).map (homOfLE le_top) ≫ (topIso T M).hom
  naturality γ δ f := by
    change (diagram T M).map f ≫
      ((diagram T M).map (homOfLE le_top) ≫ (topIso T M).hom) =
      ((diagram T M).map (homOfLE le_top) ≫ (topIso T M).hom) ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp_assoc]
    exact congrArg (fun h => (diagram T M).map h ≫ (topIso T M).hom)
      (Subsingleton.elim _ _)

/-- The genuine final stage supplies the whole original endpoint universal property. -/
def endpointIsColimit : IsColimit (Cocone.mk T.endpointObj.right (endpoint T M)) :=
  IsColimit.ofIsoColimit (colimitOfDiagramTerminal isTerminalTop (diagram T M))
    (Cocone.ext (topIso T M) (by intro γ; rfl))

/-- Both original Under comparisons identify the complete composite with T.hom. -/
theorem root_endpoint :
    (botIso T M).inv ≫ (endpoint T M).app ⊥ = T.hom := by
  let f : Under.mk (𝟙 X) ⟶ T.endpointObj :=
    (botIsoUnder T M).inv ≫ (diagramUnder T M).map (homOfLE bot_le) ≫ (topIsoUnder T M).hom
  simpa only [f, botIso, topIso, endpoint, diagram, Functor.mapIso_inv,
    Functor.mapIso_hom, Functor.comp_map, Under.forget_map, Under.comp_right,
    Under.mk_hom, Category.id_comp, CellTree.hom] using Under.w f

/-- A fully constructed original-root, original-endpoint history on the original labels. -/
def presentation : TransfiniteCompositionOfShape (ConstructionIndex P) T.hom where
  F := diagram T M
  isoBot := botIso T M
  isWellOrderContinuous := isWellOrderContinuous T M
  incl := endpoint T M
  isColimit := endpointIsColimit T M
  fac := root_endpoint T M

variable (W : MorphismProperty C) [W.IsStableUnderCobaseChange]

/-- At a real birth stage the actual lower comparison is a pushout of its original cell. -/
theorem label_map_mem (hCell : ∀ a : P, W (s (T.label a)).hom) (a : P) :
    W ((diagram T M).map (homOfLE (Order.le_succ (constructionLabel a)))) := by
  let B := originalPrefix (constructionLabel a)
  let a' : CellTreeIncrement.Label B (⊤ : LowerSet P) :=
    ⟨a, by
      constructor
      · simp
      · exact notMem_originalPrefix_label a⟩
  have hUnion := (CellTreeIncrement.successorUnionIsPushout T M B ⊤ a').map (Under.forget X)
  have hPush := (CellTreeIncrement.originalSelectedIsPushout T M a).paste_horiz hUnion.flip
  have h := W.of_isPushout hPush (hCell a)
  have hB : B ⊔ LowerSet.Iio a = B :=
    sup_eq_left.mpr (predecessor_le_originalPrefix a)
  have hD : B ⊔ LowerSet.Iic a = originalPrefix (Order.succ (constructionLabel a)) :=
    (originalPrefix_succ_label a).symm
  let eS := M.functor.mapIso (eqToIso hB)
  let eT := M.functor.mapIso (eqToIso hD)
  let target := originalPrefix_mono (Order.le_succ (constructionLabel a))
  let e : Arrow.mk (M.map (sup_le_sup_left
      (show LowerSet.Iio a ≤ LowerSet.Iic a from fun _ h => h.le) B)).right ≅
      Arrow.mk (M.map target).right :=
    Arrow.isoMk ((Under.forget X).mapIso eS) ((Under.forget X).mapIso eT) (by
      change (M.map (leOfHom (eqToHom hB))).right ≫ (M.map target).right =
        (M.map _).right ≫ (M.map (leOfHom (eqToHom hD))).right
      rw [← Under.comp_right, ← Under.comp_right, M.map_comp, M.map_comp])
  exact (W.arrow_mk_iso_iff e).mp h

/-- The extra initial transition has unchanged empty original lower set. -/
theorem bot_map_isIso :
    IsIso ((diagram T M).map (homOfLE (Order.le_succ (⊥ : ConstructionIndex P)))) := by
  have e : originalPrefix (⊥ : ConstructionIndex P) = originalPrefix (Order.succ ⊥) :=
    originalPrefix_bot.trans originalPrefix_succ_bot.symm
  have hf : homOfLE (originalPrefix_mono (Order.le_succ (⊥ : ConstructionIndex P))) =
      eqToHom e := Subsingleton.elim _ _
  change IsIso ((Under.forget X).map (M.functor.map
    (homOfLE (originalPrefix_mono (Order.le_succ (⊥ : ConstructionIndex P))))))
  rw [hf]
  change IsIso (((Under.forget X).mapIso (M.functor.mapIso (eqToIso e))).hom)
  infer_instance

variable [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W]

/-- Every genuine successor is an original generator pushout or the empty initial isomorphism. -/
theorem successor_map_mem (hCell : ∀ a : P, W (s (T.label a)).hom)
    (γ : ConstructionIndex P) (hγ : ¬IsMax γ) :
    W ((diagram T M).map (homOfLE (Order.le_succ γ))) := by
  rcases constructionIndex_cases γ with rfl | rfl | ⟨a, rfl⟩
  · let := bot_map_isIso T M
    exact W.of_isIso _
  · exact (hγ isMax_top).elim
  · exact label_map_mem T M W hCell a

end Filtration

/-- Actual generating weak saturation contains the actual original CellTree endpoint arrow. -/
theorem hom_mem (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W]
    (T : CellTree s X (P := P)) (M : LowerSetColimitData T.diagram)
    (hCell : ∀ a : P, W (s (T.label a)).hom) : W T.hom := by
  let : WellFoundedLT P := T.wellFoundedLT
  let : WellFoundedLT (ConstructionIndex P) := constructionIndexWellFounded
  let : SuccOrder (ConstructionIndex P) := constructionIndexSuccOrder
  let history : W.TransfiniteCompositionOfShape (ConstructionIndex P) T.hom :=
    { toTransfiniteCompositionOfShape := presentation T M
      map_mem := successor_map_mem T M W hCell }
  exact W.transfiniteCompositionsOfShape_le _ _ history.mem

end CategoryTheory.SmallObject.CellTreeWeakSaturation
