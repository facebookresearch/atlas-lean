/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalTransfiniteSliceFiltration
public import MathlibExt.CategoryTheory.Presentable.CompactDiagramCellTarget

/-!
# Compact attachments for actual original slice successors

The literal bounded original cell increments construct compact scalar roots,
their compact endpoints and the original component pushouts. The compact
whole-diagram producer captures these actual scalar attaching maps and every
original action at one common source stage. The actual original birth pushout
then gives the unchanged whole successor arrow.

This is the ordinary specialization of Jacob Lurie's *Higher Topos Theory*,
author PDF dated April 9, 2017, Lemma A.3.3.17, printed pages 883–884
(PDF pages 901–902), with the original compact-root arguments of A.1.5.6
and A.1.5.11. Original roots need not be presentable.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w t uD vD uC vC

namespace CategoryTheory.SmallObject.OriginalCompactSuccessorAttachments

open Limits DiagramActionCapture DiagramSliceExtensions DiagramSliceExhaustion
open CompactRootBaseChange

/-- Transport a proved attaching pushout along both maps of its actual right-hand Arrow iso. -/
theorem isPushoutOfArrowIso {K : Type uC} [Category.{vC} K]
    {X Y Z T X' T' : K} {u : Z ⟶ X} {g : Z ⟶ Y} {q : X ⟶ T} {v : Y ⟶ T}
    {q' : X' ⟶ T'} (H : IsPushout u g q v) (e : Arrow.mk q' ≅ Arrow.mk q) :
    IsPushout (u ≫ e.inv.left) g q' (v ≫ e.inv.right) := by
  refine H.of_iso' (Iso.refl _) (Arrow.leftFunc.mapIso e) (Iso.refl _)
    (Arrow.rightFunc.mapIso e) ?_ ?_ ?_ ?_
  · change 𝟙 _ ≫ u = (u ≫ (Arrow.leftFunc.mapIso e).inv) ≫ (Arrow.leftFunc.mapIso e).hom
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · exact e.hom.w
  · change 𝟙 _ ≫ v = (v ≫ (Arrow.rightFunc.mapIso e).inv) ≫ (Arrow.rightFunc.mapIso e).hom
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Postcomposition retains both complete factor maps of an original scalar chart. -/
theorem chartFactorPostcomposition {K : Type uC} [Category.{vC} K]
    {A X B Y Z : K} (a : A ⟶ X) (u : X ⟶ Y) (b : A ⟶ B)
    (t : B ⟶ Y) (e : Y ⟶ Z) (h : a ≫ u = b ≫ t) :
    a ≫ (u ≫ e) = b ≫ t ≫ e := by
  exact (Category.assoc a u e).symm.trans
    ((eq_whisker h e).trans (Category.assoc b t e))

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (good : ∀ d, (theta.component d).tree.IsGood chi)
  {A B : Slice theta L chi} (p : A ⟶ B)

omit [IsCardinalLocallyPresentable C chi] in
/-- The literal original relative cell-label carrier is bounded by the selected target slice. -/
theorem increment_bound (d : D) :
    HasCardinalLT (CellTree.Increment (A.supports d).1 (B.supports d).1) chi :=
  (B.supports d).2.of_injective
    (fun a => (⟨a.1, a.2.1⟩ : ((B.supports d).1 : Set (P d))))
    (fun _ _ h => Subtype.ext (congrArg
      (fun a : ((B.supports d).1 : Set (P d)) => a.1) h))

/-- The actual increment internally constructs its compact root and every original comparison. -/
def scalarRoot (d : D) : CompactRootPresentation chi (inclusionTree theta L chi p d) :=
  compactRootPresentation chi (inclusionTree theta L chi p d)
    (increment_bound theta L chi (A := A) (B := B) d)
    (fun a => (good d).presentable_source a.1)
    (fun a => (good d).presentable_target a.1)

/-- The actual new compact scalar arrow has the same original increment cell labels. -/
abbrev scalarArrow (d : D) := (scalarRoot theta L chi good p d).tree.hom

/-- The actual compact root map enters the same original selected source component. -/
abbrev scalarSourceMap (d : D) := (scalarRoot theta L chi good p d).rootMap

/-- The actual compact endpoint map enters the same original selected target component. -/
abbrev scalarTargetMap (d : D) :=
  pushout.inl (scalarArrow theta L chi good p d) (scalarSourceMap theta L chi good p d) ≫
    (scalarRoot theta L chi good p d).endpointComparison.hom.right

/-- Both actual original component maps form the derived scalar pushout. -/
theorem scalarIsPushout (d : D) :
    IsPushout (scalarSourceMap theta L chi good p d) (scalarArrow theta L chi good p d)
      (p.toNatTrans.app d) (scalarTargetMap theta L chi good p d) :=
  (scalarRoot theta L chi good p d).endpoint_isPushout.flip

variable (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
  [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W]
  (hCell : ∀ d (a : P d), W (s ((theta.component d).tree.label a)).hom)

include hCell in
/-- Derive membership from the preserved original cells in the constructed compact tree. -/
theorem scalar_mem (d : D) : W (scalarArrow theta L chi good p d) := by
  let R := scalarRoot theta L chi good p d
  apply CellTreeWeakSaturation.hom_mem W R.tree R.lower
  intro a
  rw [congrFun R.label_eq a]
  exact hCell d a.1

include hCell in
/-- The actual compact scalar charts construct the whole compact original inclusion attachment. -/
theorem existsCompactInclusionDiagram (hArrow : HasCardinalLT (Arrow D) chi) :
    ∃ (F0 G0 : D ⥤ C) (u : F0 ⟶ A.toFunctor theta L chi)
      (v : G0 ⟶ B.toFunctor theta L chi) (f0 : F0 ⟶ G0)
      (a0 : ∀ d, (scalarRoot theta L chi good p d).root ⟶ F0.obj d)
      (b0 : ∀ d, (scalarRoot theta L chi good p d).tree.endpointObj.right ⟶ G0.obj d),
      IsCardinalPresentable F0 chi ∧ IsCardinalPresentable G0 chi ∧
      (∀ d, IsCardinalPresentable (F0.obj d) chi ∧ IsCardinalPresentable (G0.obj d) chi) ∧
      (∀ d, W (f0.app d)) ∧ IsPushout u f0 p.toNatTrans v ∧
      ∀ d, IsPushout (a0 d) (scalarArrow theta L chi good p d) (f0.app d) (b0 d) ∧
        a0 d ≫ u.app d = scalarSourceMap theta L chi good p d ∧
        b0 d ≫ v.app d = scalarTargetMap theta L chi good p d := by
  obtain ⟨F0, G0, u, v, f0, a0, b0, hF, hG, hValues, hWhole, hCharts⟩ :=
    Presentable.existsCompactDiagramCellTarget chi hArrow
      (A.toFunctor theta L chi) (B.toFunctor theta L chi) p.toNatTrans
      (fun d => (scalarRoot theta L chi good p d).root)
      (fun d => (scalarRoot theta L chi good p d).tree.endpointObj.right)
      (scalarArrow theta L chi good p) (scalarSourceMap theta L chi good p)
      (scalarTargetMap theta L chi good p)
      (fun d => (scalarRoot theta L chi good p d).root_presentable)
      (fun d => (scalarRoot theta L chi good p d).endpoint_presentable)
      (scalarIsPushout theta L chi good p)
  refine ⟨F0, G0, u, v, f0, a0, b0, hF, hG, hValues, ?_, hWhole, hCharts⟩
  intro d
  exact W.of_isPushout (hCharts d).1 (scalar_mem theta L chi good p W hCell d)

section Births

variable {U : OriginalSlice theta L} {seed : Supports (P := P) chi}
  (E : OriginalTransfiniteSliceFiltration.Birth theta L chi U seed)

/-- The actual produced intersection-to-patch inclusion keeps both original natural maps. -/
def birthPatchMap : E.overlap ⟶ E.patch where
  support_le := E.intoPatch.le
  naturality := E.intoPatch.naturality

include hCell in
/-- Compact original scalar roots and the actual birth pushout construct its whole compact arrow. -/
theorem existsCompactBirthDiagram (hArrow : HasCardinalLT (Arrow D) chi) :
    ∃ (F0 G0 : D ⥤ C) (u : F0 ⟶ U.toFunctor)
      (v : G0 ⟶ E.after.toFunctor) (f0 : F0 ⟶ G0)
      (a0 : ∀ d, (scalarRoot theta L chi good (birthPatchMap theta L chi E) d).root ⟶ F0.obj d)
      (b0 : ∀ d, (scalarRoot theta L chi good
        (birthPatchMap theta L chi E) d).tree.endpointObj.right ⟶ G0.obj d),
      IsCardinalPresentable F0 chi ∧ IsCardinalPresentable G0 chi ∧
      (∀ d, IsCardinalPresentable (F0.obj d) chi ∧ IsCardinalPresentable (G0.obj d) chi) ∧
      (∀ d, W (f0.app d)) ∧ IsPushout u f0 E.beforeInclusion.toNatTrans v ∧
      ∀ d, IsPushout (a0 d) (scalarArrow theta L chi good (birthPatchMap theta L chi E) d)
          (f0.app d) (b0 d) ∧
        a0 d ≫ u.app d = scalarSourceMap theta L chi good (birthPatchMap theta L chi E) d ≫
          E.intoBefore.toNatTrans.app d ∧
        b0 d ≫ v.app d = scalarTargetMap theta L chi good (birthPatchMap theta L chi E) d ≫
          E.patchInclusion.toNatTrans.app d := by
  obtain ⟨F0, G0, u, v, f0, a0, b0, hF, hG, hValues, hMem, hWhole, hCharts⟩ :=
    existsCompactInclusionDiagram theta L chi good (birthPatchMap theta L chi E) W hCell hArrow
  refine ⟨F0, G0, u ≫ E.intoBefore.toNatTrans, v ≫ E.patchInclusion.toNatTrans,
    f0, a0, b0, hF, hG, hValues, hMem, hWhole.paste_horiz E.isPushout, ?_⟩
  intro d
  refine ⟨(hCharts d).1, ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ E.intoBefore.toNatTrans.app d) (hCharts d).2.1)
  · exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ E.patchInclusion.toNatTrans.app d) (hCharts d).2.2)

end Births

end CategoryTheory.SmallObject.OriginalCompactSuccessorAttachments

namespace HomotopicalAlgebra.FunctorInjective

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.OriginalCompactSuccessorAttachments
open CategoryTheory.SmallObject.CompactRootBaseChange

attribute [local instance] constructionIndexWellFounded constructionIndexSuccOrder

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d kappaLP s.equivalence) {F G : D ⥤ C}
  (f : F ⟶ G) (hf : ∀ a : D, cofibrations C (f.app a))

local instance originalCompactCoefficientLP : IsCardinalLocallyPresentable C b.cardinal :=
  b.profile.baseLocallyPresentable

local instance originalCompactPushouts : HasPushouts C := inferInstance

local instance originalCompactCofibrationsTC :
    (cofibrations C).IsStableUnderTransfiniteComposition.{w} := by
  rw [← trivialFibrations_llp C]
  infer_instance

local instance originalCompactDiagramLP : IsCardinalLocallyPresentable (D ⥤ C) b.cardinal :=
  b.profile.diagramLocallyPresentable

/-- The actual original model constructs the selected component trees at the SAME original rank. -/
abbrev originalCompactComponentPresentation :=
  letI := originalSliceComponentOrders d kappaLP s b f hf
  originalComponentPresentation d kappaLP (originalFiltrationSelectedIndex s).equivalence
    (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
    (originalFiltrationSelectedCofibration s f hf)

/-- All actual chosen original lower-colimit data are retained. -/
abbrev originalCompactComponentLowerData :=
  letI := originalSliceComponentOrders d kappaLP s b f hf
  originalComponentLowerData d kappaLP (originalFiltrationSelectedIndex s).equivalence
    (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
    (originalFiltrationSelectedCofibration s f hf)

/-- The SAME original selected trees have their actually constructed goodness proof. -/
theorem originalCompactComponentGood :
    letI := originalSliceComponentOrders d kappaLP s b f hf
    ∀ a, ((originalCompactComponentPresentation d kappaLP s b f hf).component a).tree.IsGood
      b.cardinal := by
  let := originalSliceComponentOrders d kappaLP s b f hf
  exact originalComponentGood d kappaLP (originalFiltrationSelectedIndex s).equivalence
    (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
    (originalFiltrationSelectedCofibration s f hf)

/-- The original born intersection-to-patch map retains every original lower function. -/
abbrev originalCompactPatchMap (p : originalSliceHistoryIndex d kappaLP s b f hf) :=
  letI := originalSliceComponentOrders d kappaLP s b f hf
  birthPatchMap (originalCompactComponentPresentation d kappaLP s b f hf)
    (originalCompactComponentLowerData d kappaLP s b f hf) b.cardinal
    (originalSliceBirth d kappaLP s b f hf p)

/-- The actual original scalar increment constructs its compact root, cells and all comparisons. -/
abbrev originalCompactScalarRoot (p : originalSliceHistoryIndex d kappaLP s b f hf)
    (a : s.index) :=
  letI := originalSliceComponentOrders d kappaLP s b f hf
  scalarRoot (originalCompactComponentPresentation d kappaLP s b f hf)
    (originalCompactComponentLowerData d kappaLP s b f hf) b.cardinal
    (originalCompactComponentGood d kappaLP s b f hf)
    (originalCompactPatchMap d kappaLP s b f hf p) a

/-- The produced compact scalar endpoint has its actual original target comparison map. -/
def originalCompactScalarTargetMap (p : originalSliceHistoryIndex d kappaLP s b f hf)
    (a : s.index) :=
  letI := originalSliceComponentOrders d kappaLP s b f hf
  scalarTargetMap (originalCompactComponentPresentation d kappaLP s b f hf)
    (originalCompactComponentLowerData d kappaLP s b f hf) b.cardinal
    (originalCompactComponentGood d kappaLP s b f hf)
    (originalCompactPatchMap d kappaLP s b f hf p) a

/-- Every actual original common scalar label is an original coefficient cofibration. -/
theorem originalCompactComponentCell (a : s.index)
    (x : originalComponentLabels d kappaLP (originalFiltrationSelectedIndex s).equivalence
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf) a) :
    letI := originalSliceComponentOrders d kappaLP s b f hf
    cofibrations C (OriginalCofibrationGoodTree.compactScalarArrows C b.cardinal
      (((originalCompactComponentPresentation d kappaLP s b f hf).component a).tree.label x)).hom :=
    by
  let := originalSliceComponentOrders d kappaLP s b f hf
  exact
    (((originalCompactComponentPresentation d kappaLP s b f hf).component a).tree.label
      x).property.1

-- Both transported scalar squares unfold the full original tree and coefficient model data.
set_option maxHeartbeats 1000000 in
-- The unchanged `change` steps unfold the bounded-construction data through the equivalence API.
/-- Construct the whole original compact attaching arrow for each actual native birth.
The compact scalar source and target maps are retained at every original object,
including both original factor equations into the same native successor square. -/
theorem originalCompactSuccessorAttachment (p : originalSliceHistoryIndex d kappaLP s b f hf) :
    letI := originalSliceComponentOrders d kappaLP s b f hf
    ∃ (F0 G0 : D ⥤ C)
      (u : F0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj
        (constructionLabel p))
      (v : G0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj
        (Order.succ (constructionLabel p))) (f0 : F0 ⟶ G0)
      (a0 : ∀ a : D, (originalCompactScalarRoot d kappaLP s b f hf p
        (s.equivalence.functor.obj a)).root ⟶ F0.obj a)
      (b0 : ∀ a : D, (originalCompactScalarRoot d kappaLP s b f hf p
        (s.equivalence.functor.obj a)).tree.endpointObj.right ⟶ G0.obj a),
      compactCofibrationArrows D C b.cardinal (Arrow.mk f0) ∧
      IsPushout u f0
        ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map
          (homOfLE (Order.le_succ (constructionLabel p)))) v ∧
      ∀ a : D, IsPushout (a0 a)
          (originalCompactScalarRoot d kappaLP s b f hf p (s.equivalence.functor.obj a)).tree.hom
          (f0.app a) (b0 a) ∧
        a0 a ≫ u.app a =
          (originalCompactScalarRoot d kappaLP s b f hf p (s.equivalence.functor.obj a)).rootMap ≫
            (originalSliceBirth d kappaLP s b f hf p).intoBefore.toNatTrans.app
              (s.equivalence.functor.obj a) ≫
                (originalTransfiniteFiltrationBirthIso d kappaLP s b f hf p).inv.left.app a ∧
        b0 a ≫ v.app a =
          originalCompactScalarTargetMap d kappaLP s b f hf p (s.equivalence.functor.obj a) ≫
            (originalSliceBirth d kappaLP s b f hf p).patchInclusion.toNatTrans.app
              (s.equivalence.functor.obj a) ≫
                (originalTransfiniteFiltrationBirthIso d kappaLP s b f hf p).inv.right.app a := by
  let := originalSliceComponentOrders d kappaLP s b f hf
  let theta := originalCompactComponentPresentation d kappaLP s b f hf
  let L := originalCompactComponentLowerData d kappaLP s b f hf
  let E := originalSliceBirth d kappaLP s b f hf p
  obtain ⟨F0, G0, u, v, f0, a0, b0, hF, hG, hValues, hMem, hWhole, hCharts⟩ :=
    existsCompactBirthDiagram theta L b.cardinal (originalCompactComponentGood d kappaLP s b f hf)
      (cofibrations C) (originalCompactComponentCell d kappaLP s b f hf) E b.profile.arrows
  let Q := (originalFiltrationEquivalence s).inverse
  let : Q.IsEquivalence := inferInstance
  let hQ : PreservesColimitsOfShape WalkingSpan Q := inferInstance
  let : PreservesColimit (span u f0) Q := hQ.preservesColimit
  let e := originalTransfiniteFiltrationBirthIso d kappaLP s b f hf p
  let u' := Q.map u ≫ e.inv.left
  let v' := Q.map v ≫ e.inv.right
  have hF' : IsCardinalPresentable (Q.obj F0) b.cardinal :=
    (isCardinalPresentable_iff_of_isEquivalence F0 b.cardinal Q).2 hF
  have hG' : IsCardinalPresentable (Q.obj G0) b.cardinal :=
    (isCardinalPresentable_iff_of_isEquivalence G0 b.cardinal Q).2 hG
  refine ⟨Q.obj F0, Q.obj G0, u', v', Q.map f0,
    (fun a => a0 (s.equivalence.functor.obj a)),
    (fun a => b0 (s.equivalence.functor.obj a)), ?_, ?_, ?_⟩
  · exact ⟨(fun a => hMem (s.equivalence.functor.obj a)), hF', hG'⟩
  · exact isPushoutOfArrowIso (hWhole.map Q) e
  · intro a
    refine ⟨(hCharts (s.equivalence.functor.obj a)).1, ?_, ?_⟩
    · change a0 (s.equivalence.functor.obj a) ≫
        (u.app (s.equivalence.functor.obj a) ≫ e.inv.left.app a) = _
      exact chartFactorPostcomposition _ _ _ _ (e.inv.left.app a)
        (hCharts (s.equivalence.functor.obj a)).2.1
    · change b0 (s.equivalence.functor.obj a) ≫
        (v.app (s.equivalence.functor.obj a) ≫ e.inv.right.app a) = _
      exact chartFactorPostcomposition _ _ _ _ (e.inv.right.app a)
        (hCharts (s.equivalence.functor.obj a)).2.2

/-- The extra initial isomorphism has an actual compact identity attaching arrow.
Its source is chosen from the original source approximation, without assuming
the original source diagram is presentable. -/
theorem originalCompactInitialAttachment :
    ∃ (F0 G0 : D ⥤ C)
      (u : F0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj ⊥)
      (v : G0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj
        (Order.succ ⊥)) (f0 : F0 ⟶ G0),
      compactCofibrationArrows D C b.cardinal (Arrow.mk f0) ∧
      IsPushout u f0
        ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map
          (homOfLE (Order.le_succ ⊥))) v := by
  let T := originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf
  let A := compactApproximation b.cardinal (T.F.obj ⊥)
  let : IsFiltered A.index := isFiltered_of_isCardinalFiltered A.index b.cardinal
  let : Nonempty A.index := IsFiltered.nonempty
  let i : A.index := Classical.arbitrary A.index
  let F0 := A.presentation.diag.obj i
  let u : F0 ⟶ T.F.obj ⊥ := A.presentation.ι.app i
  let q := T.F.map (homOfLE (Order.le_succ ⊥))
  let : IsIso q := originalTransfiniteFiltrationBotMapIsIso d kappaLP s b f hf
  refine ⟨F0, F0, u, u ≫ q, 𝟙 F0, ?_, ?_⟩
  · exact ⟨(fun a => (cofibrations C).id_mem (F0.obj a)), A.presentable i, A.presentable i⟩
  · exact IsPushout.of_vert_isIso ⟨by
      change u ≫ q = 𝟙 F0 ≫ (u ≫ q)
      rw [Category.id_comp]⟩

/-- Every original native successor is an actual compact whole-diagram attachment. -/
theorem originalCompactEverySuccessorAttachment
    (gamma : ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf))
    (hgamma : ¬IsMax gamma) :
    ∃ (F0 G0 : D ⥤ C)
      (u : F0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj gamma)
      (v : G0 ⟶ (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj
        (Order.succ gamma)) (f0 : F0 ⟶ G0),
      compactCofibrationArrows D C b.cardinal (Arrow.mk f0) ∧
      IsPushout u f0
        ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map
          (homOfLE (Order.le_succ gamma))) v := by
  rcases constructionIndex_cases gamma with rfl | rfl | ⟨p, rfl⟩
  · exact originalCompactInitialAttachment d kappaLP s b f hf
  · exact (hgamma isMax_top).elim
  · let := originalSliceComponentOrders d kappaLP s b f hf
    obtain ⟨F0, G0, u, v, f0, a0, b0, hMem, hPush, hCharts⟩ :=
      originalCompactSuccessorAttachment d kappaLP s b f hf p
    exact ⟨F0, G0, u, v, f0, hMem, hPush⟩

end HomotopicalAlgebra.FunctorInjective
