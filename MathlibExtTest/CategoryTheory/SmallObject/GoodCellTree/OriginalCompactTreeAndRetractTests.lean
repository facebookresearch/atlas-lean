/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.BoundedCellTreeCompactRetract
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalSplitFiltrationConstruction
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeCompactRootBaseChange

/-!
# Whole original compact-tree and retract clients

Every compact root, scalar chart and split filtration is constructed from the
original tree and original retract. The working, cell-label, coefficient-object
and coefficient-Hom universes stay independent. Original roots and endpoints
have no presentability premise, and the split-tree carrier has no total bound.
-/

set_option autoImplicit false
noncomputable section

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  CategoryTheory.MorphismProperty OriginalIdempotentLowerSupport
  OriginalIdempotentSupportHistory OriginalSplitFiltrationConstruction

namespace OriginalCompactTreeAndRetractTests

/-- The supplied working colimits give the actual finite coproducts at every w. -/
local instance workingBinaryCoproducts {C : Type u} [Category.{v} C]
    [HasColimitsOfSize.{w, w} C] : HasBinaryCoproducts C := by
  let _ : HasCoproducts.{w} C := inferInstance
  exact hasCoproductsOfShape_of_small.{w} C WalkingPair

/-- The same working colimits give the actual coefficient coequalizers. -/
local instance workingCoequalizers {C : Type u} [Category.{v} C]
    [HasColimitsOfSize.{w, w} C] : HasCoequalizers C :=
  hasColimitsOfShape_of_essentiallySmall.{w} WalkingParallelPair C

variable {C : Type u} [Category.{v} C] [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalAccessibleCategory C chi]
  {X : C} {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P))

section BoundedOriginalTree

variable (hP : HasCardinalLT P chi)
  (hSource : ∀ a : P, IsCardinalPresentable (s (T.label a)).left chi)
  (hTarget : ∀ a : P, IsCardinalPresentable (s (T.label a)).right chi)

private abbrev rootChart :=
  CompactRootBaseChange.compactRootPresentation chi T hP hSource hTarget

/-- All new compact points and goodness are outputs of the same literal-label constructor. -/
theorem allConstructedPointsCompact :
    let H := rootChart chi T hP hSource hTarget
    H.tree.label = T.label ∧ H.tree.IsGood chi ∧
      IsCardinalPresentable H.root chi ∧
      IsCardinalPresentable H.tree.endpointObj.right chi ∧
      (∀ a, IsCardinalPresentable (H.tree.vertex a).right chi) ∧
      (∀ a, IsCardinalPresentable (H.tree.predecessorObj a).right chi) ∧
      ∀ B, IsCardinalPresentable (H.lower.obj B).right chi := by
  let H := rootChart chi T hP hSource hTarget
  exact ⟨H.label_eq, H.good, H.root_presentable, H.endpoint_presentable,
    H.vertex_presentable, H.predecessor_presentable, H.lower_presentable⟩

/-- Both predecessor directions keep every original cofan leg and structural map. -/
theorem wholePredecessorComparisons (a : P) (b : LowerSet.Iio a) :
    let H := rootChart chi T hP hSource hTarget
    Nonempty (IsColimit (H.tree.predecessor a).cocone) ∧
    (Under.pushout H.rootMap).map ((H.tree.predecessor a).cocone.ι.app b) ≫
        (H.predecessorComparison a).hom =
      H.comparison.hom.app b.1 ≫ (T.predecessor a).cocone.ι.app b ∧
    (T.predecessor a).cocone.ι.app b ≫ (H.predecessorComparison a).inv =
      H.comparison.inv.app b.1 ≫
        (Under.pushout H.rootMap).map ((H.tree.predecessor a).cocone.ι.app b) ∧
    (Under.pushout H.rootMap).map (H.tree.predecessorMap a) ≫ H.comparison.hom.app a =
      (H.predecessorComparison a).hom ≫ T.predecessorMap a ∧
    T.predecessorMap a ≫ H.comparison.inv.app a =
      (H.predecessorComparison a).inv ≫ (Under.pushout H.rootMap).map (H.tree.predecessorMap a) := by
  let H := rootChart chi T hP hSource hTarget
  exact ⟨⟨(H.tree.predecessor a).isColimit⟩, H.predecessor_leg a b, H.predecessor_leg_inv a b,
    H.predecessor_map a, H.predecessor_map_inv a⟩

/-- The actual attaching and target-cell functions keep their dependent original labels. -/
theorem wholeOriginalCellFunctions :
    let H := rootChart chi T hP hSource hTarget
    (fun a : P => H.tree.attaching a ≫
      pushout.inl (H.tree.predecessorObj a).hom H.rootMap ≫
      (H.predecessorComparison a).hom.right) =
      (fun a : P => eqToHom (congrArg (fun l : alpha => (s l).left)
        (congrFun H.label_eq a)) ≫ T.attaching a) ∧
    (fun a : P => H.tree.cell a ≫ pushout.inl (H.tree.vertex a).hom H.rootMap ≫
      (H.comparison.hom.app a).right) =
      (fun a : P => eqToHom (congrArg (fun l : alpha => (s l).right)
        (congrFun H.label_eq a)) ≫ T.cell a) := by
  let H := rootChart chi T hP hSource hTarget
  exact ⟨H.attaching_function, H.cell_function⟩

/-- Every original chosen lower cocone is compared at all maps, in both directions. -/
theorem arbitraryChosenLowerMaps (L : LowerSetColimitData T.diagram)
    (B D : LowerSet P) (h : B ≤ D) :
    let H := rootChart chi T hP hSource hTarget
    Nonempty (IsColimit (H.lower.cocone B)) ∧
    (Under.pushout H.rootMap).map (H.lower.map h) ≫ (H.lowerComparison L).hom.app D =
      (H.lowerComparison L).hom.app B ≫ L.map h ∧
    L.map h ≫ (H.lowerComparison L).inv.app D =
      (H.lowerComparison L).inv.app B ≫ (Under.pushout H.rootMap).map (H.lower.map h) := by
  let H := rootChart chi T hP hSource hTarget
  exact ⟨⟨H.lower.isColimit B⟩, (H.lowerComparison L).hom.naturality (homOfLE h),
    (H.lowerComparison L).inv.naturality (homOfLE h)⟩

/-- Lower comparisons retain every original leg and both whole endpoint/predecessor Isos. -/
theorem wholeLowerCompatibility (L : LowerSetColimitData T.diagram) (B : LowerSet P)
    (a : B) (p : P) :
    let H := rootChart chi T hP hSource hTarget
    (Under.pushout H.rootMap).map (H.lower.ι B a) ≫ (H.lowerComparison L).hom.app B =
      H.comparison.hom.app a.1 ≫ L.ι B a ∧
    (Under.pushout H.rootMap).mapIso (H.tree.endpointIso H.lower) ≪≫ H.endpointComparison =
      (H.lowerComparison L).app ⊤ ≪≫ T.endpointIso L ∧
    (Under.pushout H.rootMap).mapIso (H.tree.predecessorIso H.lower p) ≪≫
        H.predecessorComparison p =
      (H.lowerComparison L).app (LowerSet.Iio p) ≪≫ T.predecessorIso L p := by
  let H := rootChart chi T hP hSource hTarget
  exact ⟨H.lower_leg L B a, H.lower_endpoint_iso L, H.lower_predecessor_iso L p⟩

/-- The whole original endpoint arrow, both root maps and both vertex legs are retained. -/
theorem sameOriginalEndpoint (a : P) :
    let H := rootChart chi T hP hSource hTarget
    IsPushout H.tree.hom H.rootMap
      (pushout.inl H.tree.hom H.rootMap ≫ H.endpointComparison.hom.right) T.hom ∧
    pushout.inr H.tree.hom H.rootMap ≫ H.endpointComparison.hom.right = T.hom ∧
    T.hom ≫ H.endpointComparison.inv.right = pushout.inr H.tree.hom H.rootMap ∧
    (Under.pushout H.rootMap).map (H.tree.inclusion a) ≫ H.endpointComparison.hom =
      H.comparison.hom.app a ≫ T.inclusion a ∧
    T.inclusion a ≫ H.endpointComparison.inv =
      H.comparison.inv.app a ≫ (Under.pushout H.rootMap).map (H.tree.inclusion a) ∧
    IsCardinalPresentable (Arrow.mk H.tree.hom) chi := by
  let H := rootChart chi T hP hSource hTarget
  exact ⟨H.endpoint_isPushout, Under.w H.endpointComparison.hom,
    Under.w H.endpointComparison.inv, H.endpoint_leg a, H.endpoint_leg_inv a,
    BoundedCellTreeCompactRetract.compactArrowPresentable chi T hP hSource hTarget⟩

/-- An arbitrary actual Arrow retract receives a scalar chart over its SAME original source.
The compact scalar's actual retract retains both whole squares and both splitting laws. -/
theorem actualArrowRetractChart {A B : C} {g : A ⟶ B} (R : RetractArrow g T.hom) :
    let H := rootChart chi T hP hSource hTarget
    ∃ (D' Z : C) (_ : IsCardinalPresentable D' chi) (_ : IsCardinalPresentable Z chi)
      (beta : H.root ⟶ D') (v' : D' ⟶ A)
      (_ : beta ≫ v' = H.rootMap ≫ R.r.left) (f' : D' ⟶ Z) (k : Z ⟶ B)
      (R' : RetractArrow f' (pushout.inl beta H.tree.hom)),
      IsPushout v' f' g k ∧ IsCardinalPresentable (Arrow.mk f') chi ∧
      R'.i.left ≫ pushout.inl beta H.tree.hom = f' ≫ R'.i.right ∧
      R'.r.left ≫ f' = pushout.inl beta H.tree.hom ≫ R'.r.right ∧
      R'.i.left ≫ R'.r.left = 𝟙 D' ∧ R'.i.right ≫ R'.r.right = 𝟙 Z := by
  obtain ⟨D', Z, hD, hZ, beta, v', hroot, f', k, R', hpush, harrow⟩ :=
    BoundedCellTreeCompactRetract.existsCompactPushout chi T hP hSource hTarget R
  refine ⟨D', Z, hD, hZ, beta, v', hroot, f', k, R', hpush, harrow, R'.i.w, R'.r.w, ?_, ?_⟩
  · exact congrArg (fun m : Arrow.mk f' ⟶ Arrow.mk f' => m.left) R'.retract
  · exact congrArg (fun m : Arrow.mk f' ⟶ Arrow.mk f' => m.right) R'.retract

end BoundedOriginalTree

section OriginalSplitFiltration

variable (L : LowerSetColimitData T.diagram) (hUncountable : Cardinal.aleph0 < chi)
  (good : T.IsGood chi) {Y : C} (f : X ⟶ Y) (R : RetractArrow f T.hom)
  (hsource : R.i.left = 𝟙 X)

private abbrev actualIdempotent :=
  arrowProjection T f R hsource ≫ arrowInclusion T f R hsource

omit [HasPushouts C] [HasColimitsOfSize.{w, w} C] in
private theorem actualIdempotent_idempotent :
    actualIdempotent T f R hsource ≫ actualIdempotent T f R hsource =
      actualIdempotent T f R hsource :=
  OriginalRetractSplitIso.idempotent_idempotent
    (arrowInclusion T f R hsource) (arrowProjection T f R hsource) (arrowSplit T f R hsource)

omit [HasPushouts C] in
/-- The actual retract builds its exhaustive BEFORE/AFTER history, including every limit.
Each literal AFTER-minus-BEFORE difference is bounded at the original chi. -/
theorem exhaustiveOriginalSupports :
    letI := T.wellFoundedLT
    let q := actualIdempotent T f R hsource
    let hq := actualIdempotent_idempotent T f R hsource
    (⨆ p, (after T L q hq chi hUncountable good p).support) = ⊤ ∧
    ∀ p : HistoryIndex (P := P),
      (before T L q hq chi hUncountable good p).support =
        ⨆ j : Set.Iio p, (after T L q hq chi hUncountable good j.1).support ∧
      HasCardinalLT (((after T L q hq chi hUncountable good p).support : Set P) \
        ((before T L q hq chi hUncountable good p).support : Set P) : Set P) chi ∧
      (differenceTree T L q hq chi hUncountable good p).hom =
        (L.map (beforeToAfter T L q hq chi hUncountable good p).le).right := by
  let _ := T.wellFoundedLT
  let q := actualIdempotent T f R hsource
  let hq := actualIdempotent_idempotent T f R hsource
  refine ⟨exhausts T L q hq chi hUncountable good, fun p => ?_⟩
  exact ⟨before_union T L q hq chi hUncountable good p,
    birth_difference_bounded T L q hq chi hUncountable good p,
    differenceTree_hom T L q hq chi hUncountable good p⟩

omit [HasPushouts C] in
/-- Both genuine BEFORE colimits and all split-map covariance are constructed internally. -/
theorem originalBeforeUPsAndNaturalSplitting :
    letI := T.wellFoundedLT
    let q := actualIdempotent T f R hsource
    let hq := actualIdempotent_idempotent T f R hsource
    (∀ p : HistoryIndex (P := P),
      Nonempty (IsColimit (beforeTargetCocone T L q hq chi hUncountable good p)) ∧
      Nonempty (IsColimit (beforeSourceCocone T L q hq chi hUncountable good p))) ∧
    splitInclusion T L q hq chi hUncountable good ≫
      splitProjection T L q hq chi hUncountable good =
        𝟙 (splitAfter T L q hq chi hUncountable good) ∧
    splitProjection T L q hq chi hUncountable good ≫
      splitInclusion T L q hq chi hUncountable good =
        diagramIdempotent (afterStateFunctor T L q hq chi hUncountable good) := by
  let _ := T.wellFoundedLT
  let q := actualIdempotent T f R hsource
  let hq := actualIdempotent_idempotent T f R hsource
  exact ⟨fun p => ⟨⟨beforeTargetIsColimit T L q hq chi hUncountable good p⟩,
    ⟨beforeSourceIsColimit T L q hq chi hUncountable good p⟩⟩,
    splitInclusion_projection T L q hq chi hUncountable good,
    splitProjection_inclusion T L q hq chi hUncountable good⟩

/-- Every chosen birth has genuinely compact ends/Arrow, its original root equation,
and the actual scalar pushout for the original BEFORE-to-AFTER split map. -/
theorem actualCompactBirthSquares :
    letI := T.wellFoundedLT
    let q := actualIdempotent T f R hsource
    let hq := actualIdempotent_idempotent T f R hsource
    ∀ p : HistoryIndex (P := P),
      let B := birthChart T L q hq chi hUncountable good p
      IsCardinalPresentable B.cell.left chi ∧ IsCardinalPresentable B.cell.right chi ∧
      IsCardinalPresentable B.cell chi ∧
      B.beta ≫ B.attaching = (compactBirthData T L q hq chi hUncountable good p).rootMap ≫
        (State.projection (before T L q hq chi hUncountable good p)).right ∧
      IsPushout B.attaching B.cell.hom
        (State.splitMap (beforeToAfter T L q hq chi hUncountable good p)).right B.cellMap ∧
      B.scalarRetract.i.left ≫
          pushout.inl B.beta (compactBirthData T L q hq chi hUncountable good p).tree.hom =
        B.cell.hom ≫ B.scalarRetract.i.right ∧
      B.scalarRetract.r.left ≫ B.cell.hom =
        pushout.inl B.beta (compactBirthData T L q hq chi hUncountable good p).tree.hom ≫
          B.scalarRetract.r.right ∧
      B.scalarRetract.i.left ≫ B.scalarRetract.r.left = 𝟙 B.cell.left ∧
      B.scalarRetract.i.right ≫ B.scalarRetract.r.right = 𝟙 B.cell.right := by
  let _ := T.wellFoundedLT
  let q := actualIdempotent T f R hsource
  let hq := actualIdempotent_idempotent T f R hsource
  dsimp only
  intro p
  let B := birthChart T L q hq chi hUncountable good p
  refine ⟨B.presentable_source, B.presentable_target, B.presentable_arrow, B.rootSquare,
    B.pushout, B.scalarRetract.i.w, B.scalarRetract.r.w, ?_, ?_⟩
  · exact congrArg (fun m : B.cell ⟶ B.cell => m.left) B.scalarRetract.retract
  · exact congrArg (fun m : B.cell ⟶ B.cell => m.right) B.scalarRetract.retract

omit [HasPushouts C] in
/-- The actual source and full two-map splitting cocones recover the original endpoint.
Neither component colimit nor an endpoint comparison is supplied as an outcome. -/
theorem originalEndpointUPs :
    letI := T.wellFoundedLT
    let i := arrowInclusion T f R hsource
    let r := arrowProjection T f R hsource
    let hir := arrowSplit T f R hsource
    Nonempty (IsColimit (originalSourceCocone T L chi hUncountable good i r hir)) ∧
      Nonempty (IsColimit (originalSplittingCocone T L chi hUncountable good i r hir)) := by
  let _ := T.wellFoundedLT
  exact ⟨⟨originalSourceIsColimit T L chi hUncountable good
      (arrowInclusion T f R hsource) (arrowProjection T f R hsource) (arrowSplit T f R hsource)⟩,
    ⟨originalSplittingIsColimit T L chi hUncountable good
      (arrowInclusion T f R hsource) (arrowProjection T f R hsource) (arrowSplit T f R hsource)⟩⟩

/-- The returned endpoint is literally the original f, with its original inclusion/projection. -/
theorem actualOriginalEndpointMaps :
    letI := T.wellFoundedLT
    R.r.left = 𝟙 X ∧ f ≫ R.i.right = T.hom ∧ T.hom ≫ R.r.right = f ∧
    (fromOriginalArrow T L chi hUncountable good f R hsource).hom = f ∧
    (IdempotentCoequalizerSplit.projection (actualIdempotent T f R hsource)).right ≫
      (fromOriginalArrowEndpointIso T f R hsource).hom.right = R.r.right ∧
    (fromOriginalArrowEndpointIso T f R hsource).inv.right =
      R.i.right ≫ (IdempotentCoequalizerSplit.projection
        (actualIdempotent T f R hsource)).right ∧
    (IdempotentCoequalizerSplit.obj (actualIdempotent T f R hsource)).hom ≫
      (fromOriginalArrowEndpointIso T f R hsource).hom.right = f := by
  let _ := T.wellFoundedLT
  exact ⟨originalProjection_source T f R hsource,
    Under.w (arrowInclusion T f R hsource), Under.w (arrowProjection T f R hsource),
    fromOriginalArrow_hom T L chi hUncountable good f R hsource,
    fromOriginalArrow_endpointProjection T f R hsource,
    fromOriginalArrow_endpointInverse T f R hsource,
    fromOriginalArrow_endpointRoot T f R hsource⟩

/-- Empty original labels still recover the actual original target under an arbitrary root. -/
theorem emptyOriginalFiltration [IsEmpty P] :
    letI := T.wellFoundedLT
    IsEmpty (HistoryIndex (P := P)) ∧
      (fromOriginalArrow T L chi hUncountable good f R hsource).endpointObj = Under.mk f ∧
      (fromOriginalArrow T L chi hUncountable good f R hsource).hom = f := by
  let _ := T.wellFoundedLT
  refine ⟨⟨fun p => isEmptyElim (OriginalCellWellOrderEnumeration.labels.symm p)⟩, rfl, rfl⟩

variable (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
  [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W] [W.IsStableUnderRetracts]
  (hs : ∀ a : P, W (s (T.label a)).hom)

include hs in
/-- Original cell membership proves membership of every ACTUALLY chosen compact scalar birth. -/
theorem actualBirthsInOriginalClass :
    letI := T.wellFoundedLT
    ∀ p : HistoryIndex (P := P),
      W (compactCells T L (actualIdempotent T f R hsource)
        (actualIdempotent_idempotent T f R hsource) chi hUncountable good p).hom := by
  let _ := T.wellFoundedLT
  exact fromOriginalArrow_cells_mem T L chi hUncountable good f R hsource W hs

include T L chi hUncountable good R hsource hs in
/-- The actual compact-cell filtration proves membership of the SAME whole original f. -/
theorem wholeOriginalArrowInClass : W f := by
  let _ := T.wellFoundedLT
  have h := fromOriginalArrow_mem T L chi hUncountable good f R hsource W hs
  rwa [fromOriginalArrow_hom T L chi hUncountable good f R hsource] at h

end OriginalSplitFiltration

section ConcreteOriginalBoundary

attribute [local instance] Cardinal.fact_isRegular_aleph0

example : ¬ IsCardinalPresentable ℕ Cardinal.aleph0.{0} :=
  CompactRootBaseChangeExamples.originalRoot_noncompact

example : ¬ Mono GoodCellTreeDataExamples.quotientTree.{t}.hom :=
  CompactRootBaseChangeExamples.originalEndpoint_nonmono.{t}

end ConcreteOriginalBoundary

end OriginalCompactTreeAndRetractTests
