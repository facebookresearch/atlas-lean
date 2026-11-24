/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tsutomu Okano, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalIdempotentHistoryConstruction
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalSplitFiltrationEndpoint
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.BoundedDifferenceSplitChart
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Actual original retract split filtrations

The original support history constructs the actual canonical split objects,
all their maps, every predecessor colimit and the original endpoint cocone.
The original bounded difference producer constructs the compact birth charts.
These data construct the whole birth cell tree under the original source.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalSplitFiltrationConstruction

open CategoryTheory.Limits OriginalIdempotentLowerSupport
  OriginalIdempotentSupportHistory CoherentRetracts

variable {C : Type u} [Category.{v} C] {X : C}
  {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (q : T.endpointObj ⟶ T.endpointObj) [HasCoequalizers (Under X)]

section OriginalArrowMaps

omit [HasCoequalizers (Under X)]

variable {Y : C} (f : X ⟶ Y) (R : RetractArrow f T.hom)

/-- The actual original source retract equation proves the projection's source is fixed too. -/
theorem originalProjection_source (hsource : R.i.left = 𝟙 X) : R.r.left = 𝟙 X := by
  have h := congrArg (fun k : Arrow.mk f ⟶ Arrow.mk f => k.left) R.retract
  change R.i.left ≫ R.r.left = 𝟙 X at h
  rw [hsource] at h
  exact (Category.id_comp R.r.left).symm.trans h

/-- The actual original Arrow inclusion square constructs its map under the same source X. -/
abbrev arrowInclusion (hsource : R.i.left = 𝟙 X) : Under.mk f ⟶ T.endpointObj :=
  Under.homMk R.i.right (by
    have h := R.i.w
    change R.i.left ≫ T.hom = f ≫ R.i.right at h
    rw [hsource] at h
    exact ((Category.id_comp T.hom).symm.trans h).symm)

/-- The actual original Arrow projection square constructs its map under the same source X. -/
abbrev arrowProjection (hsource : R.i.left = 𝟙 X) : T.endpointObj ⟶ Under.mk f :=
  Under.homMk R.r.right (by
    have h := R.r.w
    change R.r.left ≫ f = T.hom ≫ R.r.right at h
    rw [originalProjection_source T f R hsource] at h
    exact ((Category.id_comp f).symm.trans h).symm)

/-- Both actual original Arrow target maps retain their original splitting equation. -/
theorem arrowSplit (hsource : R.i.left = 𝟙 X) : arrowInclusion T f R hsource ≫
    arrowProjection T f R hsource = 𝟙 (Under.mk f) := by
  apply Under.UnderMorphism.ext
  exact congrArg (fun k : Arrow.mk f ⟶ Arrow.mk f => k.right) R.retract

end OriginalArrowMaps

/-- The actual canonical split map is expressed in the original inclusion and projection. -/
theorem splitMap_formula {A B : State T L q} (h : State.Inclusion A B) :
    State.splitMap h = State.inclusion A ≫ L.map h.le ≫ State.projection B := by
  calc
    State.splitMap h = (State.inclusion A ≫ State.projection A) ≫ State.splitMap h := by
      rw [State.inclusion_projection, Category.id_comp]
    _ = _ := by rw [Category.assoc, State.projection_splitMap]

/-- The original identity induces the identity on its selected split image. -/
theorem splitMap_identity (A : State T L q) :
    State.splitMap (State.Inclusion.identity A) = 𝟙 (State.splitObj A) := by
  apply IdempotentCoequalizerSplit.hom_ext A.e
  rw [State.projection_splitMap, L.map_id, Category.id_comp, Category.comp_id]

/-- All canonical split maps retain the actual composition of original lower inclusions. -/
theorem splitMap_comp {A B D : State T L q}
    (h : State.Inclusion A B) (k : State.Inclusion B D) :
    State.splitMap (State.Inclusion.comp h k) = State.splitMap h ≫ State.splitMap k := by
  apply IdempotentCoequalizerSplit.hom_ext A.e
  rw [State.projection_splitMap, ← Category.assoc, State.projection_splitMap,
    Category.assoc, State.projection_splitMap, ← Category.assoc, L.map_comp]

/-- Each original lower state has its actual chosen splitting under the original source. -/
abbrev stateSplit (A : State T L q) : SplitObject (Under X) where
  source := State.splitObj A
  target := L.obj A.support
  inclusion := State.inclusion A
  retraction := State.projection A
  splitting := State.inclusion_projection A

/-- The full two-square splitting functor is constructed from the original state inclusions. -/
abbrev stateSplitFunctor : State T L q ⥤ SplitObject (Under X) where
  obj A := stateSplit T L q A
  map {A B} f :=
    { left := State.splitMap (f : State.Inclusion A B)
      right := L.map (State.Inclusion.le f)
      inclusion_naturality := (State.splitMap_inclusion f).symm
      retraction_naturality := State.projection_splitMap f }
  map_id A := by
    apply SplitObject.Hom.ext
    · exact splitMap_identity T L q A
    · exact L.map_id A.support
  map_comp f g := by
    apply SplitObject.Hom.ext
    · exact splitMap_comp T L q f g
    · exact (L.map_comp (State.Inclusion.le f) (State.Inclusion.le g)).symm

section HistoryDiagrams

variable [WellFoundedLT P] [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hq : q ≫ q = q) (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)

/-- All actual AFTER split objects and both original component maps. -/
abbrev splitAfterDiagram : HistoryIndex (P := P) ⥤ SplitObject (Under X) :=
  afterStateFunctor T L q hq chi hUncountable good ⋙ stateSplitFunctor T L q

/-- The actual canonical split-source diagram under the original X. -/
abbrev splitAfter : HistoryIndex (P := P) ⥤ Under X :=
  splitAfterDiagram T L q hq chi hUncountable good ⋙ SplitObject.sourceFunctor

/-- The complete inclusion transformation retains the original selected split maps. -/
abbrev splitInclusion :=
  SplitObject.inclusionNatTrans (splitAfterDiagram T L q hq chi hUncountable good)

/-- The complete projection transformation retains the original selected split maps. -/
abbrev splitProjection :=
  SplitObject.retractionNatTrans (splitAfterDiagram T L q hq chi hUncountable good)

/-- The source splitting law holds throughout the actual constructed diagram. -/
theorem splitInclusion_projection :
    splitInclusion T L q hq chi hUncountable good ≫
      splitProjection T L q hq chi hUncountable good =
        𝟙 (splitAfter T L q hq chi hUncountable good) :=
  SplitObject.inclusion_retraction _

/-- The target splitting law is exactly the original lower idempotent transformation. -/
theorem splitProjection_inclusion :
    splitProjection T L q hq chi hUncountable good ≫
      splitInclusion T L q hq chi hUncountable good =
        diagramIdempotent (afterStateFunctor T L q hq chi hUncountable good) := by
  apply NatTrans.ext
  funext p
  exact State.projection_inclusion (after T L q hq chi hUncountable good p)

/-- The actual earlier AFTER state functor at a birth. -/
abbrev belowStateFunctor (p : HistoryIndex (P := P)) : Set.Iio p ⥤ State T L q :=
  familyFunctor T L q (fun j => after T L q hq chi hUncountable good j.1)
    (historyBelowCompatible T L q hq chi hUncountable good p)

/-- The full original splitting diagram below this label, retaining both original maps. -/
abbrev belowSplitDiagram (p : HistoryIndex (P := P)) : Set.Iio p ⥤ SplitObject (Under X) :=
  belowStateFunctor T L q hq chi hUncountable good p ⋙ stateSplitFunctor T L q

/-- The actual original BEFORE target cocone, at its same selected original lower object. -/
abbrev beforeTargetCocone (p : HistoryIndex (P := P)) :
    Cocone (belowSplitDiagram T L q hq chi hUncountable good p ⋙ SplitObject.targetFunctor) :=
  beforeCocone T L q hq chi hUncountable good p

/-- The constructed original support history supplies the actual BEFORE target UP. -/
def beforeTargetIsColimit (p : HistoryIndex (P := P)) :
    IsColimit (beforeTargetCocone T L q hq chi hUncountable good p) :=
  beforeIsColimit T L q hq chi hUncountable good p

/-- The actual original lower-inclusion square supplies the full endpoint idempotent equation. -/
theorem beforeEndpointCompatibility (p : HistoryIndex (P := P)) (j : Set.Iio p) :
    (beforeTargetCocone T L q hq chi hUncountable good p).ι.app j ≫
        State.projection (before T L q hq chi hUncountable good p) ≫
        State.inclusion (before T L q hq chi hUncountable good p) =
      ((belowSplitDiagram T L q hq chi hUncountable good p).obj j).retraction ≫
        ((belowSplitDiagram T L q hq chi hUncountable good p).obj j).inclusion ≫
        (beforeTargetCocone T L q hq chi hUncountable good p).ι.app j := by
  change L.map (earlierToBefore T L q hq chi hUncountable good j.1 p j.2).le ≫
      State.projection (before T L q hq chi hUncountable good p) ≫
      State.inclusion (before T L q hq chi hUncountable good p) =
    State.projection (after T L q hq chi hUncountable good j.1) ≫
      State.inclusion (after T L q hq chi hUncountable good j.1) ≫
      L.map (earlierToBefore T L q hq chi hUncountable good j.1 p j.2).le
  rw [State.projection_inclusion, ← Category.assoc, State.projection_inclusion]
  exact (earlierToBefore T L q hq chi hUncountable good j.1 p j.2).commutes.symm

/-- The actual BEFORE split-source cocone is constructed from the original target cocone. -/
abbrev beforeSourceCocone (p : HistoryIndex (P := P)) :=
  OriginalSplitFiltrationEndpoint.sourceCocone
    (belowSplitDiagram T L q hq chi hUncountable good p)
    (beforeTargetCocone T L q hq chi hUncountable good p)
    (State.projection (before T L q hq chi hUncountable good p))

/-- The genuine original target UP constructs the BEFORE source UP, including at all limits. -/
def beforeSourceIsColimit (p : HistoryIndex (P := P)) :
    IsColimit (beforeSourceCocone T L q hq chi hUncountable good p) :=
  OriginalSplitFiltrationEndpoint.sourceIsColimit _ _
    (State.inclusion (before T L q hq chi hUncountable good p))
    (State.projection (before T L q hq chi hUncountable good p))
    (State.inclusion_projection _) (beforeEndpointCompatibility T L q hq chi hUncountable good p)
    (beforeTargetIsColimit T L q hq chi hUncountable good p)

/-- Every actual predecessor source leg is the same original canonical split inclusion map. -/
theorem beforeSourceLeg (p : HistoryIndex (P := P)) (j : Set.Iio p) :
    (beforeSourceCocone T L q hq chi hUncountable good p).ι.app j =
      State.splitMap (earlierToBefore T L q hq chi hUncountable good j.1 p j.2) :=
  (splitMap_formula T L q _).symm

/-- The whole target cocone retains the actual original endpoint and original lower legs. -/
abbrev afterTargetCocone :
    Cocone (splitAfterDiagram T L q hq chi hUncountable good ⋙ SplitObject.targetFunctor) where
  pt := T.endpointObj
  ι :=
    { app p := endpointLeg T L (after T L q hq chi hUncountable good p).support
      naturality a b h := by
        change L.map
            (State.Inclusion.le ((afterStateFunctor T L q hq chi hUncountable good).map h)) ≫
            endpointLeg T L (after T L q hq chi hUncountable good b).support =
          endpointLeg T L (after T L q hq chi hUncountable good a).support ≫ 𝟙 _
        rw [map_endpointLeg, Category.comp_id] }

/-- Exhaustion and the original whole-tree UP prove the actual original target cocone
is colimiting. -/
def afterTargetIsColimit : IsColimit (afterTargetCocone T L q hq chi hUncountable good) := by
  refine IsColimit.ofIsoColimit
    (familyIsColimit T L q (after T L q hq chi hUncountable good)
      (historyCompatible T L q hq chi hUncountable good))
    (Cocone.ext
      ((L.functor.mapIso (eqToIso (exhausts T L q hq chi hUncountable good))) ≪≫
        T.endpointIso L) ?_)
  intro a
  change L.map (le_iSup (fun p => (after T L q hq chi hUncountable good p).support) a) ≫
      (L.map (leOfHom (eqToHom (exhausts T L q hq chi hUncountable good))) ≫
        (T.endpointIso L).hom) = _
  rw [← Category.assoc, L.map_comp]

/-- The chosen predecessor consists of the actual split BEFORE object and its constructed UP. -/
abbrev splitPredecessor (p : HistoryIndex (P := P)) :
    ColimitCocone (LowerSetColimits.restriction
      (splitAfter T L q hq chi hUncountable good) (LowerSet.Iio p)) where
  cocone := beforeSourceCocone T L q hq chi hUncountable good p
  isColimit := beforeSourceIsColimit T L q hq chi hUncountable good p

/-- The predecessor-to-vertex map is exactly the original BEFORE-to-AFTER split map. -/
theorem splitPredecessorMap (p : HistoryIndex (P := P)) :
    cellTreePredecessorMap (splitAfter T L q hq chi hUncountable good) p
        (splitPredecessor T L q hq chi hUncountable good p) =
      State.splitMap (beforeToAfter T L q hq chi hUncountable good p) := by
  apply (splitPredecessor T L q hq chi hUncountable good p).isColimit.hom_ext
  intro j
  rw [cellTreePredecessorMap_fac]
  change State.splitMap ((afterStateFunctor T L q hq chi hUncountable good).map
      (homOfLE j.2.le)) =
    (beforeSourceCocone T L q hq chi hUncountable good p).ι.app j ≫
      State.splitMap (beforeToAfter T L q hq chi hUncountable good p)
  rw [beforeSourceLeg, ← splitMap_comp]

end HistoryDiagrams

section CompactBirths

variable [WellFoundedLT P] [HasBinaryCoproducts C]
  (hq : q ≫ q = q) (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)
  [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  [IsCardinalAccessibleCategory C chi]

/-- The compact approximation belongs to the actual original bounded birth difference. -/
abbrev compactBirthData (p : HistoryIndex (P := P)) :=
  BoundedDifferenceSplitChart.compactDifferenceForInclusion T L
    (before T L q hq chi hUncountable good p) (after T L q hq chi hUncountable good p)
    (beforeToAfter T L q hq chi hUncountable good p) chi good
    (birth_difference_bounded T L q hq chi hUncountable good p)

/-- A local compact birth chart retains its original coefficient root and original split step. -/
structure BirthChart (p : HistoryIndex (P := P)) where
  /-- The compact scalar arrow for the original split birth. -/
  cell : Arrow C
  presentable_source : IsCardinalPresentable cell.left chi
  presentable_target : IsCardinalPresentable cell.right chi
  presentable_arrow : IsCardinalPresentable cell chi
  /-- The map from the chosen compact root to the scalar source. -/
  beta : (compactBirthData T L q hq chi hUncountable good p).root ⟶ cell.left
  /-- The scalar source map into the original BEFORE split image. -/
  attaching : cell.left ⟶ (State.splitObj (before T L q hq chi hUncountable good p)).right
  /-- The scalar target map into the original AFTER split image. -/
  cellMap : cell.right ⟶ (State.splitObj (after T L q hq chi hUncountable good p)).right
  rootSquare : beta ≫ attaching =
    (compactBirthData T L q hq chi hUncountable good p).rootMap ≫
      (State.projection (before T L q hq chi hUncountable good p)).right
  /-- The scalar arrow's retract into the compact difference tree after root base change. -/
  scalarRetract : RetractArrow cell.hom
    (pushout.inl beta (compactBirthData T L q hq chi hUncountable good p).tree.hom)
  pushout : IsPushout attaching cell.hom
    (State.splitMap (beforeToAfter T L q hq chi hUncountable good p)).right cellMap

/-- The actual bounded-difference compact producer constructs every full local birth chart. -/
theorem existsBirthChart (p : HistoryIndex (P := P)) :
    Nonempty (BirthChart T L q hq chi hUncountable good p) := by
  obtain ⟨A, Z, hA, hZ, beta, a, hroot, f, b, hR, hpushout, harrow⟩ :=
    BoundedDifferenceSplitChart.existsCompactPushoutForInclusion T L
      (before T L q hq chi hUncountable good p) (after T L q hq chi hUncountable good p)
      (beforeToAfter T L q hq chi hUncountable good p) chi good
      (birth_difference_bounded T L q hq chi hUncountable good p)
  exact ⟨
    { cell := Arrow.mk f
      presentable_source := hA
      presentable_target := hZ
      presentable_arrow := harrow
      beta := beta
      attaching := a
      cellMap := b
      rootSquare := hroot
      scalarRetract := hR
      pushout := hpushout }⟩

/-- The selected local birth chart is constructed from the actual original difference geometry. -/
def birthChart (p : HistoryIndex (P := P)) : BirthChart T L q hq chi hUncountable good p :=
  Classical.choice (existsBirthChart T L q hq chi hUncountable good p)

/-- The actual compact generating arrows of the constructed birth tree. -/
abbrev compactCells (p : HistoryIndex (P := P)) : Arrow C :=
  (birthChart T L q hq chi hUncountable good p).cell

/-- Every actually chosen compact birth scalar belongs to the original class,
proved from its original scalar retract and the actual original cell closures. -/
theorem compactCells_mem (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W] [W.IsStableUnderRetracts]
    (hs : ∀ a : P, W (s (T.label a)).hom) (p : HistoryIndex (P := P)) :
    W (compactCells T L q hq chi hUncountable good p).hom :=
  BoundedDifferenceSplitChart.scalar_memForInclusion T L
    (before T L q hq chi hUncountable good p) (after T L q hq chi hUncountable good p)
    (beforeToAfter T L q hq chi hUncountable good p) chi good
    (birth_difference_bounded T L q hq chi hUncountable good p) W hs
    (birthChart T L q hq chi hUncountable good p).beta
    (compactCells T L q hq chi hUncountable good p).hom
    (birthChart T L q hq chi hUncountable good p).scalarRetract

end CompactBirths

section OriginalEndpoint

variable [WellFoundedLT P] [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)
  {Y : Under X} (i : Y ⟶ T.endpointObj) (r : T.endpointObj ⟶ Y)
  (hir : i ≫ r = 𝟙 Y)

/-- The actual original inclusion and projection determine the whole split diagram's idempotent. -/
abbrev originalSplits :=
  splitAfterDiagram T L (r ≫ i)
    (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good

/-- The target cocone is still at the actual original tree endpoint. -/
abbrev originalTargetCocone :=
  afterTargetCocone T L (r ≫ i)
    (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good

/-- The original endpoint split equation is exactly the recursively constructed stage equation. -/
theorem originalEndpointCompatibility (p : HistoryIndex (P := P)) :
    (originalTargetCocone T L chi hUncountable good i r hir).ι.app p ≫ r ≫ i =
      ((originalSplits T L chi hUncountable good i r hir).obj p).retraction ≫
        ((originalSplits T L chi hUncountable good i r hir).obj p).inclusion ≫
        (originalTargetCocone T L chi hUncountable good i r hir).ι.app p := by
  change endpointLeg T L (after T L (r ≫ i)
        (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p).support ≫
      r ≫ i =
    State.projection (after T L (r ≫ i)
        (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p) ≫
      State.inclusion (after T L (r ≫ i)
        (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p) ≫
      endpointLeg T L (after T L (r ≫ i)
        (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p).support
  let A := after T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
    chi hUncountable good p
  change endpointLeg T L A.support ≫ r ≫ i =
    State.projection A ≫ State.inclusion A ≫ endpointLeg T L A.support
  rw [← Category.assoc (State.projection A) (State.inclusion A)
    (endpointLeg T L A.support), State.projection_inclusion]
  exact A.endpoint.symm

/-- The actual original retract endpoint Y is the constructed whole split-source cocone point. -/
abbrev originalSourceCocone :=
  OriginalSplitFiltrationEndpoint.sourceCocone
    (originalSplits T L chi hUncountable good i r hir)
    (originalTargetCocone T L chi hUncountable good i r hir) r

/-- The original target UP and original i/r construct the source UP at the actual original Y. -/
def originalSourceIsColimit :
    IsColimit (originalSourceCocone T L chi hUncountable good i r hir) :=
  OriginalSplitFiltrationEndpoint.sourceIsColimit _ _ i r hir
    (originalEndpointCompatibility T L chi hUncountable good i r hir)
    (afterTargetIsColimit T L (r ≫ i)
      (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good)

/-- Both actual original endpoint objects, original maps and all leg squares form
the full cocone. -/
abbrev originalSplittingCocone :=
  OriginalSplitFiltrationEndpoint.splittingCocone
    (originalSplits T L chi hUncountable good i r hir)
    (originalTargetCocone T L chi hUncountable good i r hir) i r hir
    (originalEndpointCompatibility T L chi hUncountable good i r hir)

/-- The full original splitting cocone is colimiting, with neither component UP assumed. -/
def originalSplittingIsColimit :
    IsColimit (originalSplittingCocone T L chi hUncountable good i r hir) :=
  OriginalSplitFiltrationEndpoint.splittingIsColimit _ _ i r hir
    (originalEndpointCompatibility T L chi hUncountable good i r hir)
    (afterTargetIsColimit T L (r ≫ i)
      (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good)

/-- Every actual source cocone leg retains its original inclusion square. -/
theorem originalSourceLeg_inclusion (p : HistoryIndex (P := P)) :
    (originalSourceCocone T L chi hUncountable good i r hir).ι.app p ≫ i =
      ((originalSplits T L chi hUncountable good i r hir).obj p).inclusion ≫
        (originalTargetCocone T L chi hUncountable good i r hir).ι.app p :=
  OriginalSplitFiltrationEndpoint.sourceLeg_inclusion
    (originalSplits T L chi hUncountable good i r hir)
    (originalTargetCocone T L chi hUncountable good i r hir) i r
    (originalEndpointCompatibility T L chi hUncountable good i r hir) p

/-- Every actual target cocone leg retains its original projection square. -/
theorem originalTargetLeg_projection (p : HistoryIndex (P := P)) :
    (originalTargetCocone T L chi hUncountable good i r hir).ι.app p ≫ r =
      ((originalSplits T L chi hUncountable good i r hir).obj p).retraction ≫
        (originalSourceCocone T L chi hUncountable good i r hir).ι.app p :=
  OriginalSplitFiltrationEndpoint.targetLeg_retraction
    (originalSplits T L chi hUncountable good i r hir)
    (originalTargetCocone T L chi hUncountable good i r hir) i r hir
    (originalEndpointCompatibility T L chi hUncountable good i r hir) p

omit [WellFoundedLT P] [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- The internally chosen whole idempotent split is compared to Y using the same original i/r. -/
abbrev originalEndpointIso : IdempotentCoequalizerSplit.obj (r ≫ i) ≅ Y :=
  OriginalRetractSplitIso.iso i r hir

omit [WellFoundedLT P] [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- The full original projection is recovered by the actual forward endpoint comparison. -/
theorem originalEndpointIso_projection :
    IdempotentCoequalizerSplit.projection (r ≫ i) ≫
      (originalEndpointIso T i r hir).hom = r :=
  OriginalRetractSplitIso.projection_iso_hom i r hir

omit [WellFoundedLT P] [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- The inverse endpoint comparison retains the actual original inclusion and chosen projection. -/
theorem originalEndpointIso_inverse :
    (originalEndpointIso T i r hir).inv =
      i ≫ IdempotentCoequalizerSplit.projection (r ≫ i) := rfl

end OriginalEndpoint

section OriginalCellTree

variable [WellFoundedLT P] [HasBinaryCoproducts C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)
  [HasPushouts C] [HasColimitsOfSize.{w, w} C] [IsCardinalAccessibleCategory C chi]
  {Y : Under X} (i : Y ⟶ T.endpointObj) (r : T.endpointObj ⟶ Y)
  (hir : i ≫ r = 𝟙 Y)

/-- The actual split birth tree uses its genuine BEFORE predecessor at every label,
and its whole endpoint is the original retract Y under the same original X. -/
def originalSplitTree : CellTree
    (compactCells T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
      chi hUncountable good) X (P := HistoryIndex (P := P)) where
  wellFounded := OriginalCellWellOrderEnumeration.enumeration_wellFounded
  diagram := splitAfter T L (r ≫ i)
    (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good
  label p := p
  predecessor p := splitPredecessor T L (r ≫ i)
    (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p
  attaching p := (birthChart T L (r ≫ i)
    (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p).attaching
  cell p := (birthChart T L (r ≫ i)
    (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p).cellMap
  isPushout p := by
    rw [splitPredecessorMap]
    exact (birthChart T L (r ≫ i)
      (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p).pushout
  endpoint :=
    { cocone := originalSourceCocone T L chi hUncountable good i r hir
      isColimit := originalSourceIsColimit T L chi hUncountable good i r hir }

/-- The constructed split tree recovers the actual original arrow out of X. -/
theorem originalSplitTree_hom :
    (originalSplitTree T L chi hUncountable good i r hir).hom = Y.hom := rfl

/-- Every original AFTER split image remains the actual vertex under X. -/
theorem originalSplitTree_vertex (p : HistoryIndex (P := P)) :
    (originalSplitTree T L chi hUncountable good i r hir).vertex p =
      State.splitObj (after T L (r ≫ i)
        (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p) := rfl

/-- Every original BEFORE split image remains the actual predecessor under X. -/
theorem originalSplitTree_predecessorObj (p : HistoryIndex (P := P)) :
    (originalSplitTree T L chi hUncountable good i r hir).predecessorObj p =
      State.splitObj (before T L (r ≫ i)
        (OriginalRetractSplitIso.idempotent_idempotent i r hir) chi hUncountable good p) := rfl

/-- Each actual birth cell source is chi-presentable. -/
theorem originalSplitTree_cell_source_presentable (p : HistoryIndex (P := P)) :
    IsCardinalPresentable
      (compactCells T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
        chi hUncountable good p).left chi :=
  (birthChart T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
    chi hUncountable good p).presentable_source

/-- Each actual birth cell target is chi-presentable. -/
theorem originalSplitTree_cell_target_presentable (p : HistoryIndex (P := P)) :
    IsCardinalPresentable
      (compactCells T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
        chi hUncountable good p).right chi :=
  (birthChart T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
    chi hUncountable good p).presentable_target

/-- Each actual birth arrow is chi-presentable in the genuine Arrow category. -/
theorem originalSplitTree_cell_arrow_presentable (p : HistoryIndex (P := P)) :
    IsCardinalPresentable
      (compactCells T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
        chi hUncountable good p) chi :=
  (birthChart T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
    chi hUncountable good p).presentable_arrow

/-- Every constructed split-tree birth cell is a compact scalar in the original class. -/
theorem originalSplitTree_cell_mem (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W] [W.IsStableUnderRetracts]
    (hs : ∀ a : P, W (s (T.label a)).hom) (p : HistoryIndex (P := P)) :
    W (compactCells T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
      chi hUncountable good p).hom :=
  compactCells_mem T L (r ≫ i) (OriginalRetractSplitIso.idempotent_idempotent i r hir)
    chi hUncountable good W hs p

/-- The actual compact scalar birth tree proves membership of its original endpoint arrow. -/
theorem originalSplitTree_hom_mem (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W] [W.IsStableUnderRetracts]
    (hs : ∀ a : P, W (s (T.label a)).hom) :
    W (originalSplitTree T L chi hUncountable good i r hir).hom :=
  CellTreeWeakSaturation.hom_mem W (originalSplitTree T L chi hUncountable good i r hir)
    (LowerSetColimitData.ofHasColimits _)
    (originalSplitTree_cell_mem T L chi hUncountable good i r hir W hs)

end OriginalCellTree

section SourceFixedArrow

variable [HasBinaryCoproducts C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (hUncountable : Cardinal.aleph0 < chi) (good : T.IsGood chi)
  [HasPushouts C] [HasColimitsOfSize.{w, w} C] [IsCardinalAccessibleCategory C chi]
  {Y : C} (f : X ⟶ Y) (R : RetractArrow f T.hom) (hsource : R.i.left = 𝟙 X)

/-- The original good tree supplies its own well-foundedness; its actual source-fixed
Arrow retract constructs the whole split tree, without a supplied history or filtration. -/
def fromOriginalArrow :
    letI := T.wellFoundedLT
    CellTree (compactCells T L
      (arrowProjection T f R hsource ≫ arrowInclusion T f R hsource)
      (OriginalRetractSplitIso.idempotent_idempotent
        (arrowInclusion T f R hsource) (arrowProjection T f R hsource)
        (arrowSplit T f R hsource)) chi hUncountable good) X
      (P := HistoryIndex (P := P)) := by
  letI := T.wellFoundedLT
  exact originalSplitTree T L chi hUncountable good
    (arrowInclusion T f R hsource) (arrowProjection T f R hsource) (arrowSplit T f R hsource)

/-- The full constructed filtration has exactly the ACTUAL original Arrow f as its endpoint. -/
theorem fromOriginalArrow_hom :
    letI := T.wellFoundedLT
    (fromOriginalArrow T L chi hUncountable good f R hsource).hom = f := rfl

/-- The original source-fixed retract constructs only compact scalar births
in the original class. -/
theorem fromOriginalArrow_cells_mem (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W] [W.IsStableUnderRetracts]
    (hs : ∀ a : P, W (s (T.label a)).hom) :
    letI := T.wellFoundedLT
    ∀ p, W (compactCells T L
      (arrowProjection T f R hsource ≫ arrowInclusion T f R hsource)
      (OriginalRetractSplitIso.idempotent_idempotent
        (arrowInclusion T f R hsource) (arrowProjection T f R hsource)
        (arrowSplit T f R hsource)) chi hUncountable good p).hom := by
  let _ := T.wellFoundedLT
  exact compactCells_mem T L _ _ chi hUncountable good W hs

/-- The constructed original source-fixed split filtration recovers f in the original class. -/
theorem fromOriginalArrow_mem (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    [MorphismProperty.IsStableUnderTransfiniteComposition.{w} W] [W.IsStableUnderRetracts]
    (hs : ∀ a : P, W (s (T.label a)).hom) :
    letI := T.wellFoundedLT
    W (fromOriginalArrow T L chi hUncountable good f R hsource).hom := by
  let _ := T.wellFoundedLT
  exact originalSplitTree_hom_mem T L chi hUncountable good
    (arrowInclusion T f R hsource) (arrowProjection T f R hsource) (arrowSplit T f R hsource)
    W hs

end SourceFixedArrow

section OriginalArrowEndpoint

variable {Y : C} (f : X ⟶ Y) (R : RetractArrow f T.hom) (hsource : R.i.left = 𝟙 X)

/-- The whole internal idempotent split comparison uses the actual original Arrow target maps. -/
abbrev fromOriginalArrowEndpointIso :
    IdempotentCoequalizerSplit.obj
      (arrowProjection T f R hsource ≫ arrowInclusion T f R hsource) ≅ Under.mk f :=
  OriginalRetractSplitIso.iso (arrowInclusion T f R hsource)
    (arrowProjection T f R hsource) (arrowSplit T f R hsource)

/-- Deprecated alias for `fromOriginalArrowEndpointIso`. -/
@[deprecated fromOriginalArrowEndpointIso (since := "2026-10-29"), nolint defsWithUnderscore]
alias fromOriginalArrow_endpointIso := fromOriginalArrowEndpointIso

/-- The forward whole comparison recovers the same original target projection. -/
theorem fromOriginalArrow_endpointProjection :
    (IdempotentCoequalizerSplit.projection
      (arrowProjection T f R hsource ≫ arrowInclusion T f R hsource)).right ≫
      (fromOriginalArrowEndpointIso T f R hsource).hom.right = R.r.right :=
  congrArg Under.Hom.right
    (OriginalRetractSplitIso.projection_iso_hom (arrowInclusion T f R hsource)
      (arrowProjection T f R hsource) (arrowSplit T f R hsource))

/-- The inverse whole comparison recovers the same original target inclusion
and split projection. -/
theorem fromOriginalArrow_endpointInverse :
    (fromOriginalArrowEndpointIso T f R hsource).inv.right =
      R.i.right ≫ (IdempotentCoequalizerSplit.projection
        (arrowProjection T f R hsource ≫ arrowInclusion T f R hsource)).right := rfl

/-- The whole comparison preserves the full original source equation for f. -/
theorem fromOriginalArrow_endpointRoot :
    (IdempotentCoequalizerSplit.obj
      (arrowProjection T f R hsource ≫ arrowInclusion T f R hsource)).hom ≫
      (fromOriginalArrowEndpointIso T f R hsource).hom.right = f :=
  Under.w (fromOriginalArrowEndpointIso T f R hsource).hom

end OriginalArrowEndpoint

end CategoryTheory.SmallObject.OriginalSplitFiltrationConstruction
