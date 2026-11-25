/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramActionCapture
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The same original Nat lower-colimit action

All stage factors and delayed equations come from the internally constructed
original refinement chain. The colimit remains the original L filtered
cocone. Ordinary Nat filteredness suffices; Nat is never made chi-filtered.
The main results assume that the regular rank `chi` is uncountable
(`Cardinal.aleph0 < chi`), since the refinement chain takes countable unions of
bounded label sets.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t uD vD uC vC

namespace CategoryTheory.SmallObject.DiagramActionRefinement

open CategoryTheory.Limits BoundedLowerSupport DiagramActionCapture

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (hUncountable : Cardinal.aleph0 < chi)
  {seed : Supports (P := P) chi} (K : RefinementChain theta L chi seed)

/-- The whole original lower-support sequence with its actual adjacent inclusions. -/
abbrev supportFunctor (d : D) : ℕ ⥤ LowerSet (P d) :=
  Functor.ofSequence (X := fun n => (K.supports n d).1)
    (fun n => homOfLE (K.le n d))

omit [Fact chi.IsRegular] in
@[simp]
theorem supportFunctor_obj (d : D) (n : ℕ) :
    (supportFunctor theta L chi K d).obj n = (K.supports n d).1 := rfl

omit [Fact chi.IsRegular] in
/-- Native sequence construction leaves every original adjacent support map unchanged. -/
theorem supportFunctor_map_succ (d : D) (n : ℕ) :
    (supportFunctor theta L chi K d).map (homOfLE (n.le_add_right 1)) =
      homOfLE (K.le n d) :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The actual countable union retains precisely the original lower-support values. -/
def unionSupport (d : D) : Carrier chi (P := P d) :=
  countableUnion chi hUncountable (fun n => K.supports n d)

@[simp]
theorem unionSupport_val (d : D) :
    (unionSupport theta L chi hUncountable K d).1 = ⨆ n, (K.supports n d).1 := rfl

/-- Each original stage is included in the same genuine bounded union. -/
theorem stage_le_union (d : D) (n : ℕ) :
    K.supports n d ≤ unionSupport theta L chi hUncountable K d :=
  le_indexedUnion chi (fun n => K.supports n d) (GoodOrderBounds.natLt chi hUncountable) n

/-- The original seed stays included through its literal stage-zero equality. -/
theorem seed_le_union (d : D) :
    seed d ≤ unionSupport theta L chi hUncountable K d := by
  exact (congrFun K.start d).symm.le.trans
    (stage_le_union theta L chi hUncountable K d 0)

/-- The source diagram is exactly the original selected lower-colimit functor. -/
abbrev stageDiagram (d : D) : ℕ ⥤ Under (F.obj d) :=
  (L d).filteredDiagram (supportFunctor theta L chi K d)

omit [Fact chi.IsRegular] in
/-- Its original adjacent comparison, as a whole under-morphism. -/
theorem stageDiagram_map_succ (d : D) (n : ℕ) :
    (stageDiagram theta L chi K d).map (homOfLE (n.le_add_right 1)) =
      (L d).map (K.le n d) := by
  change (L d).functor.map
    ((supportFunctor theta L chi K d).map (homOfLE (n.le_add_right 1))) = _
  rw [supportFunctor_map_succ]
  rfl

/-- The same selected union object under its original root. -/
abbrev unionObject (d : D) : Under (F.obj d) :=
  (L d).obj (unionSupport theta L chi hUncountable K d).1

/-- The original source-stage leg into its exact selected union. -/
abbrev stageLeg (d : D) (n : ℕ) :
    piece theta L d (K.supports n d).1 ⟶ unionObject theta L chi hUncountable K d :=
  (L d).map (stage_le_union theta L chi hUncountable K d n)

/-- Adjacent original inclusions compose to the same original union leg. -/
theorem inclusion_stageLeg (d : D) (n : ℕ) :
    ((L d).map (K.le n d)).right ≫ (stageLeg theta L chi hUncountable K d (n + 1)).right =
      (stageLeg theta L chi hUncountable K d n).right :=
  congrArg Under.Hom.right ((L d).map_comp (K.le n d)
    (stage_le_union theta L chi hUncountable K d (n + 1)))

/-- Every stage leg keeps the literal original G-endpoint comparison. -/
theorem stageLeg_endpoint (d : D) (n : ℕ) :
    (stageLeg theta L chi hUncountable K d n).right ≫
        leg theta L d (unionSupport theta L chi hUncountable K d).1 =
      leg theta L d (K.supports n d).1 :=
  inclusion_leg theta L d (stage_le_union theta L chi hUncountable K d n)

/-- The native colimit is the SAME original L cocone, not a second chosen engine. -/
abbrev originalColimit (d : D) :
    IsColimit ((L d).filteredCocone (supportFunctor theta L chi K d)) :=
  (L d).isColimitFilteredCocone

/-- A stage action lands in the root change of the same original target union. -/
def stageAction {d e : D} (g : d ⟶ e) (n : ℕ) :
    (stageDiagram theta L chi K d).obj n ⟶
      (Under.map (F.map g)).obj (unionObject theta L chi hUncountable K e) :=
  Under.homMk ((K.factors n).map g ≫ (stageLeg theta L chi hUncountable K e (n + 1)).right)
    (by
      change (piece theta L d (K.supports n d).1).hom ≫
        ((K.factors n).map g ≫ (stageLeg theta L chi hUncountable K e (n + 1)).right) =
        F.map g ≫ (unionObject theta L chi hUncountable K e).hom
      rw [← Category.assoc, (K.factors n).root, Category.assoc, Under.w])

/-- Its exact raw function retains the original stage factor and actual target comparison. -/
theorem stageAction_right {d e : D} (g : d ⟶ e) (n : ℕ) :
    (stageAction theta L chi hUncountable K g n).right =
      (K.factors n).map g ≫ (stageLeg theta L chi hUncountable K e (n + 1)).right := rfl

/-- The entire original action leg function, with its native root certificate. -/
theorem stageAction_right_function {d e : D} (g : d ⟶ e) :
    (fun n => (stageAction theta L chi hUncountable K g n).right) =
      (fun n => (K.factors n).map g ≫
        (stageLeg theta L chi hUncountable K e (n + 1)).right) := rfl

/-- The genuine ladder equation is adjacent naturality of these actual under-morphisms. -/
theorem stageAction_naturality_succ {d e : D} (g : d ⟶ e) (n : ℕ) :
    (stageDiagram theta L chi K d).map (homOfLE (n.le_add_right 1)) ≫
        stageAction theta L chi hUncountable K g (n + 1) =
      stageAction theta L chi hUncountable K g n := by
  rw [stageDiagram_map_succ]
  apply Under.UnderMorphism.ext
  change ((L d).map (K.le n d)).right ≫
    ((K.factors (n + 1)).map g ≫
      (stageLeg theta L chi hUncountable K e (n + 2)).right) =
    (K.factors n).map g ≫ (stageLeg theta L chi hUncountable K e (n + 1)).right
  calc
    _ = (((L d).map (K.le n d)).right ≫ (K.factors (n + 1)).map g) ≫
        (stageLeg theta L chi hUncountable K e (n + 2)).right :=
      (Category.assoc _ _ _).symm
    _ = ((K.factors n).map g ≫ ((L e).map (K.le (n + 1) e)).right) ≫
        (stageLeg theta L chi hUncountable K e (n + 2)).right := by
      rw [← K.ladder n g]
    _ = _ := by rw [Category.assoc, inclusion_stageLeg]

/-- Native NatTrans.ofSequence keeps the whole original app function. -/
def actionCocone {d e : D} (g : d ⟶ e) :
    Cocone (stageDiagram theta L chi K d) where
  pt := (Under.map (F.map g)).obj (unionObject theta L chi hUncountable K e)
  ι := NatTrans.ofSequence (stageAction theta L chi hUncountable K g)
    (fun n => by
      change _ = stageAction theta L chi hUncountable K g n ≫ 𝟙 _
      rw [Category.comp_id]
      exact stageAction_naturality_succ theta L chi hUncountable K g n)

/-- The actual cocone keeps every original selected stage leg. -/
theorem actionCocone_leg_function {d e : D} (g : d ⟶ e) :
    (fun n => ((actionCocone theta L chi hUncountable K g).ι.app n).right) =
      (fun n => (K.factors n).map g ≫
        (stageLeg theta L chi hUncountable K e (n + 1)).right) := rfl

/-- The actual whole under-morphism is the original L colimit descender. -/
def actionUnder {d e : D} (g : d ⟶ e) :
    unionObject theta L chi hUncountable K d ⟶
      (Under.map (F.map g)).obj (unionObject theta L chi hUncountable K e) :=
  (originalColimit theta L chi K d).desc (actionCocone theta L chi hUncountable K g)

/-- Its raw original coefficient action is precisely that descender's right component. -/
abbrev action {d e : D} (g : d ⟶ e) :
    (unionObject theta L chi hUncountable K d).right ⟶
      (unionObject theta L chi hUncountable K e).right :=
  (actionUnder theta L chi hUncountable K g).right

/-- Native fac preserves every original source-stage leg and original partial action. -/
theorem action_fac {d e : D} (g : d ⟶ e) (n : ℕ) :
    (stageLeg theta L chi hUncountable K d n).right ≫
        action theta L chi hUncountable K g =
      (K.factors n).map g ≫ (stageLeg theta L chi hUncountable K e (n + 1)).right :=
  congrArg Under.Hom.right
    ((originalColimit theta L chi K d).fac (actionCocone theta L chi hUncountable K g) n)

/-- The root equation belongs to the same actual native descender. -/
theorem action_root {d e : D} (g : d ⟶ e) :
    (unionObject theta L chi hUncountable K d).hom ≫ action theta L chi hUncountable K g =
      F.map g ≫ (unionObject theta L chi hUncountable K e).hom :=
  Under.w (actionUnder theta L chi hUncountable K g)

/-- The forced stage units prove the whole original unit through the source colimit. -/
theorem action_id (d : D) : action theta L chi hUncountable K (𝟙 d) =
    𝟙 (unionObject theta L chi hUncountable K d).right := by
  let p : unionObject theta L chi hUncountable K d ⟶
      unionObject theta L chi hUncountable K d :=
    Under.homMk (action theta L chi hUncountable K (𝟙 d)) (by
      simpa only [F.map_id, Category.id_comp] using action_root theta L chi hUncountable K (𝟙 d))
  have hp : p = 𝟙 _ := (originalColimit theta L chi K d).hom_ext (fun n => by
    apply Under.UnderMorphism.ext
    change (stageLeg theta L chi hUncountable K d n).right ≫
      action theta L chi hUncountable K (𝟙 d) =
      (stageLeg theta L chi hUncountable K d n).right ≫ 𝟙 _
    rw [action_fac, K.unit, inclusion_stageLeg, Category.comp_id])
  exact congrArg Under.Hom.right hp

/-- Delayed stage composition proves actual whole composition on the same source colimit. -/
theorem action_comp {d m e : D} (g : d ⟶ m) (h : m ⟶ e) :
    action theta L chi hUncountable K g ≫ action theta L chi hUncountable K h =
      action theta L chi hUncountable K (g ≫ h) := by
  let p : unionObject theta L chi hUncountable K d ⟶
      (Under.map (F.map (g ≫ h))).obj (unionObject theta L chi hUncountable K e) :=
    Under.homMk (action theta L chi hUncountable K g ≫ action theta L chi hUncountable K h) (by
      change (unionObject theta L chi hUncountable K d).hom ≫
        (action theta L chi hUncountable K g ≫ action theta L chi hUncountable K h) =
        F.map (g ≫ h) ≫ (unionObject theta L chi hUncountable K e).hom
      rw [← Category.assoc, action_root, Category.assoc, action_root, F.map_comp]
      exact (Category.assoc _ _ _).symm)
  have hp : p = actionUnder theta L chi hUncountable K (g ≫ h) :=
    (originalColimit theta L chi K d).hom_ext (fun n => by
      apply Under.UnderMorphism.ext
      change (stageLeg theta L chi hUncountable K d n).right ≫
          (action theta L chi hUncountable K g ≫ action theta L chi hUncountable K h) =
        (stageLeg theta L chi hUncountable K d n).right ≫
          action theta L chi hUncountable K (g ≫ h)
      calc
        _ = (K.factors n).map g ≫
            ((stageLeg theta L chi hUncountable K m (n + 1)).right ≫
              action theta L chi hUncountable K h) := by
          rw [← Category.assoc, action_fac, Category.assoc]
        _ = (K.factors n).map g ≫ ((K.factors (n + 1)).map h ≫
            (stageLeg theta L chi hUncountable K e (n + 2)).right) := by rw [action_fac]
        _ = ((K.factors n).map (g ≫ h) ≫ ((L e).map (K.le (n + 1) e)).right) ≫
            (stageLeg theta L chi hUncountable K e (n + 2)).right := by
          rw [← Category.assoc, K.composition]
        _ = (K.factors n).map (g ≫ h) ≫
            (stageLeg theta L chi hUncountable K e (n + 1)).right := by
          rw [Category.assoc, inclusion_stageLeg]
        _ = _ := (action_fac theta L chi hUncountable K (g ≫ h) n).symm)
  exact congrArg Under.Hom.right hp

/-- Source hom_ext proves endpoint naturality without cancelling the endpoint map. -/
theorem action_endpoint {d e : D} (g : d ⟶ e) :
    action theta L chi hUncountable K g ≫
        leg theta L e (unionSupport theta L chi hUncountable K e).1 =
      leg theta L d (unionSupport theta L chi hUncountable K d).1 ≫ G.map g := by
  let target : Under (F.obj d) := Under.mk (F.map g ≫ f.app e)
  let p : unionObject theta L chi hUncountable K d ⟶ target :=
    Under.homMk (action theta L chi hUncountable K g ≫
      leg theta L e (unionSupport theta L chi hUncountable K e).1) (by
        change (unionObject theta L chi hUncountable K d).hom ≫
          (action theta L chi hUncountable K g ≫
            leg theta L e (unionSupport theta L chi hUncountable K e).1) =
          F.map g ≫ f.app e
        rw [← Category.assoc, action_root, Category.assoc, leg_root])
  let q : unionObject theta L chi hUncountable K d ⟶ target :=
    Under.homMk (leg theta L d (unionSupport theta L chi hUncountable K d).1 ≫ G.map g) (by
      rw [← Category.assoc, leg_root]
      exact (f.naturality g).symm)
  have hp : p = q := (originalColimit theta L chi K d).hom_ext (fun n => by
    apply Under.UnderMorphism.ext
    change (stageLeg theta L chi hUncountable K d n).right ≫
        (action theta L chi hUncountable K g ≫
          leg theta L e (unionSupport theta L chi hUncountable K e).1) =
      (stageLeg theta L chi hUncountable K d n).right ≫
        (leg theta L d (unionSupport theta L chi hUncountable K d).1 ≫ G.map g)
    calc
      _ = (K.factors n).map g ≫
          ((stageLeg theta L chi hUncountable K e (n + 1)).right ≫
            leg theta L e (unionSupport theta L chi hUncountable K e).1) := by
        rw [← Category.assoc, action_fac, Category.assoc]
      _ = (K.factors n).map g ≫ leg theta L e (K.supports (n + 1) e).1 := by
        rw [stageLeg_endpoint]
      _ = leg theta L d (K.supports n d).1 ≫ G.map g := (K.factors n).endpoint g
      _ = _ := by rw [← stageLeg_endpoint, Category.assoc])
  exact congrArg Under.Hom.right hp

/-- The exact selected union objects and original descender maps form the whole functor. -/
def toFunctor : D ⥤ C where
  obj d := (unionObject theta L chi hUncountable K d).right
  map g := action theta L chi hUncountable K g
  map_id d := action_id theta L chi hUncountable K d
  map_comp g h := (action_comp theta L chi hUncountable K g h).symm

/-- Its entire original object function is the actual selected lower-union coefficient. -/
theorem object_function :
    (fun d => (toFunctor theta L chi hUncountable K).obj d) =
      (fun d => ((L d).obj (unionSupport theta L chi hUncountable K d).1).right) := rfl

/-- Its entire original Hom function is the right component of the SAME native descender. -/
theorem map_function :
    (fun (d e : D) (g : d ⟶ e) => (toFunctor theta L chi hUncountable K).map g) =
      (fun (d e : D) (g : d ⟶ e) =>
        (((L d).isColimitFilteredCocone (B := supportFunctor theta L chi K d)).desc
          (actionCocone theta L chi hUncountable K g)).right) := rfl

/-- Its original root functions form a natural transformation by the native root equation. -/
def root : F ⟶ toFunctor theta L chi hUncountable K where
  app d := (unionObject theta L chi hUncountable K d).hom
  naturality _ _ g := (action_root theta L chi hUncountable K g).symm

/-- Its original endpoint functions form the other whole natural transformation. -/
def target : toFunctor theta L chi hUncountable K ⟶ G where
  app d := leg theta L d (unionSupport theta L chi hUncountable K d).1
  naturality _ _ g := action_endpoint theta L chi hUncountable K g

/-- The full original root function is the original selected union-root function. -/
theorem root_function :
    (fun d => (root theta L chi hUncountable K).app d) =
      (fun d => ((L d).obj (unionSupport theta L chi hUncountable K d).1).hom) := rfl

/-- The entire endpoint function keeps the two given endpoint comparison maps. -/
theorem target_function :
    (fun d => (target theta L chi hUncountable K).app d) =
      (fun d => ((L d).map (le_top : (unionSupport theta L chi hUncountable K d).1 ≤ ⊤) ≫
        ((theta.component d).tree.endpointIso (L d)).hom ≫
          (theta.component d).endpointIso.hom).right) := by
  funext d
  simp only [target, leg, legUnder, EndpointDiagramTransport.lowerLeg,
    Under.comp_right, Category.assoc]
  rfl

/-- The strict whole original factor equation follows from Under.w, component by component. -/
theorem root_target : root theta L chi hUncountable K ≫ target theta L chi hUncountable K = f := by
  apply NatTrans.ext
  funext d
  exact leg_root theta L d (unionSupport theta L chi hUncountable K d).1

/-- The entire selected original label family is bounded at the same genuine direct rank. -/
theorem total_selected_labels (hArrow : HasCardinalLT (Arrow D) chi) :
    HasCardinalLT (Sigma (fun d : D =>
      ((unionSupport theta L chi hUncountable K d).1 : Set (P d)))) chi :=
  hasCardinalLT_sigma _ chi (hasCardinalLT_of_hasCardinalLT_arrow hArrow)
    (fun d => (unionSupport theta L chi hUncountable K d).2)

/-- The returned compatible slice has fixed original objects in every dependent map TYPE. -/
structure CompatibleSlice (seed : Supports (P := P) chi) where
  /-- The same original bounded supports. -/
  supports : Supports (P := P) chi
  /-- Original seeds remain included. -/
  le : ∀ d, seed d ≤ supports d
  /-- Actual output actions with literal original chosen-piece domains and codomains. -/
  map {d e : D} (g : d ⟶ e) :
    ((L d).obj (supports d).1).right ⟶ ((L e).obj (supports e).1).right
  /-- The original unit equality, proved by source colimit hom_ext. -/
  map_id (d : D) : map (𝟙 d) = 𝟙 ((L d).obj (supports d).1).right
  /-- The original composition equality, proved from actual delayed stage composition. -/
  map_comp {d m e : D} (g : d ⟶ m) (h : m ⟶ e) : map (g ≫ h) = map g ≫ map h
  /-- Both sides use the literal original chosen root maps. -/
  map_root {d e : D} (g : d ⟶ e) :
    ((L d).obj (supports d).1).hom ≫ map g = F.map g ≫ ((L e).obj (supports e).1).hom
  /-- Both sides retain the literal original target comparison legs. -/
  map_endpoint {d e : D} (g : d ⟶ e) :
    map g ≫ leg theta L e (supports e).1 = leg theta L d (supports d).1 ≫ G.map g
  /-- The genuine direct rank bounds the whole selected label family. -/
  labels_lt : HasCardinalLT (Sigma (fun d : D => ((supports d).1 : Set (P d)))) chi

/-- The output packet's whole functor has the same literal original object and action functions. -/
def CompatibleSlice.toFunctor (S : CompatibleSlice theta L chi seed) : D ⥤ C where
  obj d := ((L d).obj (S.supports d).1).right
  map g := S.map g
  map_id d := S.map_id d
  map_comp g h := S.map_comp g h

/-- The whole output root natural transformation uses every literal original root. -/
def CompatibleSlice.root (S : CompatibleSlice theta L chi seed) :
    F ⟶ S.toFunctor theta L chi where
  app d := ((L d).obj (S.supports d).1).hom
  naturality _ _ g := (S.map_root g).symm

/-- The whole output endpoint natural transformation uses every literal original target leg. -/
def CompatibleSlice.target (S : CompatibleSlice theta L chi seed) :
    S.toFunctor theta L chi ⟶ G where
  app d := leg theta L d (S.supports d).1
  naturality _ _ g := S.map_endpoint g

omit [Fact chi.IsRegular] in
/-- The output packet retains the strict whole original natural-transformation factorization. -/
theorem CompatibleSlice.factor (S : CompatibleSlice theta L chi seed) :
    S.root theta L chi ≫ S.target theta L chi = f := by
  apply NatTrans.ext
  funext d
  exact leg_root theta L d (S.supports d).1

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hArrow : HasCardinalLT (Arrow D) chi)
  (good : ∀ d, (theta.component d).tree.IsGood chi)

/-- The public constructor takes primitive original data and seeds, constructing its own chain. -/
def actionCompatibleSlice (originalSeed : Supports (P := P) chi) :
    CompatibleSlice theta L chi originalSeed := by
  let K := refinementChain theta L chi hArrow good originalSeed
  exact
    { supports := unionSupport theta L chi hUncountable K
      le := seed_le_union theta L chi hUncountable K
      map := action theta L chi hUncountable K
      map_id := action_id theta L chi hUncountable K
      map_comp := fun g h => (action_comp theta L chi hUncountable K g h).symm
      map_root := action_root theta L chi hUncountable K
      map_endpoint := action_endpoint theta L chi hUncountable K
      labels_lt := total_selected_labels theta L chi hUncountable K hArrow }

/-- The public construction retains its original internally chosen support union function. -/
theorem actionCompatibleSlice_support_function (originalSeed : Supports (P := P) chi) :
    (actionCompatibleSlice theta L chi hUncountable hArrow good originalSeed).supports =
      unionSupport theta L chi hUncountable
        (refinementChain theta L chi hArrow good originalSeed) := rfl

/-- The whole public action function is the same internal chain's original native descender. -/
theorem actionCompatibleSlice_map_function (originalSeed : Supports (P := P) chi) :
    (fun (d e : D) (g : d ⟶ e) =>
      (actionCompatibleSlice theta L chi hUncountable hArrow good originalSeed).map g) =
    (fun (d e : D) (g : d ⟶ e) =>
      action theta L chi hUncountable
        (refinementChain theta L chi hArrow good originalSeed) g) := rfl

/-- The original input seeds and every actual selected label remain in the returned packet. -/
theorem actionCompatibleSlice_seed_labels (originalSeed : Supports (P := P) chi) :
    (∀ d, originalSeed d ≤
      (actionCompatibleSlice theta L chi hUncountable hArrow good originalSeed).supports d) ∧
    HasCardinalLT (Sigma (fun d : D =>
      (((actionCompatibleSlice theta L chi hUncountable hArrow good originalSeed).supports d).1 :
        Set (P d)))) chi :=
  ⟨(actionCompatibleSlice theta L chi hUncountable hArrow good originalSeed).le,
    (actionCompatibleSlice theta L chi hUncountable hArrow good originalSeed).labels_lt⟩


/-- The theorem returns the SAME internally chosen chain union, entire functor and strict factor. -/
theorem existsActionCompatibleSlice (originalSeed : Supports (P := P) chi) :
    ∃ S : CompatibleSlice theta L chi originalSeed,
      S.supports = unionSupport theta L chi hUncountable
        (refinementChain theta L chi hArrow good originalSeed) ∧
      S.toFunctor theta L chi = toFunctor theta L chi hUncountable
        (refinementChain theta L chi hArrow good originalSeed) ∧
      S.root theta L chi ≫ S.target theta L chi = f := by
  refine ⟨actionCompatibleSlice theta L chi hUncountable hArrow good originalSeed, rfl, rfl, ?_⟩
  exact (actionCompatibleSlice theta L chi hUncountable hArrow good originalSeed).factor theta L chi

end CategoryTheory.SmallObject.DiagramActionRefinement
