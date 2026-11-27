/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceExhaustion
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalPredecessorCellCapture

/-!
# Compatible intersections in original good diagram cell trees

A pair of actual preserved extension chains constructs both bounded slice
unions and the original natural inclusions of their literal intersection.
The original lower-colimit witnesses detect the action equalities; endpoint
maps are never cancelled. The original slice may have unbounded supports.
The main results assume that the regular rank `chi` is uncountable
(`Cardinal.aleph0 < chi`).

This is the fixed-component-tree ordinary construction in Lurie,
*Higher Topos Theory*, Lemma A.3.3.16. Production of good trees for all
original coefficient cofibrations is a separate theorem.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SmallObject
open CategoryTheory.SmallObject.DiagramSliceExhaustion

universe w t uD vD uC vC

namespace CategoryTheory.SmallObject.DiagramSliceIntersection

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (A : OriginalSlice theta L)

-- Actual original lower trees, with the SAME original slice root and endpoint.
private noncomputable abbrev restrictedPresentation :
    PointwiseCellTreePresentation (s := s) A.root (fun d => A.supports d) where
  component d :=
    { tree := CellTreeLowerRestriction.tree (theta.component d).tree (L d) (A.supports d)
      endpointIso := Under.isoMk (Iso.refl _) (by
        change ((L d).obj (A.supports d)).hom ≫ 𝟙 _ =
          ((L d).obj (A.supports d)).hom
        exact Category.comp_id _) }

-- All lower pieces remain the actual original L pieces on lifted original labels.
private noncomputable abbrev restrictedLowerData (d : D) :
    LowerSetColimitData ((restrictedPresentation theta L A).component d).tree.diagram :=
  OriginalLowerSubtreeChoices.choices (A.supports d) (L d)

-- The restricted endpoint leg is the actual original lower-to-A comparison.
private theorem restrictedLeg (d : D) (U : LowerSet (A.supports d)) :
    DiagramActionCapture.leg (restrictedPresentation theta L A)
      (restrictedLowerData theta L A) d U =
        ((L d).map (OriginalLowerSubtreeChoices.lift_le (A.supports d) U)).right := by
  have h := congrArg Under.Hom.right
    (OriginalPredecessorCellCapture.originalEndpointMap
      (theta.component d).tree (L d) (A.supports d) U)
  have hc : DiagramActionCapture.leg (restrictedPresentation theta L A)
      (restrictedLowerData theta L A) d U =
        (((OriginalLowerSubtreeChoices.choices (A.supports d) (L d)).map (le_top : U ≤ ⊤)) ≫
          ((CellTreeLowerRestriction.tree (theta.component d).tree (L d) (A.supports d)).endpointIso
            (OriginalLowerSubtreeChoices.choices (A.supports d) (L d))).hom).right ≫
          𝟙 ((L d).obj (A.supports d)).right := rfl
  exact hc.trans ((Category.comp_id _).trans h)


-- The same original points and action functions turn a bounded restricted slice
-- into a bounded original slice; only the original label carrier is lifted.
private noncomputable def liftSlice (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (U : DiagramSliceExtensions.Slice (restrictedPresentation theta L A)
      (restrictedLowerData theta L A) chi) : DiagramSliceExtensions.Slice theta L chi := by
  let supports (d : D) : BoundedLowerSupport.Carrier chi (P := P d) :=
    ⟨OriginalLowerSubtreeChoices.lift (A.supports d) (U.supports d).1,
      OriginalLowerSubtreeChoices.lift_bound (A.supports d) chi (U.supports d).1
        (U.supports d).2⟩
  refine
    { supports := supports
      le := fun d => by
        change (⊥ : LowerSet (P d)) ≤ (supports d).1
        exact bot_le
      map := fun g => U.map g
      map_id := U.map_id
      map_comp := U.map_comp
      map_root := fun g => U.map_root g
      map_endpoint := ?_
      labels_lt := ?_ }
  · intro d e g
    let hd := OriginalLowerSubtreeChoices.lift_le (A.supports d) (U.supports d).1
    let he := OriginalLowerSubtreeChoices.lift_le (A.supports e) (U.supports e).1
    let m : ((L d).obj (OriginalLowerSubtreeChoices.lift (A.supports d) (U.supports d).1)).right ⟶
        ((L e).obj (OriginalLowerSubtreeChoices.lift
          (A.supports e) (U.supports e).1)).right := U.map g
    have hu : m ≫ ((L e).map he).right = ((L d).map hd).right ≫ A.map g := by
      have h := U.map_endpoint g
      change U.map g ≫ DiagramActionCapture.leg (restrictedPresentation theta L A)
          (restrictedLowerData theta L A) e (U.supports e).1 =
        DiagramActionCapture.leg (restrictedPresentation theta L A)
          (restrictedLowerData theta L A) d (U.supports d).1 ≫ A.map g at h
      rw [restrictedLeg theta L A e (U.supports e).1,
        restrictedLeg theta L A d (U.supports d).1] at h
      exact h
    change m ≫ DiagramActionCapture.leg theta L e
        (OriginalLowerSubtreeChoices.lift (A.supports e) (U.supports e).1) =
      DiagramActionCapture.leg theta L d
        (OriginalLowerSubtreeChoices.lift (A.supports d) (U.supports d).1) ≫ G.map g
    calc
      m ≫ DiagramActionCapture.leg theta L e
          (OriginalLowerSubtreeChoices.lift (A.supports e) (U.supports e).1) =
        m ≫ (((L e).map he).right ≫ DiagramActionCapture.leg theta L e (A.supports e)) :=
          congrArg (fun z => m ≫ z) (DiagramActionCapture.inclusion_leg theta L e he).symm
      _ = (m ≫ ((L e).map he).right) ≫ DiagramActionCapture.leg theta L e (A.supports e) :=
        (Category.assoc _ _ _).symm
      _ = (((L d).map hd).right ≫ A.map g) ≫ DiagramActionCapture.leg theta L e (A.supports e) :=
        congrArg (fun z => z ≫ DiagramActionCapture.leg theta L e (A.supports e)) hu
      _ = ((L d).map hd).right ≫
          (DiagramActionCapture.leg theta L d (A.supports d) ≫ G.map g) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun z => ((L d).map hd).right ≫ z) (A.map_endpoint g))
      _ = DiagramActionCapture.leg theta L d
          (OriginalLowerSubtreeChoices.lift (A.supports d) (U.supports d).1) ≫ G.map g :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ G.map g) (DiagramActionCapture.inclusion_leg theta L d hd))
  · let E : (Σ d : D, ((supports d).1 : Set (P d))) ≃
        (Σ d : D, ((U.supports d).1 : Set (A.supports d))) :=
      Equiv.sigmaCongrRight (fun d =>
        (OriginalLowerSubtreeChoices.carrierIso (A.supports d) (U.supports d).1).symm.toEquiv)
    exact U.labels_lt.of_injective E E.injective


-- The lifted slice has its actual natural inclusion into the original unbounded A.
private noncomputable def liftedInclusion (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (U : DiagramSliceExtensions.Slice (restrictedPresentation theta L A)
      (restrictedLowerData theta L A) chi) :
    OriginalSlice.Inclusion (OriginalSlice.ofBounded chi (liftSlice theta L A chi U)) A where
  le d := OriginalLowerSubtreeChoices.lift_le (A.supports d) (U.supports d).1
  naturality {d e} g := by
    have h := U.map_endpoint g
    change U.map g ≫ DiagramActionCapture.leg (restrictedPresentation theta L A)
        (restrictedLowerData theta L A) e (U.supports e).1 =
      DiagramActionCapture.leg (restrictedPresentation theta L A)
        (restrictedLowerData theta L A) d (U.supports d).1 ≫ A.map g at h
    rw [restrictedLeg theta L A e (U.supports e).1,
      restrictedLeg theta L A d (U.supports d).1] at h
    exact h.symm

-- Each actual restricted inclusion becomes the same original lifted-support map.
private noncomputable def liftSliceMap (chi : Cardinal.{w}) [Fact chi.IsRegular]
    {U V : DiagramSliceExtensions.Slice (restrictedPresentation theta L A)
      (restrictedLowerData theta L A) chi} (p : U ⟶ V) :
    liftSlice theta L A chi U ⟶ liftSlice theta L A chi V where
  support_le d := OriginalLowerSubtreeChoices.lift_mono (A.supports d) (p.support_le d)
  naturality {d e} g := by
    have h := p.naturality g
    have hm (d : D) : (restrictedLowerData theta L A d).map (p.support_le d) =
        (L d).map (OriginalLowerSubtreeChoices.lift_mono (A.supports d) (p.support_le d)) :=
      OriginalLowerSubtreeChoices.choices_map (A.supports d) (L d) (p.support_le d)
    rw [hm d, hm e] at h
    exact h


-- An actual chain of compatible slices supplies every existing refinement certificate.
private noncomputable def sliceChain (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (S : ℕ → DiagramSliceExtensions.Slice theta L chi)
    (p : ∀ n, S n ⟶ S (n + 1)) :
    DiagramActionCapture.RefinementChain theta L chi (S 0).supports := by
  let inc (n : ℕ) (d : D) := ((L d).map ((p n).support_le d)).right
  let factors (n : ℕ) :
      DiagramActionCapture.Factors theta L chi (S n).supports (S (n + 1)).supports :=
    { map := fun {d e} g => (S n).map g ≫ inc n e
      root := fun {d e} g => by
        rw [← Category.assoc, (S n).map_root, Category.assoc, Under.w]
      endpoint := fun {d e} g => by
        rw [Category.assoc, DiagramActionCapture.inclusion_leg]
        exact (S n).map_endpoint g }
  refine
    { supports := fun n => (S n).supports
      start := rfl
      le := fun n d => (p n).support_le d
      factors := factors
      unit := ?_
      ladder := ?_
      composition := ?_ }
  · intro n d
    change (S n).map (𝟙 d) ≫ inc n d = _
    rw [(S n).map_id, Category.id_comp]
  · intro n d e g
    change ((S n).map g ≫ inc n e) ≫ inc (n + 1) e =
      inc n d ≫ ((S (n + 1)).map g ≫ inc (n + 1) e)
    have h : inc n d ≫ (S (n + 1)).map g = (S n).map g ≫ inc n e := (p n).naturality g
    exact (congrArg (fun z => z ≫ inc (n + 1) e) h).symm.trans (Category.assoc _ _ _)
  · intro n d m e g h
    change ((S n).map g ≫ inc n m) ≫ ((S (n + 1)).map h ≫ inc (n + 1) e) =
      ((S n).map (g ≫ h) ≫ inc n e) ≫ inc (n + 1) e
    have hp : inc n m ≫ (S (n + 1)).map h = (S n).map h ≫ inc n e := (p n).naturality h
    rw [Category.assoc, ← Category.assoc (inc n m), hp]
    rw [Category.assoc, ← Category.assoc ((S n).map g), ← (S n).map_comp]
    simp only [Category.assoc]


-- The actual existing refinement colimit forms the bounded union of an actual slice chain.
private noncomputable def chainUnion (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
    (S : ℕ → DiagramSliceExtensions.Slice theta L chi) (p : ∀ n, S n ⟶ S (n + 1)) :
    DiagramSliceExtensions.Slice theta L chi := by
  let K := sliceChain theta L chi S p
  exact
    { supports := DiagramActionRefinement.unionSupport theta L chi hUncountable K
      le := fun d => by
        change (⊥ : LowerSet (P d)) ≤ _
        exact bot_le
      map := DiagramActionRefinement.action theta L chi hUncountable K
      map_id := DiagramActionRefinement.action_id theta L chi hUncountable K
      map_comp := fun g h =>
        (DiagramActionRefinement.action_comp theta L chi hUncountable K g h).symm
      map_root := DiagramActionRefinement.action_root theta L chi hUncountable K
      map_endpoint := DiagramActionRefinement.action_endpoint theta L chi hUncountable K
      labels_lt := DiagramActionRefinement.total_selected_labels theta L chi hUncountable K hArrow }

-- Every actual original source-stage inclusion is natural into that SAME union.
private noncomputable def chainUnionStage (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
    (S : ℕ → DiagramSliceExtensions.Slice theta L chi) (p : ∀ n, S n ⟶ S (n + 1)) (n : ℕ) :
    S n ⟶ chainUnion theta L chi hUncountable hArrow S p where
  support_le d := DiagramActionRefinement.stage_le_union theta L chi hUncountable
    (sliceChain theta L chi S p) d n
  naturality {d e} g := by
    let K := sliceChain theta L chi S p
    change (DiagramActionRefinement.stageLeg theta L chi hUncountable K d n).right ≫
        DiagramActionRefinement.action theta L chi hUncountable K g =
      (S n).map g ≫ (DiagramActionRefinement.stageLeg theta L chi hUncountable K e n).right
    rw [DiagramActionRefinement.action_fac]
    change ((S n).map g ≫ ((L e).map ((p n).support_le e)).right) ≫
        (DiagramActionRefinement.stageLeg theta L chi hUncountable K e (n + 1)).right = _
    have h : ((L e).map ((p n).support_le e)).right ≫
        (DiagramActionRefinement.stageLeg theta L chi hUncountable K e (n + 1)).right =
      (DiagramActionRefinement.stageLeg theta L chi hUncountable K e n).right :=
      DiagramActionRefinement.inclusion_stageLeg theta L chi hUncountable K e n
    exact (Category.assoc _ _ _).trans (congrArg (fun z => (S n).map g ≫ z) h)


-- The original union colimit glues actual natural inclusions into an unbounded slice.
private noncomputable def chainUnionIntoOriginal (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
    (S : ℕ → DiagramSliceExtensions.Slice theta L chi) (p : ∀ n, S n ⟶ S (n + 1))
    (q : ∀ n, OriginalSlice.Inclusion (OriginalSlice.ofBounded chi (S n)) A) :
    OriginalSlice.Inclusion
      (OriginalSlice.ofBounded chi (chainUnion theta L chi hUncountable hArrow S p)) A := by
  let K := sliceChain theta L chi S p
  let B := chainUnion theta L chi hUncountable hArrow S p
  have hBA (d : D) : (B.supports d).1 ≤ A.supports d := iSup_le (fun n => (q n).le d)
  refine { le := hBA, naturality := ?_ }
  intro d e g
  let target : Under (F.obj d) := (Under.map (F.map g)).obj ((L e).obj (A.supports e))
  let left : (L d).obj (B.supports d).1 ⟶ target :=
    Under.homMk (((L d).map (hBA d)).right ≫ A.map g) (by
      rw [← Category.assoc, Under.w, A.map_root]
      rfl)
  let right : (L d).obj (B.supports d).1 ⟶ target :=
    Under.homMk (B.map g ≫ ((L e).map (hBA e)).right) (by
      rw [← Category.assoc, B.map_root, Category.assoc, Under.w]
      rfl)
  have h : left = right := by
    apply (DiagramActionRefinement.originalColimit theta L chi K d).hom_ext
    intro n
    apply Under.UnderMorphism.ext
    let ld : ((L d).obj ((S n).supports d).1).right ⟶ ((L d).obj (B.supports d).1).right :=
      (DiagramActionRefinement.stageLeg theta L chi hUncountable K d n).right
    let le : ((L e).obj ((S n).supports e).1).right ⟶ ((L e).obj (B.supports e).1).right :=
      (DiagramActionRefinement.stageLeg theta L chi hUncountable K e n).right
    have hd : ld ≫ ((L d).map (hBA d)).right = ((L d).map ((q n).le d)).right := by
      change ((L d).map
        (DiagramActionRefinement.stage_le_union theta L chi hUncountable K d n)).right ≫
        ((L d).map (hBA d)).right = _
      have h := congrArg Under.Hom.right ((L d).map_comp
        (DiagramActionRefinement.stage_le_union theta L chi hUncountable K d n) (hBA d))
      change ld ≫ ((L d).map (hBA d)).right = ((L d).map ((q n).le d)).right at h
      exact h
    have he : le ≫ ((L e).map (hBA e)).right = ((L e).map ((q n).le e)).right := by
      change ((L e).map
        (DiagramActionRefinement.stage_le_union theta L chi hUncountable K e n)).right ≫
        ((L e).map (hBA e)).right = _
      have h := congrArg Under.Hom.right ((L e).map_comp
        (DiagramActionRefinement.stage_le_union theta L chi hUncountable K e n) (hBA e))
      change le ≫ ((L e).map (hBA e)).right = ((L e).map ((q n).le e)).right at h
      exact h
    have hn : ld ≫ B.map g = (S n).map g ≫ le :=
      (chainUnionStage theta L chi hUncountable hArrow S p n).naturality g
    change ld ≫ (((L d).map (hBA d)).right ≫ A.map g) =
      ld ≫ (B.map g ≫ ((L e).map (hBA e)).right)
    have hq : ((L d).map ((q n).le d)).right ≫ A.map g =
        (S n).map g ≫ ((L e).map ((q n).le e)).right := (q n).naturality g
    have hl : ld ≫ (((L d).map (hBA d)).right ≫ A.map g) =
        (S n).map g ≫ ((L e).map ((q n).le e)).right :=
      (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ A.map g) hd).trans hq)
    have hr : ld ≫ (B.map g ≫ ((L e).map (hBA e)).right) =
        (S n).map g ≫ ((L e).map ((q n).le e)).right :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ ((L e).map (hBA e)).right) hn).trans
          ((Category.assoc _ _ _).trans (congrArg (fun z => (S n).map g ≫ z) he)))
    exact hl.trans hr.symm
  exact congrArg Under.Hom.right h

-- A bounded original seed is pulled inside the original, possibly unbounded A.
private def insideSeed (chi : Cardinal.{w})
    (B : DiagramActionCapture.Supports (P := P) chi) :
    DiagramActionCapture.Supports (P := fun d => A.supports d) chi := by
  intro d
  let U : LowerSet (A.supports d) :=
    { carrier := {p | p.1 ∈ (B d).1}
      lower' := fun _ _ h hp => (B d).1.lower' h hp }
  refine ⟨U, (B d).2.of_injective
    (fun p : (U : Set (A.supports d)) => (⟨p.1.1, p.2⟩ : ((B d).1 : Set (P d)))) ?_⟩
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ((B d).1 : Set (P d)) => z.1) h

private theorem insideSeed_lift (chi : Cardinal.{w})
    (B : DiagramActionCapture.Supports (P := P) chi) (d : D) :
    OriginalLowerSubtreeChoices.lift (A.supports d) (insideSeed theta L A chi B d).1 =
      A.supports d ⊓ (B d).1 := by
  ext p
  constructor
  · rintro ⟨hpA, hpB⟩
    exact ⟨hpA, hpB⟩
  · rintro ⟨hpA, hpB⟩
    exact ⟨hpA, hpB⟩

-- Both actual lanes and their original cross comparison are selected together.
@[nolint structureInType]
private structure Stage (chi : Cardinal.{w}) [Fact chi.IsRegular] where
  inside : DiagramSliceExtensions.Slice (restrictedPresentation theta L A)
    (restrictedLowerData theta L A) chi
  outside : DiagramSliceExtensions.Slice theta L chi
  cross : liftSlice theta L A chi inside ⟶ outside

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]

private noncomputable def firstStage (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
    (good : ∀ d, (theta.component d).tree.IsGood chi)
    (B : DiagramActionCapture.Supports (P := P) chi) : Stage theta L A chi := by
  let goodA := fun d => CellTreeLowerRestriction.tree_good
    (theta.component d).tree (L d) (A.supports d) chi (good d)
  let emptyFamily : Empty → DiagramSliceExtensions.Slice (restrictedPresentation theta L A)
      (restrictedLowerData theta L A) chi := fun i => nomatch i
  let U := DiagramSliceExtensions.extension (restrictedPresentation theta L A)
    (restrictedLowerData theta L A) chi hArrow goodA
    (hasCardinalLT_of_finite Empty chi hUncountable.le) emptyFamily hUncountable
    (DiagramSliceExtensions.emptySupports chi)
  let family : Unit → DiagramSliceExtensions.Slice theta L chi :=
    fun _ => liftSlice theta L A chi U
  let V := DiagramSliceExtensions.extension theta L chi hArrow good
    (hasCardinalLT_of_finite Unit chi hUncountable.le) family hUncountable B
  exact
    { inside := U
      outside := V
      cross := DiagramSliceExtensions.extensionInclusion theta L chi hArrow good
        (hasCardinalLT_of_finite Unit chi hUncountable.le) family hUncountable B () }

-- A single actual step retains both old action systems and captures A ∩ outside.
@[nolint structureInType]
private structure StageStep (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (S : Stage theta L A chi) where
  next : Stage theta L A chi
  insideInclusion : S.inside ⟶ next.inside
  outsideInclusion : S.outside ⟶ next.outside
  capture (d : D) : A.supports d ⊓ (S.outside.supports d).1 ≤
    (liftSlice theta L A chi next.inside).supports d

private noncomputable def stageStep (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
    (good : ∀ d, (theta.component d).tree.IsGood chi)
    (S : Stage theta L A chi) : StageStep theta L A chi S := by
  let goodA := fun d => CellTreeLowerRestriction.tree_good
    (theta.component d).tree (L d) (A.supports d) chi (good d)
  let insideFamily : Unit → DiagramSliceExtensions.Slice (restrictedPresentation theta L A)
      (restrictedLowerData theta L A) chi := fun _ => S.inside
  let seed := insideSeed theta L A chi S.outside.supports
  let U := DiagramSliceExtensions.extension (restrictedPresentation theta L A)
    (restrictedLowerData theta L A) chi hArrow goodA
    (hasCardinalLT_of_finite Unit chi hUncountable.le) insideFamily hUncountable seed
  let outsideFamily : Bool → DiagramSliceExtensions.Slice theta L chi :=
    fun b => if b then liftSlice theta L A chi U else S.outside
  let V := DiagramSliceExtensions.extension theta L chi hArrow good
    (hasCardinalLT_of_finite Bool chi hUncountable.le) outsideFamily hUncountable
    (DiagramSliceExtensions.emptySupports chi)
  refine
    { next :=
        { inside := U
          outside := V
          cross := DiagramSliceExtensions.extensionInclusion theta L chi hArrow good
            (hasCardinalLT_of_finite Bool chi hUncountable.le) outsideFamily hUncountable
            (DiagramSliceExtensions.emptySupports chi) true }
      insideInclusion := DiagramSliceExtensions.extensionInclusion
        (restrictedPresentation theta L A) (restrictedLowerData theta L A) chi hArrow goodA
        (hasCardinalLT_of_finite Unit chi hUncountable.le) insideFamily hUncountable seed ()
      outsideInclusion := DiagramSliceExtensions.extensionInclusion theta L chi hArrow good
        (hasCardinalLT_of_finite Bool chi hUncountable.le) outsideFamily hUncountable
        (DiagramSliceExtensions.emptySupports chi) false
      capture := ?_ }
  intro d
  rw [← insideSeed_lift theta L A chi S.outside.supports d]
  exact OriginalLowerSubtreeChoices.lift_mono (A.supports d)
    (DiagramSliceExtensions.seed_le_extension (restrictedPresentation theta L A)
      (restrictedLowerData theta L A) chi hArrow goodA
      (hasCardinalLT_of_finite Unit chi hUncountable.le) insideFamily hUncountable seed d)

private theorem firstStage_seed (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
    (good : ∀ d, (theta.component d).tree.IsGood chi)
    (B : DiagramActionCapture.Supports (P := P) chi) (d : D) :
    B d ≤ (firstStage theta L A chi hUncountable hArrow good B).outside.supports d := by
  exact DiagramSliceExtensions.seed_le_extension theta L chi hArrow good
    (hasCardinalLT_of_finite Unit chi hUncountable.le)
    (fun _ : Unit => liftSlice theta L A chi
      (firstStage theta L A chi hUncountable hArrow good B).inside) hUncountable B d

-- Nat recursion constructs the original two lanes, rather than assuming a chain.
private noncomputable def stages (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
    (good : ∀ d, (theta.component d).tree.IsGood chi)
    (B : DiagramActionCapture.Supports (P := P) chi) : ℕ → Stage theta L A chi :=
  Nat.rec (firstStage theta L A chi hUncountable hArrow good B)
    (fun _ S => (stageStep theta L A chi hUncountable hArrow good S).next)

-- The full original bounded comparison is also an original unbounded comparison.
private noncomputable def boundedInclusion (chi : Cardinal.{w}) [Fact chi.IsRegular]
    {U V : DiagramSliceExtensions.Slice theta L chi} (p : U ⟶ V) :
    OriginalSlice.Inclusion (OriginalSlice.ofBounded chi U) (OriginalSlice.ofBounded chi V) where
  le := p.support_le
  naturality := p.naturality

/-- Every bounded seed has a bounded compatible receiving slice whose literal
intersection with an arbitrary original slice is bounded and compatible.
Both inclusion arrows use the original lower-piece comparison functions. -/
theorem existsGenericBoundedCompatibleIntersection (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
    (good : ∀ d, (theta.component d).tree.IsGood chi)
    (seed : DiagramActionCapture.Supports (P := P) chi) :
    ∃ (N Nprime : DiagramSliceExtensions.Slice theta L chi),
      (∀ d, seed d ≤ N.supports d) ∧
      (∀ d, (Nprime.supports d).1 = A.supports d ⊓ (N.supports d).1) ∧
      Nonempty (OriginalSlice.Inclusion (OriginalSlice.ofBounded chi Nprime) A) ∧
      Nonempty (OriginalSlice.Inclusion
        (OriginalSlice.ofBounded chi Nprime) (OriginalSlice.ofBounded chi N)) := by
  let S := stages theta L A chi hUncountable hArrow good seed
  let U : ℕ → DiagramSliceExtensions.Slice theta L chi :=
    fun n => liftSlice theta L A chi (S n).inside
  let V : ℕ → DiagramSliceExtensions.Slice theta L chi := fun n => (S n).outside
  let pU : ∀ n, U n ⟶ U (n + 1) := fun n =>
    liftSliceMap theta L A chi
      (stageStep theta L A chi hUncountable hArrow good (S n)).insideInclusion
  let pV : ∀ n, V n ⟶ V (n + 1) := fun n =>
    (stageStep theta L A chi hUncountable hArrow good (S n)).outsideInclusion
  let N := chainUnion theta L chi hUncountable hArrow V pV
  let Nprime := chainUnion theta L chi hUncountable hArrow U pU
  refine ⟨N, Nprime, ?_, ?_, ?_, ?_⟩
  · intro d
    exact (firstStage_seed theta L A chi hUncountable hArrow good seed d).trans
      ((chainUnionStage theta L chi hUncountable hArrow V pV 0).support_le d)
  · intro d
    change (⨆ n, ((U n).supports d).1) = A.supports d ⊓ (⨆ n, ((V n).supports d).1)
    apply interleaved_intersection
    · intro n
      exact le_inf (OriginalLowerSubtreeChoices.lift_le (A.supports d) ((S n).inside.supports d).1)
        ((S n).cross.support_le d)
    · intro n
      exact (stageStep theta L A chi hUncountable hArrow good (S n)).capture d
  · exact ⟨chainUnionIntoOriginal theta L A chi hUncountable hArrow U pU
      (fun n => liftedInclusion theta L A chi (S n).inside)⟩
  · exact ⟨chainUnionIntoOriginal theta L (OriginalSlice.ofBounded chi N) chi
      hUncountable hArrow U pU (fun n => boundedInclusion theta L chi
        ((S n).cross ≫ chainUnionStage theta L chi hUncountable hArrow V pV n))⟩

end CategoryTheory.SmallObject.DiagramSliceIntersection
