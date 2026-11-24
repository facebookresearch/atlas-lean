/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.Boundary
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Natural lifts from original latching and matching corners

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure.Lifting

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPullbacks C] [HasPushouts C]
  {A B X Y : J ⥤ C} {i : A ⟶ B} {p : X ⟶ Y} {t : A ⟶ X} {b : B ⟶ Y}
  (sq : CommSq t i p b)

/-- A lift on all smaller original objects, natural on every original arrow between them. -/
structure LowerLift (sq : CommSq t i p b) (d : D) where
  /-- The lift component `B.obj j ⟶ X.obj j` at each object of degree below `d`. -/
  app (j : J) (hj : r.degree j < d) : B.obj j ⟶ X.obj j
  left (j : J) (hj : r.degree j < d) : i.app j ≫ app j hj = t.app j
  right (j : J) (hj : r.degree j < d) : app j hj ≫ p.app j = b.app j
  naturality {j k : J} (hj : r.degree j < d) (hk : r.degree k < d) (f : j ⟶ k) :
    B.map f ≫ app k hk = app j hj ≫ X.map f

attribute [reassoc] LowerLift.left LowerLift.right

variable {r sq}

/-- The smaller lift and original incoming arrows give the complete latching cocone at the next
object. -/
def lowerLatchingCocone (j : J) (l : LowerLift r sq (r.degree j)) :
    Cocone (r.latchingDiagram B j) where
  pt := X.obj j
  ι.app a := l.app a.obj.left.obj a.property ≫ X.map (r.latchingArrow a)
  ι.naturality a c f := by
    change B.map (r.latchingComparison f) ≫
      (l.app c.obj.left.obj c.property ≫ X.map (r.latchingArrow c)) =
      (l.app a.obj.left.obj a.property ≫ X.map (r.latchingArrow a)) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, l.naturality a.property c.property,
      Category.assoc, ← X.map_comp]
    congr 2
    exact r.latchingComparison_arrow f

/-- The next latching lift uses the universal property of the complete original latching diagram. -/
def lowerLatchingMap (j : J) (l : LowerLift r sq (r.degree j)) :
    colimit (r.latchingDiagram B j) ⟶ X.obj j :=
  colimit.desc _ (lowerLatchingCocone j l)

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C] [HasPushouts C] in
@[reassoc]
theorem lowerLatchingMap_ι (j : J) (l : LowerLift r sq (r.degree j)) (a : r.Latching j) :
    colimit.ι (r.latchingDiagram B j) a ≫ lowerLatchingMap j l =
      l.app a.obj.left.obj a.property ≫ X.map (r.latchingArrow a) :=
  colimit.ι_desc _ _

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C] [HasPushouts C] in
/-- The lower lift retains the original left coefficient triangle on the full latching source. -/
theorem lowerLatchingMap_left (j : J) (l : LowerLift r sq (r.degree j)) :
    colimMap (r.latchingTransformation i j) ≫ lowerLatchingMap j l =
      latchingMap r A j ≫ t.app j := by
  apply colimit.hom_ext
  intro a
  rw [ι_colimMap_assoc, lowerLatchingMap_ι, latchingMap_ι_assoc r]
  change i.app a.obj.left.obj ≫ l.app a.obj.left.obj a.property ≫ X.map (r.latchingArrow a) =
    A.map (r.latchingArrow a) ≫ t.app j
  rw [l.left_assoc]
  exact (t.naturality (r.latchingArrow a)).symm

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C] [HasPushouts C] in
/-- The lower lift retains the original right coefficient triangle on the full latching source. -/
theorem lowerLatchingMap_right (j : J) (l : LowerLift r sq (r.degree j)) :
    lowerLatchingMap j l ≫ p.app j = latchingMap r B j ≫ b.app j := by
  apply colimit.hom_ext
  intro a
  rw [lowerLatchingMap_ι_assoc, latchingMap_ι_assoc r]
  rw [p.naturality, l.right_assoc]
  exact (b.naturality (r.latchingArrow a)).symm

/-- The smaller lift and original outgoing arrows give the complete matching cone at the next
object. -/
def lowerMatchingCone (j : J) (l : LowerLift r sq (r.degree j)) :
    Cone (r.matchingDiagram X j) where
  pt := B.obj j
  π.app a := B.map (r.matchingArrow a) ≫ l.app a.obj.right.obj a.property
  π.naturality a c f := by
    change 𝟙 _ ≫ (B.map (r.matchingArrow c) ≫ l.app c.obj.right.obj c.property) =
      (B.map (r.matchingArrow a) ≫ l.app a.obj.right.obj a.property) ≫
        X.map (r.matchingComparison f)
    rw [Category.id_comp, Category.assoc, ← l.naturality a.property c.property,
      ← Category.assoc, ← B.map_comp]
    congr 2
    exact (r.matchingArrow_comparison f).symm

/-- The next matching lift uses the universal property of the complete original matching diagram. -/
def lowerMatchingMap (j : J) (l : LowerLift r sq (r.degree j)) :
    B.obj j ⟶ limit (r.matchingDiagram X j) := limit.lift _ (lowerMatchingCone j l)

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPullbacks C] [HasPushouts C] in
@[reassoc]
theorem lowerMatchingMap_π (j : J) (l : LowerLift r sq (r.degree j)) (a : r.Matching j) :
    lowerMatchingMap j l ≫ limit.π (r.matchingDiagram X j) a =
      B.map (r.matchingArrow a) ≫ l.app a.obj.right.obj a.property := limit.lift_π _ _

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPullbacks C] [HasPushouts C] in
/-- The lower lift retains the original right coefficient triangle on the full matching source. -/
theorem lowerMatchingMap_right (j : J) (l : LowerLift r sq (r.degree j)) :
    lowerMatchingMap j l ≫ limMap (r.matchingTransformation p j) =
      b.app j ≫ matchingMap r Y j := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, limMap_π, lowerMatchingMap_π_assoc, Category.assoc,
    matchingMap_π r]
  change B.map (r.matchingArrow a) ≫ l.app a.obj.right.obj a.property ≫ p.app a.obj.right.obj =
    b.app j ≫ Y.map (r.matchingArrow a)
  rw [l.right]
  exact b.naturality (r.matchingArrow a)

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPullbacks C] [HasPushouts C] in
/-- The lower lift retains the original left coefficient triangle on the full matching source. -/
theorem lowerMatchingMap_left (j : J) (l : LowerLift r sq (r.degree j)) :
    i.app j ≫ lowerMatchingMap j l = t.app j ≫ matchingMap r X j := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, lowerMatchingMap_π, Category.assoc, matchingMap_π r]
  rw [← i.naturality_assoc, l.left]
  exact t.naturality (r.matchingArrow a)

omit [HasPullbacks C] [HasPushouts C] in
/-- Incoming and outgoing boundary comparisons agree by lower naturality on the original
composite arrow. -/
theorem lower_boundary_compatibility (j : J) (l : LowerLift r sq (r.degree j)) :
    lowerLatchingMap j l ≫ matchingMap r X j = latchingMap r B j ≫ lowerMatchingMap j l := by
  apply colimit.hom_ext
  intro a
  apply limit.hom_ext
  intro c
  simp only [Category.assoc, lowerLatchingMap_ι_assoc, matchingMap_π r,
    latchingMap_ι_assoc r, lowerMatchingMap_π]
  rw [← X.map_comp, ← B.map_comp_assoc]
  exact (l.naturality a.property c.property (r.latchingArrow a ≫ r.matchingArrow c)).symm

/-- The actual top map of the next coefficient corner square. -/
def cornerTop (j : J) (l : LowerLift r sq (r.degree j)) :
    pushout (latchingMap r A j) (colimMap (r.latchingTransformation i j)) ⟶ X.obj j :=
  pushout.desc (t.app j) (lowerLatchingMap j l) (lowerLatchingMap_left j l).symm

/-- The actual bottom map of the next coefficient corner square. -/
def cornerBottom (j : J) (l : LowerLift r sq (r.degree j)) :
    B.obj j ⟶ pullback (limMap (r.matchingTransformation p j)) (matchingMap r Y j) :=
  pullback.lift (lowerMatchingMap j l) (b.app j) (lowerMatchingMap_right j l)

/-- A smaller natural lift gives the complete original next latching--matching coefficient
square. -/
theorem cornerSquare (j : J) (l : LowerLift r sq (r.degree j)) :
    CommSq (cornerTop j l) (latchingCorner r i j) (matchingCorner r p j) (cornerBottom j l) := by
  constructor
  apply pullback.hom_ext
  · rw [Category.assoc, matchingCorner_fst r, Category.assoc, cornerBottom, pullback.lift_fst]
    apply pushout.hom_ext
    · rw [← Category.assoc, cornerTop, pushout.inl_desc, ← Category.assoc, latchingCorner_inl r]
      exact (lowerMatchingMap_left j l).symm
    · rw [← Category.assoc, cornerTop, pushout.inr_desc, ← Category.assoc, latchingCorner_inr r]
      exact lower_boundary_compatibility j l
  · rw [Category.assoc, matchingCorner_snd r, Category.assoc, cornerBottom, pullback.lift_snd]
    apply pushout.hom_ext
    · rw [← Category.assoc, cornerTop, pushout.inl_desc, ← Category.assoc, latchingCorner_inl r]
      exact congr_app sq.w j
    · rw [← Category.assoc, cornerTop, pushout.inr_desc, ← Category.assoc, latchingCorner_inr r]
      exact lowerLatchingMap_right j l

/-- The genuine coefficient lift at the next degree, with the same original corner maps. -/
def extendComponent (j : J) (l : LowerLift r sq (r.degree j))
    [HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)] : B.obj j ⟶ X.obj j :=
  (cornerSquare j l).lift

/-- The extended coefficient retains the original left factor equation. -/
theorem extendComponent_left (j : J) (l : LowerLift r sq (r.degree j))
    [HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)] :
    i.app j ≫ extendComponent j l = t.app j := by
  have h := congrArg (fun f =>
    pushout.inl (latchingMap r A j) (colimMap (r.latchingTransformation i j)) ≫ f)
    (cornerSquare j l).fac_left
  simpa only [← Category.assoc, latchingCorner_inl r, cornerTop, pushout.inl_desc,
    extendComponent] using h

/-- The extended coefficient retains the original right factor equation. -/
theorem extendComponent_right (j : J) (l : LowerLift r sq (r.degree j))
    [HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)] :
    extendComponent j l ≫ p.app j = b.app j := by
  have h := congrArg (fun f => f ≫
    pullback.snd (limMap (r.matchingTransformation p j)) (matchingMap r Y j))
    (cornerSquare j l).fac_right
  simpa only [Category.assoc, matchingCorner_snd r, cornerBottom, pullback.lift_snd,
    extendComponent] using h


/-- The coefficient extension retains the complete original latching boundary equation. -/
theorem extendComponent_latching (j : J) (l : LowerLift r sq (r.degree j))
    [HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)] :
    latchingMap r B j ≫ extendComponent j l = lowerLatchingMap j l := by
  have h := congrArg (fun f =>
    pushout.inr (latchingMap r A j) (colimMap (r.latchingTransformation i j)) ≫ f)
    (cornerSquare j l).fac_left
  simpa only [← Category.assoc, latchingCorner_inr r, cornerTop, pushout.inr_desc,
    extendComponent] using h

/-- The coefficient extension retains the complete original matching boundary equation. -/
theorem extendComponent_matching (j : J) (l : LowerLift r sq (r.degree j))
    [HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)] :
    extendComponent j l ≫ matchingMap r X j = lowerMatchingMap j l := by
  have h := congrArg (fun f => f ≫
    pullback.fst (limMap (r.matchingTransformation p j)) (matchingMap r Y j))
    (cornerSquare j l).fac_right
  simpa only [Category.assoc, matchingCorner_fst r, cornerBottom, pullback.lift_fst,
    extendComponent] using h

/-- Every original smaller incoming direct arrow commutes with the actual coefficient extension. -/
theorem extendComponent_direct (j : J) (l : LowerLift r sq (r.degree j))
    [HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)]
    {k : J} (hk : r.degree k < r.degree j) (f : k ⟶ j) (hf : r.direct f) :
    B.map f ≫ extendComponent j l = l.app k hk ≫ X.map f := by
  let a := r.latchingMk f hf hk
  have h := congrArg (fun g => colimit.ι (r.latchingDiagram B j) a ≫ g)
    (extendComponent_latching j l)
  rw [← Category.assoc, latchingMap_ι r, lowerLatchingMap_ι] at h
  dsimp only [latchingDiagram, Functor.comp_obj, latchingInclusion] at h
  simpa only [a, latchingArrow_mk, latchingSource_mk] using h

/-- Every original smaller outgoing inverse arrow commutes with the actual coefficient extension. -/
theorem extendComponent_inverse (j : J) (l : LowerLift r sq (r.degree j))
    [HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)]
    {k : J} (hk : r.degree k < r.degree j) (f : j ⟶ k) (hf : r.inverse f) :
    extendComponent j l ≫ X.map f = B.map f ≫ l.app k hk := by
  let a := r.matchingMk f hf hk
  have h := congrArg (fun g => g ≫ limit.π (r.matchingDiagram X j) a)
    (extendComponent_matching j l)
  rw [Category.assoc, matchingMap_π r, lowerMatchingMap_π] at h
  dsimp only [matchingDiagram, Functor.comp_obj, matchingInclusion] at h
  simpa only [a, matchingArrow_mk, matchingTarget_mk] using h

variable (r sq)

/-- The local recursion invariant retains both factor equations and every smaller direct/inverse
comparison. -/
private def ComponentSpec (i : A ⟶ B) (p : X ⟶ Y) (t : A ⟶ X) (b : B ⟶ Y)
  (o : ∀ j, Option (B.obj j ⟶ X.obj j)) (j
  : J) : Prop :=
  ∃ a, o j = some a ∧ i.app j ≫ a = t.app j ∧ a ≫ p.app j = b.app j ∧
    (∀ (k : J) (_ : r.degree k < r.degree j) (f : k ⟶ j), r.direct f →
      ∀ a', o k = some a' → B.map f ≫ a = a' ≫ X.map f) ∧
    (∀ (k : J) (_ : r.degree k < r.degree j) (f : j ⟶ k), r.inverse f →
      ∀ a', o k = some a' → a ≫ X.map f = B.map f ≫ a')

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPullbacks C] [HasPushouts C] in
/-- The target invariant gives naturality on any actual direct source arrow. -/
private theorem componentSpec_direct (o : ∀ j, Option (B.obj j ⟶ X.obj j))
    {j k : J} (hk : ComponentSpec r i p t b o k) (f : j ⟶ k) (hf : r.direct f)
    {a : B.obj j ⟶ X.obj j} {a' : B.obj k ⟶ X.obj k}
    (ha : o j = some a) (ha' : o k = some a') : B.map f ≫ a' = a ≫ X.map f := by
  rcases hk with ⟨c, hc, -, -, hd, -⟩
  have he : c = a' := Option.some.inj (hc.symm.trans ha')
  subst c
  by_cases h : r.degree j < r.degree k
  · exact hd j h f hf a ha
  · obtain ⟨e, he⟩ := r.direct_identity_of_not_lt f hf h
    subst k
    have he' : a = a' := Option.some.inj (ha.symm.trans ha')
    subst a'
    simp [he]

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPullbacks C] [HasPushouts C] in
/-- The source invariant gives naturality on any actual inverse source arrow. -/
private theorem componentSpec_inverse (o : ∀ j, Option (B.obj j ⟶ X.obj j))
    {j k : J} (hj : ComponentSpec r i p t b o j) (f : j ⟶ k) (hf : r.inverse f)
    {a : B.obj j ⟶ X.obj j} {a' : B.obj k ⟶ X.obj k}
    (ha : o j = some a) (ha' : o k = some a') : B.map f ≫ a' = a ≫ X.map f := by
  rcases hj with ⟨c, hc, -, -, -, hi⟩
  have he : c = a := Option.some.inj (hc.symm.trans ha)
  subst c
  by_cases h : r.degree k < r.degree j
  · exact (hi k h f hf a' ha').symm
  · obtain ⟨e, he⟩ := r.inverse_identity_of_not_lt f hf h
    subst k
    have he' : a = a' := Option.some.inj (ha.symm.trans ha')
    subst a'
    simp [he]

/-- Local invariants at smaller degrees form a genuine natural lift on the complete lower source. -/
private def lowerLiftOfSpecs (o : ∀ j, Option (B.obj j ⟶ X.obj j)) (d : D)
    (h : ∀ j, r.degree j < d → ComponentSpec r i p t b o j) : LowerLift r sq d where
  app j hj := (h j hj).choose
  left j hj := (h j hj).choose_spec.2.1
  right j hj := (h j hj).choose_spec.2.2.1
  naturality {j k} hj hk f := by
    have hm : r.degree (r.factor f).middle < d := (r.middle_le_source f).trans_lt hj
    have hi := componentSpec_inverse r o (h j hj) (r.factor f).inverseMap
      (r.factor f).inverse_mem (h j hj).choose_spec.1 (h _ hm).choose_spec.1
    have hd := componentSpec_direct r o (h k hk) (r.factor f).directMap
      (r.factor f).direct_mem (h _ hm).choose_spec.1 (h k hk).choose_spec.1
    rw [← (r.factor f).fac, B.map_comp, X.map_comp, Category.assoc, hd,
      ← Category.assoc, hi, Category.assoc]

/-- The checked local extension step. Its optional failure branch makes no existence assumption;
well founded induction proves that branch is never taken. -/
private def componentStep
    (hcorner : ∀ j, HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j))
    (j : J) (previous : ∀ k, r.degree k < r.degree j → Option (B.obj k ⟶ X.obj k)) :
    Option (B.obj j ⟶ X.obj j) := by
  classical
  exact if h : ∃ l : LowerLift r sq (r.degree j),
      ∀ k hk, previous k hk = some (l.app k hk) then
    let : HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j) := hcorner j
    some (extendComponent j h.choose)
  else none

/-- Actual well founded degree recursion of the original coefficient extension step. -/
private def components
    (hcorner : ∀ j, HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)) :
    ∀ j, Option (B.obj j ⟶ X.obj j) :=
  (InvImage.wf r.degree wellFounded_lt).fix (componentStep r sq hcorner)

/-- The whole recursive component is exactly the original step applied to its smaller actual
components. -/
private theorem components_eq
    (hcorner : ∀ j, HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)) (j : J) :
    components r sq hcorner j = componentStep r sq hcorner j
      (fun k _ => components r sq hcorner k) :=
  (InvImage.wf r.degree wellFounded_lt).fix_eq (componentStep r sq hcorner) j

/-- Every degree recursion step succeeds and retains all original component equations and
comparisons. -/
private theorem components_spec
    (hcorner : ∀ j, HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)) (j : J) :
    ComponentSpec r i p t b (components r sq hcorner) j := by
  classical
  induction j using (InvImage.wf r.degree wellFounded_lt).induction with
  | h j ih =>
    let l := lowerLiftOfSpecs r sq (components r sq hcorner) (r.degree j) ih
    have h : ∃ l : LowerLift r sq (r.degree j),
        ∀ k hk, components r sq hcorner k = some (l.app k hk) :=
      ⟨l, fun k hk => (ih k hk).choose_spec.1⟩
    let l' := h.choose
    let : HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j) := hcorner j
    refine ⟨extendComponent j l', ?_, extendComponent_left j l', extendComponent_right j l', ?_, ?_⟩
    · rw [components_eq, componentStep, dite_eq_left h]
    · intro k hk f hf a ha
      have he : l'.app k hk = a := Option.some.inj ((h.choose_spec k hk).symm.trans ha)
      rw [← he]
      exact extendComponent_direct j l' hk f hf
    · intro k hk f hf a ha
      have he : l'.app k hk = a := Option.some.inj ((h.choose_spec k hk).symm.trans ha)
      rw [← he]
      exact extendComponent_inverse j l' hk f hf

/-- The same recursively constructed coefficient lifts assemble to a natural transformation on
every source arrow. -/
@[no_expose] def liftTransformation
    (hcorner : ∀ j, HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)) : B ⟶ X where
  app j := by exact (components_spec r sq hcorner j).choose
  naturality _ _ f := by
    exact r.naturality_of_direct_inverse
      (fun a => (components_spec r sq hcorner a).choose)
      (fun {j k} g hg => componentSpec_direct r (components r sq hcorner)
        (components_spec r sq hcorner k) g hg
        (components_spec r sq hcorner j).choose_spec.1
          (components_spec r sq hcorner k).choose_spec.1)
      (fun {j k} g hg => componentSpec_inverse r (components r sq hcorner)
        (components_spec r sq hcorner j) g hg
        (components_spec r sq hcorner j).choose_spec.1
          (components_spec r sq hcorner k).choose_spec.1) f

/-- The full assembled lift has the unchanged original left and right factor equations. -/
def liftStruct
    (hcorner : ∀ j, HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j))
      : sq.LiftStruct where
  l := liftTransformation r sq hcorner
  fac_left := by
    ext j
    exact (components_spec r sq hcorner j).choose_spec.2.1
  fac_right := by
    ext j
    exact (components_spec r sq hcorner j).choose_spec.2.2.1

variable {r sq} in
/-- The ordinary Reedy lifting property follows from the original coefficient corner lifting
properties. -/
theorem hasLiftingProperty
    (hcorner : ∀ j, HasLiftingProperty (latchingCorner r i j) (matchingCorner r p j)) :
    HasLiftingProperty i p :=
  ⟨fun sq => CommSq.HasLift.mk' (liftStruct r sq hcorner)⟩

end CategoryTheory.ReedyStructure.Lifting

end ReedyPart1
