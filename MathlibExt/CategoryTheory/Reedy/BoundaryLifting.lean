/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.Boundary
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Original boundary scalar lifting and source class laws

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

namespace CategoryTheory.ReedyStructure.LatchingLift

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  {F G : J ⥤ C} (f : F ⟶ G) (j : J)
  (cF : Cocone (r.latchingDiagram F j)) (cG : Cocone (r.latchingDiagram G j))
  (p : cF.pt ⟶ cG.pt)

/-- A partial lift retains every original smaller incoming comparison. -/
structure LowerLift (d : D) where
  /-- The lift component at an incoming latching object of degree below `d`. -/
  app (a : r.Latching j) (ha : r.degree (r.latchingSource a) < d) :
    G.obj (r.latchingSource a) ⟶ cF.pt
  left (a : r.Latching j) (ha : r.degree (r.latchingSource a) < d) :
    f.app (r.latchingSource a) ≫ app a ha = cF.ι.app a
  right (a : r.Latching j) (ha : r.degree (r.latchingSource a) < d) :
    app a ha ≫ p = cG.ι.app a
  naturality {a b : r.Latching j}
    (ha : r.degree (r.latchingSource a) < d) (hb : r.degree (r.latchingSource b) < d)
    (g : a ⟶ b) : G.map (r.latchingComparison g) ≫ app b hb = app a ha

variable {f j cF cG p}

/-- A smaller coefficient has its original ordinary coefficient type. -/
def lowerComponent (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)))
    (b : r.Latching (r.latchingSource a)) : G.obj (r.latchingSource b) ⟶ cF.pt :=
  l.app (r.latchingCompose a b) (r.latchingCompose_lt a b)

/-- The typed smaller coefficient retains its original left factor equation. -/
theorem lowerComponent_left (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)))
    (b : r.Latching (r.latchingSource a)) :
    f.app (r.latchingSource b) ≫ lowerComponent r a l b = cF.ι.app (r.latchingCompose a b) :=
  l.left (r.latchingCompose a b) (r.latchingCompose_lt a b)

/-- The typed smaller coefficient retains its original right factor equation. -/
theorem lowerComponent_right (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)))
    (b : r.Latching (r.latchingSource a)) :
    lowerComponent r a l b ≫ p = cG.ι.app (r.latchingCompose a b) :=
  l.right (r.latchingCompose a b) (r.latchingCompose_lt a b)

/-- Restrict the complete smaller lift along actual composition with an incoming source arrow. -/
def lowerCocone (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a))) :
    Cocone (r.latchingDiagram G (r.latchingSource a)) where
  pt := cF.pt
  ι.app b := lowerComponent r a l b
  ι.naturality b c g := by
    change G.map (r.latchingComparison g) ≫
      lowerComponent r a l c = lowerComponent r a l b ≫ 𝟙 _
    rw [Category.comp_id]
    exact l.naturality (r.latchingCompose_lt a b) (r.latchingCompose_lt a c)
      (r.latchingComposeMap a g)

section Colimits

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The complete universal map of the same original lower lift cocone. -/
def lowerLatchingMap (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a))) :
    colimit (r.latchingDiagram G (r.latchingSource a)) ⟶ cF.pt :=
  colimit.desc _ (lowerCocone r a l)

@[reassoc]
theorem lowerLatchingMap_ι (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)))
    (b : r.Latching (r.latchingSource a)) :
    colimit.ι (r.latchingDiagram G (r.latchingSource a)) b ≫ lowerLatchingMap r a l =
      lowerComponent r a l b := colimit.ι_desc _ _

/-- The original left factor equations commute with the entire latching comparison. -/
theorem lowerLatchingMap_left (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a))) :
    latchingMap r F (r.latchingSource a) ≫ cF.ι.app a =
      colimMap (r.latchingTransformation f (r.latchingSource a)) ≫ lowerLatchingMap r a l := by
  apply colimit.hom_ext
  intro b
  rw [← Category.assoc, latchingMap_ι r, ← Category.assoc, ι_colimMap,
    Category.assoc, lowerLatchingMap_ι]
  change F.map (r.latchingArrow b) ≫ cF.ι.app a =
    f.app (r.latchingSource b) ≫ lowerComponent r a l b
  rw [lowerComponent_left]
  have h := cF.w (r.latchingComposeTo a b)
  change F.map (r.latchingArrow b) ≫ cF.ι.app a = cF.ι.app (r.latchingCompose a b) at h
  exact h

/-- The original right factor equations commute with the entire latching map. -/
theorem lowerLatchingMap_right (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a))) :
    lowerLatchingMap r a l ≫ p =
      latchingMap r G (r.latchingSource a) ≫ cG.ι.app a := by
  apply colimit.hom_ext
  intro b
  rw [← Category.assoc, lowerLatchingMap_ι, lowerComponent_right,
    ← Category.assoc, latchingMap_ι r]
  have h := cG.w (r.latchingComposeTo a b)
  change G.map (r.latchingArrow b) ≫ cG.ι.app a = cG.ι.app (r.latchingCompose a b) at h
  exact h.symm

variable [HasPushouts C]

/-- The next source square uses the same original relative latching pushout. -/
def cornerTop (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a))) :
    pushout (latchingMap r F (r.latchingSource a))
      (colimMap (r.latchingTransformation f (r.latchingSource a))) ⟶ cF.pt :=
  pushout.desc (cF.ι.app a) (lowerLatchingMap r a l) (lowerLatchingMap_left r a l)

/-- The original cocone square induces a square on the exact original coefficient corner. -/
theorem cornerSquare
    (w : ∀ a : r.Latching j, cF.ι.app a ≫ p = f.app (r.latchingSource a) ≫ cG.ι.app a)
    (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a))) :
    CommSq (cornerTop r a l) (latchingCorner r f (r.latchingSource a)) p (cG.ι.app a) := by
  constructor
  apply pushout.hom_ext
  · rw [← Category.assoc, cornerTop, pushout.inl_desc,
      ← Category.assoc, latchingCorner_inl r]
    exact w a
  · rw [← Category.assoc, cornerTop, pushout.inr_desc,
      ← Category.assoc, latchingCorner_inr r]
    exact lowerLatchingMap_right r a l

variable
  (w : ∀ a : r.Latching j, cF.ι.app a ≫ p = f.app (r.latchingSource a) ≫ cG.ι.app a)

/-- The original lower corner lift extends the coefficient at the next actual source degree. -/
def extendComponent (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)))
    [HasLiftingProperty (latchingCorner r f (r.latchingSource a)) p] :
    G.obj (r.latchingSource a) ⟶ cF.pt := (cornerSquare r w a l).lift

/-- The extended coefficient keeps its original left factor equation. -/
theorem extendComponent_left (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)))
    [HasLiftingProperty (latchingCorner r f (r.latchingSource a)) p] :
    f.app (r.latchingSource a) ≫ extendComponent r w a l = cF.ι.app a := by
  have h := congrArg (fun g =>
    pushout.inl (latchingMap r F (r.latchingSource a))
      (colimMap (r.latchingTransformation f (r.latchingSource a))) ≫ g)
    (cornerSquare r w a l).fac_left
  simpa only [← Category.assoc, latchingCorner_inl r, cornerTop,
    pushout.inl_desc, extendComponent] using h

/-- The extended coefficient keeps its original right factor equation. -/
theorem extendComponent_right (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)))
    [HasLiftingProperty (latchingCorner r f (r.latchingSource a)) p] :
    extendComponent r w a l ≫ p = cG.ι.app a := (cornerSquare r w a l).fac_right

/-- The extension keeps the entire original smaller latching boundary. -/
theorem extendComponent_latching (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)))
    [HasLiftingProperty (latchingCorner r f (r.latchingSource a)) p] :
    latchingMap r G (r.latchingSource a) ≫ extendComponent r w a l = lowerLatchingMap r a l := by
  have h := congrArg (fun g =>
    pushout.inr (latchingMap r F (r.latchingSource a))
      (colimMap (r.latchingTransformation f (r.latchingSource a))) ≫ g)
    (cornerSquare r w a l).fac_left
  simpa only [← Category.assoc, latchingCorner_inr r, cornerTop,
    pushout.inr_desc, extendComponent] using h

/-- Every original smaller incoming comparison commutes with the actual extension. -/
theorem extendComponent_comparison (a : r.Latching j)
    (l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)))
    [HasLiftingProperty (latchingCorner r f (r.latchingSource a)) p]
    {b : r.Latching j} (hb : r.degree (r.latchingSource b) < r.degree (r.latchingSource a))
    (g : b ⟶ a) : G.map (r.latchingComparison g) ≫ extendComponent r w a l = l.app b hb := by
  let c := r.latchingMk (r.latchingComparison g) (r.latchingComparison_mem g) hb
  have h := congrArg (fun k => colimit.ι (r.latchingDiagram G (r.latchingSource a)) c ≫ k)
    (extendComponent_latching r w a l)
  rw [← Category.assoc, latchingMap_ι r, lowerLatchingMap_ι] at h
  change G.map (r.latchingComparison g) ≫ extendComponent r w a l = lowerComponent r a l c at h
  have e : r.latchingCompose a c = b := r.latchingCompose_comparison g hb
  let app : (z : {z : r.Latching j // r.degree (r.latchingSource z) <
      r.degree (r.latchingSource a)}) → G.obj (r.latchingSource z.val) ⟶ cF.pt :=
    fun z => l.app z.val z.property
  have es : (⟨r.latchingCompose a c, r.latchingCompose_lt a c⟩ :
      {z : r.Latching j // r.degree (r.latchingSource z) < r.degree (r.latchingSource a)}) =
      ⟨b, hb⟩ := Subtype.ext e
  have hApp : ∀ z z', z = z' → HEq (app z) (app z') := by
    intro z z' hz
    cases hz
    rfl
  have he := hApp _ _ es
  have he' : lowerComponent r a l c = l.app b hb := eq_of_heq he
  exact h.trans he'

end Colimits

/-- The induction invariant retains every factor equation and smaller original comparison. -/
def ComponentSpec (o : ∀ a : r.Latching j, Option (G.obj (r.latchingSource a) ⟶ cF.pt))
    (a : r.Latching j) : Prop :=
  ∃ x, o a = some x ∧ f.app (r.latchingSource a) ≫ x = cF.ι.app a ∧
    x ≫ p = cG.ι.app a ∧
    ∀ (b : r.Latching j) (_ : r.degree (r.latchingSource b) < r.degree (r.latchingSource a))
      (g : b ⟶ a) (y : G.obj (r.latchingSource b) ⟶ cF.pt),
      o b = some y → G.map (r.latchingComparison g) ≫ x = y

/-- Local invariants give naturality for every actual incoming comparison, including identities. -/
theorem componentSpec_naturality
    (o : ∀ a : r.Latching j, Option (G.obj (r.latchingSource a) ⟶ cF.pt))
    {a b : r.Latching j} (hb : ComponentSpec r (f := f) (cG := cG) (p := p) o b)
    (g : a ⟶ b) {x : G.obj (r.latchingSource a) ⟶ cF.pt}
    {y : G.obj (r.latchingSource b) ⟶ cF.pt} (hx : o a = some x) (hy : o b = some y) :
    G.map (r.latchingComparison g) ≫ y = x := by
  rcases hb with ⟨z, hz, -, -, hn⟩
  have he : z = y := Option.some.inj (hz.symm.trans hy)
  subst z
  by_cases h : r.degree (r.latchingSource a) < r.degree (r.latchingSource b)
  · exact hn a h g x hx
  · obtain ⟨e, hg⟩ := r.latchingComparison_identity_of_not_lt g h
    subst b
    have he' : x = y := Option.some.inj (hx.symm.trans hy)
    subst y
    simp [hg]

/-- All smaller invariants assemble a complete lift on the actual lower incoming source. -/
def lowerLiftOfSpecs
    (o : ∀ a : r.Latching j, Option (G.obj (r.latchingSource a) ⟶ cF.pt)) (d : D)
    (h : ∀ a : r.Latching j, r.degree (r.latchingSource a) < d →
      ComponentSpec r (f := f) (cG := cG) (p := p) o a) : LowerLift r f j cF cG p d where
  app a ha := (h a ha).choose
  left a ha := (h a ha).choose_spec.2.1
  right a ha := (h a ha).choose_spec.2.2.1
  naturality ha hb g := componentSpec_naturality r o (h _ hb) g
    (h _ ha).choose_spec.1 (h _ hb).choose_spec.1

section Construction

variable [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]
  (w : ∀ a : r.Latching j, cF.ι.app a ≫ p = f.app (r.latchingSource a) ≫ cG.ι.app a)

/-- The actual local extension step. Well founded induction proves its failure branch impossible. -/
def componentStep
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p)
    (a : r.Latching j)
    (previous : ∀ b : r.Latching j, r.degree (r.latchingSource b) <
      r.degree (r.latchingSource a) → Option (G.obj (r.latchingSource b) ⟶ cF.pt)) :
    Option (G.obj (r.latchingSource a) ⟶ cF.pt) := by
  classical
  exact if h : ∃ l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)),
      ∀ b hb, previous b hb = some (l.app b hb) then
    let : HasLiftingProperty (latchingCorner r f (r.latchingSource a)) p :=
      hcorner (r.latchingSource a) a.property
    some (extendComponent r w a h.choose)
  else none

/-- Well founded recursion on the original domains of all incoming source triangles. -/
def components
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p) :
    ∀ a : r.Latching j, Option (G.obj (r.latchingSource a) ⟶ cF.pt) :=
  (InvImage.wf (fun a : r.Latching j => r.degree (r.latchingSource a)) wellFounded_lt).fix
    (componentStep r w hcorner)

/-- The recursive coefficient is the same original step applied to all its smaller coefficients. -/
theorem components_eq
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p)
    (a : r.Latching j) :
    components r w hcorner a = componentStep r w hcorner a
      (fun b _ => components r w hcorner b) :=
  (InvImage.wf (fun a : r.Latching j => r.degree (r.latchingSource a)) wellFounded_lt).fix_eq
    (componentStep r w hcorner) a

/-- Every source degree succeeds with both original factor equations and all smaller comparisons. -/
theorem components_spec
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p)
    (a : r.Latching j) :
    ComponentSpec r (f := f) (cG := cG) (p := p) (components r w hcorner) a := by
  classical
  induction a using
    (InvImage.wf (fun a : r.Latching j => r.degree (r.latchingSource a))
      wellFounded_lt).induction with
  | h a ih =>
    let l := lowerLiftOfSpecs r (components r w hcorner) (r.degree (r.latchingSource a)) ih
    have h : ∃ l : LowerLift r f j cF cG p (r.degree (r.latchingSource a)),
        ∀ b hb, components r w hcorner b = some (l.app b hb) :=
      ⟨l, fun b hb => (ih b hb).choose_spec.1⟩
    let l' := h.choose
    let : HasLiftingProperty (latchingCorner r f (r.latchingSource a)) p :=
      hcorner (r.latchingSource a) a.property
    refine ⟨extendComponent r w a l', ?_, extendComponent_left r w a l',
      extendComponent_right r w a l', ?_⟩
    · rw [components_eq, componentStep, dite_eq_left h]
    · intro b hb g y hy
      have he : l'.app b hb = y := Option.some.inj ((h.choose_spec b hb).symm.trans hy)
      rw [← he]
      exact extendComponent_comparison r w a l' hb g

/-- The same actual recursive coefficients form a complete cocone on the original latching
source. -/
def liftCocone
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p) :
    Cocone (r.latchingDiagram G j) where
  pt := cF.pt
  ι.app a := (components_spec r w hcorner a).choose
  ι.naturality a b g := by
    change G.map (r.latchingComparison g) ≫ (components_spec r w hcorner b).choose =
      (components_spec r w hcorner a).choose ≫ 𝟙 _
    rw [Category.comp_id]
    exact componentSpec_naturality r (components r w hcorner) (components_spec r w hcorner b) g
      (components_spec r w hcorner a).choose_spec.1 (components_spec r w hcorner b).choose_spec.1

/-- Every original left cocone coefficient factors through the same constructed lift. -/
theorem liftCocone_left
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p)
    (a : r.Latching j) :
    f.app (r.latchingSource a) ≫ (liftCocone r w hcorner).ι.app a = cF.ι.app a :=
  (components_spec r w hcorner a).choose_spec.2.1

/-- Every original right cocone coefficient factors through the same constructed lift. -/
theorem liftCocone_right
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p)
    (a : r.Latching j) : (liftCocone r w hcorner).ι.app a ≫ p = cG.ι.app a :=
  (components_spec r w hcorner a).choose_spec.2.2.1

end Construction

end CategoryTheory.ReedyStructure.LatchingLift

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]
  {F G : J ⥤ C} (f : F ⟶ G) (j : J)

/-- Any caller original colimit square has a lift from the actual lower coefficient corners. -/
def latchingComparisonWithLiftStruct
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    {U V : C} (p : U ⟶ V) {t : cX.pt ⟶ U} {b : cY.pt ⟶ V}
    (sq : CommSq t (r.latchingComparisonWith f j cX hX cY) p b)
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p) :
    sq.LiftStruct := by
  let u := cX.extend t
  let v := cY.extend b
  have w : ∀ a : r.Latching j, u.ι.app a ≫ p = f.app (r.latchingSource a) ≫ v.ι.app a := by
    intro a
    change (cX.ι.app a ≫ t) ≫ p = f.app (r.latchingSource a) ≫ (cY.ι.app a ≫ b)
    rw [Category.assoc, sq.w, ← Category.assoc, r.latchingComparisonWith_ι, Category.assoc]
  let l := LatchingLift.liftCocone r (f := f) (j := j) (cF := u) (cG := v) (p := p) w hcorner
  let m : cY.pt ⟶ U := hY.desc l
  let q : ∀ a : r.Latching j, G.obj (r.latchingSource a) ⟶ U := fun a => l.ι.app a
  let x : ∀ a : r.Latching j, F.obj (r.latchingSource a) ⟶ cX.pt := fun a => cX.ι.app a
  let y : ∀ a : r.Latching j, G.obj (r.latchingSource a) ⟶ cY.pt := fun a => cY.ι.app a
  have hm (a : r.Latching j) : y a ≫ m = q a := hY.fac l a
  have hxy (a : r.Latching j) : x a ≫ r.latchingComparisonWith f j cX hX cY =
      f.app (r.latchingSource a) ≫ y a := r.latchingComparisonWith_ι f j cX hX cY a
  have hqLeft (a : r.Latching j) : f.app (r.latchingSource a) ≫ q a = x a ≫ t :=
    LatchingLift.liftCocone_left r (f := f) (j := j) (cF := u) (cG := v) (p := p) w hcorner a
  have hqRight (a : r.Latching j) : q a ≫ p = y a ≫ b :=
    LatchingLift.liftCocone_right r (f := f) (j := j) (cF := u) (cG := v) (p := p) w hcorner a
  refine { l := m, fac_left := ?_, fac_right := ?_ }
  · apply hX.hom_ext
    intro a
    change x a ≫ r.latchingComparisonWith f j cX hX cY ≫ m = x a ≫ t
    rw [← Category.assoc, hxy, Category.assoc, hm, hqLeft]
  · apply hY.hom_ext
    intro a
    change y a ≫ m ≫ p = y a ≫ b
    rw [← Category.assoc, hm, hqRight]

/-- The full original caller latching comparison has the coefficient lifting property. -/
theorem latchingComparisonWith_hasLiftingProperty
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    {U V : C} (p : U ⟶ V)
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p) :
    HasLiftingProperty (r.latchingComparisonWith f j cX hX cY) p :=
  ⟨fun sq => CommSq.HasLift.mk' (latchingComparisonWithLiftStruct r f j cX hX cY hY p sq hcorner)⟩

omit [HasPushouts C] in
/-- The comparison between the canonical original cocones is the original colimit map. -/
theorem latchingComparisonWith_canonical :
    r.latchingComparisonWith f j (colimit.cocone (r.latchingDiagram F j))
      (colimit.isColimit (r.latchingDiagram F j)) (colimit.cocone (r.latchingDiagram G j)) =
      colimMap (r.latchingTransformation f j) := by
  apply colimit.hom_ext
  intro a
  rw [ι_colimMap]
  exact r.latchingComparisonWith_ι f j (colimit.cocone _) (colimit.isColimit _)
    (colimit.cocone _) a

/-- The original canonical latching colimit map has the lower coefficient lifting property. -/
theorem latchingColimMap_hasLiftingProperty {U V : C} (p : U ⟶ V)
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty (latchingCorner r f k) p) :
    HasLiftingProperty (colimMap (r.latchingTransformation f j)) p := by
  rw [← latchingComparisonWith_canonical r f j]
  exact latchingComparisonWith_hasLiftingProperty r f j
    (colimit.cocone _) (colimit.isColimit _) (colimit.cocone _) (colimit.isColimit _) p hcorner

end CategoryTheory.ReedyStructure

end ReedyPart1

section ReedyPart2

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure.MatchingLift

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  {F G : J ⥤ C} (f : F ⟶ G) (j : J)
  (cF : Cone (r.matchingDiagram F j)) (cG : Cone (r.matchingDiagram G j))
  (i : cF.pt ⟶ cG.pt)

/-- A partial lift retains every original smaller outgoing comparison. -/
structure LowerLift (d : D) where
  /-- The lift component at an outgoing matching object of degree below `d`. -/
  app (a : r.Matching j) (ha : r.degree (r.matchingTarget a) < d) :
    cG.pt ⟶ F.obj (r.matchingTarget a)
  left (a : r.Matching j) (ha : r.degree (r.matchingTarget a) < d) :
    i ≫ app a ha = cF.π.app a
  right (a : r.Matching j) (ha : r.degree (r.matchingTarget a) < d) :
    app a ha ≫ f.app (r.matchingTarget a) = cG.π.app a
  naturality {a b : r.Matching j}
    (ha : r.degree (r.matchingTarget a) < d) (hb : r.degree (r.matchingTarget b) < d)
    (g : a ⟶ b) : app a ha ≫ F.map (r.matchingComparison g) = app b hb

variable {f j cF cG i}

/-- A smaller coefficient has its original ordinary coefficient type. -/
def lowerComponent (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)))
    (b : r.Matching (r.matchingTarget a)) : cG.pt ⟶ F.obj (r.matchingTarget b) :=
  l.app (r.matchingCompose a b) (r.matchingCompose_lt a b)

/-- The typed smaller coefficient retains its original left factor equation. -/
theorem lowerComponent_left (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)))
    (b : r.Matching (r.matchingTarget a)) :
    i ≫ lowerComponent r a l b = cF.π.app (r.matchingCompose a b) :=
  l.left (r.matchingCompose a b) (r.matchingCompose_lt a b)

/-- The typed smaller coefficient retains its original right factor equation. -/
theorem lowerComponent_right (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)))
    (b : r.Matching (r.matchingTarget a)) :
    lowerComponent r a l b ≫ f.app (r.matchingTarget b) = cG.π.app (r.matchingCompose a b) :=
  l.right (r.matchingCompose a b) (r.matchingCompose_lt a b)

/-- Restrict the complete smaller lift along actual composition with an outgoing source arrow. -/
def lowerCone (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a))) :
    Cone (r.matchingDiagram F (r.matchingTarget a)) where
  pt := cG.pt
  π.app b := lowerComponent r a l b
  π.naturality b c g := by
    change 𝟙 _ ≫ lowerComponent r a l c =
      lowerComponent r a l b ≫ F.map (r.matchingComparison g)
    rw [Category.id_comp]
    exact (l.naturality (r.matchingCompose_lt a b) (r.matchingCompose_lt a c)
      (r.matchingComposeMap a g)).symm

section Limits

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The complete universal map of the same original lower lift cone. -/
def lowerMatchingMap (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a))) :
    cG.pt ⟶ limit (r.matchingDiagram F (r.matchingTarget a)) :=
  limit.lift _ (lowerCone r a l)

@[reassoc]
theorem lowerMatchingMap_π (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)))
    (b : r.Matching (r.matchingTarget a)) :
    lowerMatchingMap r a l ≫ limit.π (r.matchingDiagram F (r.matchingTarget a)) b =
      lowerComponent r a l b := limit.lift_π _ _

/-- The original left factor equations commute with the entire matching map. -/
theorem lowerMatchingMap_left (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a))) :
    i ≫ lowerMatchingMap r a l =
      cF.π.app a ≫ matchingMap r F (r.matchingTarget a) := by
  apply limit.hom_ext
  intro b
  rw [Category.assoc, lowerMatchingMap_π, lowerComponent_left,
    Category.assoc, matchingMap_π r]
  have h := cF.w (r.matchingToCompose a b)
  change cF.π.app a ≫ F.map (r.matchingArrow b) = cF.π.app (r.matchingCompose a b) at h
  exact h.symm

/-- The original right factor equations commute with the entire matching comparison. -/
theorem lowerMatchingMap_right (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a))) :
    lowerMatchingMap r a l ≫ limMap (r.matchingTransformation f (r.matchingTarget a)) =
      cG.π.app a ≫ matchingMap r G (r.matchingTarget a) := by
  apply limit.hom_ext
  intro b
  rw [Category.assoc, limMap_π, ← Category.assoc, lowerMatchingMap_π,
    Category.assoc, matchingMap_π r]
  change lowerComponent r a l b ≫ f.app (r.matchingTarget b) =
    cG.π.app a ≫ G.map (r.matchingArrow b)
  rw [lowerComponent_right]
  have h := cG.w (r.matchingToCompose a b)
  change cG.π.app a ≫ G.map (r.matchingArrow b) = cG.π.app (r.matchingCompose a b) at h
  exact h.symm

variable [HasPullbacks C]

/-- The next source square uses the same original relative matching pullback. -/
def cornerBottom (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a))) :
    cG.pt ⟶ pullback (limMap (r.matchingTransformation f (r.matchingTarget a)))
      (matchingMap r G (r.matchingTarget a)) :=
  pullback.lift (lowerMatchingMap r a l) (cG.π.app a) (lowerMatchingMap_right r a l)

/-- The original cone square induces a square on the exact original coefficient corner. -/
theorem cornerSquare
    (w : ∀ a : r.Matching j, i ≫ cG.π.app a = cF.π.app a ≫ f.app (r.matchingTarget a))
    (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a))) :
    CommSq (cF.π.app a) i (matchingCorner r f (r.matchingTarget a)) (cornerBottom r a l) := by
  constructor
  apply pullback.hom_ext
  · rw [Category.assoc, matchingCorner_fst r, Category.assoc,
      cornerBottom, pullback.lift_fst]
    exact (lowerMatchingMap_left r a l).symm
  · rw [Category.assoc, matchingCorner_snd r, Category.assoc,
      cornerBottom, pullback.lift_snd]
    exact (w a).symm

variable
  (w : ∀ a : r.Matching j, i ≫ cG.π.app a = cF.π.app a ≫ f.app (r.matchingTarget a))

/-- The original lower corner lift extends the coefficient at the next actual target degree. -/
def extendComponent (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)))
    [HasLiftingProperty i (matchingCorner r f (r.matchingTarget a))] :
    cG.pt ⟶ F.obj (r.matchingTarget a) := (cornerSquare r w a l).lift

/-- The extended coefficient keeps its original left factor equation. -/
theorem extendComponent_left (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)))
    [HasLiftingProperty i (matchingCorner r f (r.matchingTarget a))] :
    i ≫ extendComponent r w a l = cF.π.app a := (cornerSquare r w a l).fac_left

/-- The extended coefficient keeps its original right factor equation. -/
theorem extendComponent_right (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)))
    [HasLiftingProperty i (matchingCorner r f (r.matchingTarget a))] :
    extendComponent r w a l ≫ f.app (r.matchingTarget a) = cG.π.app a := by
  have h := congrArg (fun g => g ≫
    pullback.snd (limMap (r.matchingTransformation f (r.matchingTarget a)))
      (matchingMap r G (r.matchingTarget a))) (cornerSquare r w a l).fac_right
  simpa only [Category.assoc, matchingCorner_snd r, cornerBottom,
    pullback.lift_snd, extendComponent] using h

/-- The extension keeps the entire original smaller matching boundary. -/
theorem extendComponent_matching (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)))
    [HasLiftingProperty i (matchingCorner r f (r.matchingTarget a))] :
    extendComponent r w a l ≫ matchingMap r F (r.matchingTarget a) = lowerMatchingMap r a l := by
  have h := congrArg (fun g => g ≫
    pullback.fst (limMap (r.matchingTransformation f (r.matchingTarget a)))
      (matchingMap r G (r.matchingTarget a))) (cornerSquare r w a l).fac_right
  simpa only [Category.assoc, matchingCorner_fst r, cornerBottom,
    pullback.lift_fst, extendComponent] using h

/-- Every original smaller outgoing comparison commutes with the actual extension. -/
theorem extendComponent_comparison (a : r.Matching j)
    (l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)))
    [HasLiftingProperty i (matchingCorner r f (r.matchingTarget a))]
    {b : r.Matching j} (hb : r.degree (r.matchingTarget b) < r.degree (r.matchingTarget a))
    (g : a ⟶ b) : extendComponent r w a l ≫ F.map (r.matchingComparison g) = l.app b hb := by
  let c := r.matchingMk (r.matchingComparison g) (r.matchingComparison_mem g) hb
  have h := congrArg (fun k => k ≫ limit.π (r.matchingDiagram F (r.matchingTarget a)) c)
    (extendComponent_matching r w a l)
  rw [Category.assoc, matchingMap_π r, lowerMatchingMap_π] at h
  change extendComponent r w a l ≫ F.map (r.matchingComparison g) = lowerComponent r a l c at h
  have e : r.matchingCompose a c = b := r.matchingCompose_comparison g hb
  let app : (z : {z : r.Matching j // r.degree (r.matchingTarget z) <
      r.degree (r.matchingTarget a)}) → cG.pt ⟶ F.obj (r.matchingTarget z.val) :=
    fun z => l.app z.val z.property
  have es : (⟨r.matchingCompose a c, r.matchingCompose_lt a c⟩ :
      {z : r.Matching j // r.degree (r.matchingTarget z) < r.degree (r.matchingTarget a)}) =
      ⟨b, hb⟩ := Subtype.ext e
  have hApp : ∀ z z', z = z' → HEq (app z) (app z') := by
    intro z z' hz
    cases hz
    rfl
  have he := hApp _ _ es
  have he' : lowerComponent r a l c = l.app b hb := eq_of_heq he
  exact h.trans he'

end Limits

/-- The induction invariant retains every factor equation and smaller original comparison. -/
def ComponentSpec (o : ∀ a : r.Matching j, Option (cG.pt ⟶ F.obj (r.matchingTarget a)))
    (a : r.Matching j) : Prop :=
  ∃ x, o a = some x ∧ i ≫ x = cF.π.app a ∧
    x ≫ f.app (r.matchingTarget a) = cG.π.app a ∧
    ∀ (b : r.Matching j) (_ : r.degree (r.matchingTarget b) < r.degree (r.matchingTarget a))
      (g : a ⟶ b) (y : cG.pt ⟶ F.obj (r.matchingTarget b)),
      o b = some y → x ≫ F.map (r.matchingComparison g) = y

/-- Local invariants give naturality for every actual outgoing comparison, including identities. -/
theorem componentSpec_naturality
    (o : ∀ a : r.Matching j, Option (cG.pt ⟶ F.obj (r.matchingTarget a)))
    {a b : r.Matching j} (ha : ComponentSpec r (f := f) (cF := cF) (i := i) o a)
    (g : a ⟶ b) {x : cG.pt ⟶ F.obj (r.matchingTarget a)}
    {y : cG.pt ⟶ F.obj (r.matchingTarget b)} (hx : o a = some x) (hy : o b = some y) :
    x ≫ F.map (r.matchingComparison g) = y := by
  rcases ha with ⟨z, hz, -, -, hn⟩
  have he : z = x := Option.some.inj (hz.symm.trans hx)
  subst z
  by_cases h : r.degree (r.matchingTarget b) < r.degree (r.matchingTarget a)
  · exact hn b h g y hy
  · obtain ⟨e, hg⟩ := r.matchingComparison_identity_of_not_lt g h
    subst b
    have he' : x = y := Option.some.inj (hx.symm.trans hy)
    subst y
    simp [hg]

/-- All smaller invariants assemble a complete lift on the actual lower outgoing source. -/
def lowerLiftOfSpecs
    (o : ∀ a : r.Matching j, Option (cG.pt ⟶ F.obj (r.matchingTarget a))) (d : D)
    (h : ∀ a : r.Matching j, r.degree (r.matchingTarget a) < d →
      ComponentSpec r (f := f) (cF := cF) (i := i) o a) : LowerLift r f j cF cG i d where
  app a ha := (h a ha).choose
  left a ha := (h a ha).choose_spec.2.1
  right a ha := (h a ha).choose_spec.2.2.1
  naturality ha hb g := componentSpec_naturality r o (h _ ha) g
    (h _ ha).choose_spec.1 (h _ hb).choose_spec.1

section Construction

variable [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]
  (w : ∀ a : r.Matching j, i ≫ cG.π.app a = cF.π.app a ≫ f.app (r.matchingTarget a))

/-- The actual local extension step. Well founded induction proves its failure branch impossible. -/
def componentStep
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k))
    (a : r.Matching j)
    (previous : ∀ b : r.Matching j, r.degree (r.matchingTarget b) <
      r.degree (r.matchingTarget a) → Option (cG.pt ⟶ F.obj (r.matchingTarget b))) :
    Option (cG.pt ⟶ F.obj (r.matchingTarget a)) := by
  classical
  exact if h : ∃ l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)),
      ∀ b hb, previous b hb = some (l.app b hb) then
    let : HasLiftingProperty i (matchingCorner r f (r.matchingTarget a)) :=
      hcorner (r.matchingTarget a) a.property
    some (extendComponent r w a h.choose)
  else none

/-- Well founded recursion on the original codomains of all outgoing source triangles. -/
def components
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k)) :
    ∀ a : r.Matching j, Option (cG.pt ⟶ F.obj (r.matchingTarget a)) :=
  (InvImage.wf (fun a : r.Matching j => r.degree (r.matchingTarget a)) wellFounded_lt).fix
    (componentStep r w hcorner)

/-- The recursive coefficient is the same original step applied to all its smaller coefficients. -/
theorem components_eq
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k))
    (a : r.Matching j) :
    components r w hcorner a = componentStep r w hcorner a
      (fun b _ => components r w hcorner b) :=
  (InvImage.wf (fun a : r.Matching j => r.degree (r.matchingTarget a)) wellFounded_lt).fix_eq
    (componentStep r w hcorner) a

/-- Every target degree succeeds with both original factor equations and all smaller comparisons. -/
theorem components_spec
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k))
    (a : r.Matching j) :
    ComponentSpec r (f := f) (cF := cF) (i := i) (components r w hcorner) a := by
  classical
  induction a using
    (InvImage.wf (fun a : r.Matching j => r.degree (r.matchingTarget a))
      wellFounded_lt).induction with
  | h a ih =>
    let l := lowerLiftOfSpecs r (components r w hcorner) (r.degree (r.matchingTarget a)) ih
    have h : ∃ l : LowerLift r f j cF cG i (r.degree (r.matchingTarget a)),
        ∀ b hb, components r w hcorner b = some (l.app b hb) :=
      ⟨l, fun b hb => (ih b hb).choose_spec.1⟩
    let l' := h.choose
    let : HasLiftingProperty i (matchingCorner r f (r.matchingTarget a)) :=
      hcorner (r.matchingTarget a) a.property
    refine ⟨extendComponent r w a l', ?_, extendComponent_left r w a l',
      extendComponent_right r w a l', ?_⟩
    · rw [components_eq, componentStep, dite_eq_left h]
    · intro b hb g y hy
      have he : l'.app b hb = y := Option.some.inj ((h.choose_spec b hb).symm.trans hy)
      rw [← he]
      exact extendComponent_comparison r w a l' hb g

/-- The same actual recursive coefficients form a complete cone on the original matching source. -/
def liftCone
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k)) :
    Cone (r.matchingDiagram F j) where
  pt := cG.pt
  π.app a := (components_spec r w hcorner a).choose
  π.naturality a b g := by
    change 𝟙 _ ≫ (components_spec r w hcorner b).choose =
      (components_spec r w hcorner a).choose ≫ F.map (r.matchingComparison g)
    rw [Category.id_comp]
    exact (componentSpec_naturality r (components r w hcorner) (components_spec r w hcorner a) g
      (components_spec r w hcorner a).choose_spec.1
        (components_spec r w hcorner b).choose_spec.1).symm

/-- Every original left cone coefficient factors through the same constructed lift. -/
theorem liftCone_left
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k))
    (a : r.Matching j) : i ≫ (liftCone r w hcorner).π.app a = cF.π.app a :=
  (components_spec r w hcorner a).choose_spec.2.1

/-- Every original right cone coefficient factors through the same constructed lift. -/
theorem liftCone_right
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k))
    (a : r.Matching j) :
    (liftCone r w hcorner).π.app a ≫ f.app (r.matchingTarget a) = cG.π.app a :=
  (components_spec r w hcorner a).choose_spec.2.2.1

end Construction

end CategoryTheory.ReedyStructure.MatchingLift

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]
  {F G : J ⥤ C} (f : F ⟶ G) (j : J)

/-- Any caller original limit square has a lift from the actual lower coefficient corners. -/
def matchingComparisonWithLiftStruct
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    {U V : C} (i : U ⟶ V) {t : U ⟶ cX.pt} {b : V ⟶ cY.pt}
    (sq : CommSq t i (r.matchingComparisonWith f j cX cY hY) b)
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k)) :
    sq.LiftStruct := by
  let u := cX.extend t
  let v := cY.extend b
  have w : ∀ a : r.Matching j, i ≫ v.π.app a = u.π.app a ≫ f.app (r.matchingTarget a) := by
    intro a
    change i ≫ (b ≫ cY.π.app a) = (t ≫ cX.π.app a) ≫ f.app (r.matchingTarget a)
    rw [← Category.assoc, ← sq.w, Category.assoc, r.matchingComparisonWith_π, ← Category.assoc]
  let l := MatchingLift.liftCone r (f := f) (j := j) (cF := u) (cG := v) (i := i) w hcorner
  let m : V ⟶ cX.pt := hX.lift l
  let q : ∀ a : r.Matching j, V ⟶ F.obj (r.matchingTarget a) := fun a => l.π.app a
  let x : ∀ a : r.Matching j, cX.pt ⟶ F.obj (r.matchingTarget a) := fun a => cX.π.app a
  let y : ∀ a : r.Matching j, cY.pt ⟶ G.obj (r.matchingTarget a) := fun a => cY.π.app a
  have hm (a : r.Matching j) : m ≫ x a = q a := hX.fac l a
  have hxy (a : r.Matching j) : r.matchingComparisonWith f j cX cY hY ≫ y a =
      x a ≫ f.app (r.matchingTarget a) := r.matchingComparisonWith_π f j cX cY hY a
  have hqLeft (a : r.Matching j) : i ≫ q a = t ≫ x a :=
    MatchingLift.liftCone_left r (f := f) (j := j) (cF := u) (cG := v) (i := i) w hcorner a
  have hqRight (a : r.Matching j) : q a ≫ f.app (r.matchingTarget a) = b ≫ y a :=
    MatchingLift.liftCone_right r (f := f) (j := j) (cF := u) (cG := v) (i := i) w hcorner a
  refine { l := m, fac_left := ?_, fac_right := ?_ }
  · apply hX.hom_ext
    intro a
    change (i ≫ m) ≫ x a = t ≫ x a
    rw [Category.assoc, hm, hqLeft]
  · apply hY.hom_ext
    intro a
    change (m ≫ r.matchingComparisonWith f j cX cY hY) ≫ y a = b ≫ y a
    rw [Category.assoc, hxy, ← Category.assoc, hm, hqRight]

/-- The full original caller matching comparison has the coefficient lifting property. -/
theorem matchingComparisonWith_hasLiftingProperty
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    {U V : C} (i : U ⟶ V)
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k)) :
    HasLiftingProperty i (r.matchingComparisonWith f j cX cY hY) :=
  ⟨fun sq => CommSq.HasLift.mk' (matchingComparisonWithLiftStruct r f j cX hX cY hY i sq hcorner)⟩

omit [HasPullbacks C] in
/-- The comparison between the canonical original cones is the original limit map. -/
theorem matchingComparisonWith_canonical :
    r.matchingComparisonWith f j (limit.cone (r.matchingDiagram F j))
      (limit.cone (r.matchingDiagram G j)) (limit.isLimit (r.matchingDiagram G j)) =
      limMap (r.matchingTransformation f j) := by
  apply limit.hom_ext
  intro a
  rw [limMap_π]
  exact r.matchingComparisonWith_π f j (limit.cone _) (limit.cone _) (limit.isLimit _) a

/-- The original canonical matching limit map has the lower coefficient lifting property. -/
theorem matchingLimMap_hasLiftingProperty {U V : C} (i : U ⟶ V)
    (hcorner : ∀ k : J, r.degree k < r.degree j → HasLiftingProperty i (matchingCorner r f k)) :
    HasLiftingProperty i (limMap (r.matchingTransformation f j)) := by
  rw [← matchingComparisonWith_canonical r f j]
  exact matchingComparisonWith_hasLiftingProperty r f j
    (limit.cone _) (limit.isLimit _) (limit.cone _) (limit.isLimit _) i hcorner

end CategoryTheory.ReedyStructure

end ReedyPart2

section ReedyPart3

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  {F G : J ⥤ C} (f : F ⟶ G) (j : J)
  (L R : MorphismProperty C) [hLR : IsWeakFactorizationSystem L R]

include hLR

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]

/-- Any caller full latching comparison lies in the original source left class. -/
theorem latchingComparisonWith_mem
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (hcorner : ∀ k : J, r.degree k < r.degree j → L (latchingCorner r f k)) :
    L (r.latchingComparisonWith f j cX hX cY) := by
  rw [← llp_eq_of_wfs L R]
  intro U V p hp
  exact latchingComparisonWith_hasLiftingProperty r f j cX hX cY hY p
    (fun k hk => hasLiftingProperty_of_wfs _ _ (hcorner k hk) hp)

/-- The canonical full latching comparison lies in the original source left class. -/
theorem latchingColimMap_mem
    (hcorner : ∀ k : J, r.degree k < r.degree j → L (latchingCorner r f k)) :
    L (colimMap (r.latchingTransformation f j)) := by
  rw [← llp_eq_of_wfs L R]
  intro U V p hp
  exact latchingColimMap_hasLiftingProperty r f j p
    (fun k hk => hasLiftingProperty_of_wfs _ _ (hcorner k hk) hp)

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]

/-- Any caller full matching comparison lies in the original source right class. -/
theorem matchingComparisonWith_mem
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (hcorner : ∀ k : J, r.degree k < r.degree j → R (matchingCorner r f k)) :
    R (r.matchingComparisonWith f j cX cY hY) := by
  rw [← rlp_eq_of_wfs L R]
  intro U V i hi
  exact matchingComparisonWith_hasLiftingProperty r f j cX hX cY hY i
    (fun k hk => hasLiftingProperty_of_wfs _ _ hi (hcorner k hk))

/-- The canonical full matching comparison lies in the original source right class. -/
theorem matchingLimMap_mem
    (hcorner : ∀ k : J, r.degree k < r.degree j → R (matchingCorner r f k)) :
    R (limMap (r.matchingTransformation f j)) := by
  rw [← rlp_eq_of_wfs L R]
  intro U V i hi
  exact matchingLimMap_hasLiftingProperty r f j i
    (fun k hk => hasLiftingProperty_of_wfs _ _ hi (hcorner k hk))

end Matching

end CategoryTheory.ReedyStructure

end ReedyPart3
