/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalCofibrationSliceIntersection
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.OriginalSliceFilteredUnion
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# The actual original transfinite compatible-slice filtration

The original component labels are well-ordered without bounding their total
carrier. Every birth constructs a bounded compatible patch and its literal
intersection with the accumulated original slice. The original lower-colimit
maps produce its successor pushout. Limit stages use the same chosen original
lower-colimit union objects and all original actions.

This is the ordinary specialization of Jacob Lurie's *Higher Topos Theory*,
Lemma A.3.3.16 in the proof of Lemma A.3.3.3, author PDF dated April 9, 2017.
The original coefficient cofibration producer constructs the good component
trees; no complete compatible history or target filtration is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w t uD vD uC vC

namespace CategoryTheory.SmallObject.OriginalTransfiniteSliceFiltration

open Limits DiagramActionCapture DiagramSliceExtensions DiagramSliceExhaustion
open OriginalSliceFilteredUnion

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- A birth stores the actual produced bounded patch, intersection and original inclusions. -/
structure Birth (A : OriginalSlice theta L) (seed : Supports (P := P) chi) where
  /-- The selected bounded compatible original receiving slice. -/
  patch : Slice theta L chi
  /-- The selected bounded compatible original intersection slice. -/
  overlap : Slice theta L chi
  /-- The full original intersection inclusion into the accumulated slice. -/
  intoBefore : OriginalSlice.Inclusion (OriginalSlice.ofBounded chi overlap) A
  /-- The full original intersection inclusion into the selected patch. -/
  intoPatch : OriginalSlice.Inclusion (OriginalSlice.ofBounded chi overlap)
    (OriginalSlice.ofBounded chi patch)
  /-- The actual original next seed is contained in the produced patch. -/
  seed_le (d : D) : seed d ≤ patch.supports d
  /-- The intersection has exactly the original intersection support. -/
  overlap_support (d : D) : (overlap.supports d).1 = A.supports d ⊓ (patch.supports d).1

namespace Birth

variable {theta L chi} {A : OriginalSlice theta L} {seed : Supports (P := P) chi}
  (E : Birth theta L chi A seed)

/-- Both original lower-map isomorphisms identify the actual intersection objects. -/
def overlapIso (d : D) :
    ((L d).obj (E.overlap.supports d).1).right ≅
      ((L d).obj (A.supports d ⊓ (E.patch.supports d).1)).right :=
  ((L d).functor ⋙ Under.forget (F.obj d)).mapIso (eqToIso (E.overlap_support d))

/-- The forward original intersection comparison retains the original BEFORE leg. -/
theorem overlap_hom_before (d : D) :
    (E.overlapIso d).hom ≫ ((L d).map
      (inf_le_left : A.supports d ⊓ (E.patch.supports d).1 ≤ A.supports d)).right =
        ((L d).map (E.intoBefore.le d)).right := by
  exact congrArg Under.Hom.right
    ((L d).map_comp (E.overlap_support d).le inf_le_left)

/-- The inverse original intersection comparison retains the same BEFORE leg. -/
theorem overlap_inv_before (d : D) :
    (E.overlapIso d).inv ≫ ((L d).map (E.intoBefore.le d)).right =
      ((L d).map
        (inf_le_left : A.supports d ⊓ (E.patch.supports d).1 ≤ A.supports d)).right := by
  have hA : (E.overlap.supports d).1 ≤ A.supports d := E.intoBefore.le d
  exact congrArg Under.Hom.right ((L d).map_comp (E.overlap_support d).symm.le hA)

/-- The forward original intersection comparison retains the actual selected patch leg. -/
theorem overlap_hom_patch (d : D) :
    (E.overlapIso d).hom ≫ ((L d).map
      (inf_le_right : A.supports d ⊓ (E.patch.supports d).1 ≤
        (E.patch.supports d).1)).right = ((L d).map (E.intoPatch.le d)).right := by
  exact congrArg Under.Hom.right
    ((L d).map_comp (E.overlap_support d).le inf_le_right)

/-- The inverse original intersection comparison retains that same selected patch leg. -/
theorem overlap_inv_patch (d : D) :
    (E.overlapIso d).inv ≫ ((L d).map (E.intoPatch.le d)).right =
      ((L d).map
        (inf_le_right : A.supports d ⊓ (E.patch.supports d).1 ≤
          (E.patch.supports d).1)).right := by
  have hN : (E.overlap.supports d).1 ≤ (E.patch.supports d).1 := E.intoPatch.le d
  exact congrArg Under.Hom.right ((L d).map_comp (E.overlap_support d).symm.le hN)

/-- Conjugate the actual selected intersection action to the same original L(A ∩ N) points. -/
abbrev overlapAction {d e : D} (g : d ⟶ e) :=
  (E.overlapIso d).inv ≫ E.overlap.map g ≫ (E.overlapIso e).hom

/-- The complete original BEFORE naturality square follows from the actual overlap inclusion. -/
theorem overlap_before {d e : D} (g : d ⟶ e) :
    ((L d).map
      (inf_le_left : A.supports d ⊓ (E.patch.supports d).1 ≤ A.supports d)).right ≫
        A.map g = E.overlapAction g ≫ ((L e).map
          (inf_le_left : A.supports e ⊓ (E.patch.supports e).1 ≤ A.supports e)).right := by
  have hn := E.intoBefore.naturality g
  have hd : (E.overlap.supports d).1 ≤ A.supports d := E.intoBefore.le d
  have he : (E.overlap.supports e).1 ≤ A.supports e := E.intoBefore.le e
  change ((L d).map hd).right ≫ A.map g =
    E.overlap.map g ≫ ((L e).map he).right at hn
  calc
    _ = ((E.overlapIso d).inv ≫ ((L d).map hd).right) ≫
        A.map g := congrArg (fun k => k ≫ A.map g) (E.overlap_inv_before d).symm
    _ = (E.overlapIso d).inv ≫
        (((L d).map hd).right ≫ A.map g) := Category.assoc _ _ _
    _ = (E.overlapIso d).inv ≫
        (E.overlap.map g ≫ ((L e).map he).right) :=
      congrArg (fun k => (E.overlapIso d).inv ≫ k) hn
    _ = (E.overlapIso d).inv ≫ (E.overlap.map g ≫ ((E.overlapIso e).hom ≫
        ((L e).map (inf_le_left : A.supports e ⊓ (E.patch.supports e).1 ≤
          A.supports e)).right)) :=
      congrArg (fun k => (E.overlapIso d).inv ≫ (E.overlap.map g ≫ k))
        (E.overlap_hom_before e).symm
    _ = _ := by simp only [overlapAction, Category.assoc]

/-- The complete original patch naturality square follows from the actual overlap inclusion. -/
theorem overlap_patch {d e : D} (g : d ⟶ e) :
    ((L d).map
      (inf_le_right : A.supports d ⊓ (E.patch.supports d).1 ≤
        (E.patch.supports d).1)).right ≫ E.patch.map g =
      E.overlapAction g ≫ ((L e).map
        (inf_le_right : A.supports e ⊓ (E.patch.supports e).1 ≤
          (E.patch.supports e).1)).right := by
  have hn := E.intoPatch.naturality g
  have hd : (E.overlap.supports d).1 ≤ (E.patch.supports d).1 := E.intoPatch.le d
  have he : (E.overlap.supports e).1 ≤ (E.patch.supports e).1 := E.intoPatch.le e
  change ((L d).map hd).right ≫ E.patch.map g =
    E.overlap.map g ≫ ((L e).map he).right at hn
  calc
    _ = ((E.overlapIso d).inv ≫ ((L d).map hd).right) ≫
        E.patch.map g := congrArg (fun k => k ≫ E.patch.map g) (E.overlap_inv_patch d).symm
    _ = (E.overlapIso d).inv ≫
        (((L d).map hd).right ≫ E.patch.map g) := Category.assoc _ _ _
    _ = (E.overlapIso d).inv ≫
        (E.overlap.map g ≫ ((L e).map he).right) :=
      congrArg (fun k => (E.overlapIso d).inv ≫ k) hn
    _ = (E.overlapIso d).inv ≫ (E.overlap.map g ≫ ((E.overlapIso e).hom ≫
        ((L e).map (inf_le_right : A.supports e ⊓ (E.patch.supports e).1 ≤
          (E.patch.supports e).1)).right)) :=
      congrArg (fun k => (E.overlapIso d).inv ≫ (E.overlap.map g ≫ k))
        (E.overlap_hom_patch e).symm
    _ = _ := by simp only [overlapAction, Category.assoc]

/-- AFTER is the original lower-union pushout construction with the derived overlap actions. -/
def after : OriginalSlice theta L :=
  unionSlice theta L A (OriginalSlice.ofBounded chi E.patch)
    E.overlapAction E.overlap_before E.overlap_patch

/-- The actual full original BEFORE-to-AFTER inclusion. -/
def beforeInclusion : OriginalSlice.Inclusion A E.after :=
  leftUnionInclusion theta L A (OriginalSlice.ofBounded chi E.patch)
    E.overlapAction E.overlap_before E.overlap_patch

/-- The selected patch retains its full original natural inclusion into AFTER. -/
def patchInclusion : OriginalSlice.Inclusion (OriginalSlice.ofBounded chi E.patch) E.after :=
  rightUnionInclusion theta L A (OriginalSlice.ofBounded chi E.patch)
    E.overlapAction E.overlap_before E.overlap_patch

/-- Each component successor is the actual pushout on the original selected overlap object. -/
theorem componentIsPushout (d : D) :
    IsPushout (E.intoBefore.toNatTrans.app d) (E.intoPatch.toNatTrans.app d)
      (E.beforeInclusion.toNatTrans.app d) (E.patchInclusion.toNatTrans.app d) := by
  refine (unionCoefficientIsPushout theta L A
    (OriginalSlice.ofBounded chi E.patch) d).of_iso'
    (E.overlapIso d) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change (E.overlapIso d).hom ≫ ((L d).map
      (inf_le_left : A.supports d ⊓ (E.patch.supports d).1 ≤ A.supports d)).right =
        ((L d).map (E.intoBefore.le d)).right ≫ 𝟙 _
    rw [Category.comp_id]
    exact E.overlap_hom_before d
  · change (E.overlapIso d).hom ≫ ((L d).map
      (inf_le_right : A.supports d ⊓ (E.patch.supports d).1 ≤
        (E.patch.supports d).1)).right = ((L d).map (E.intoPatch.le d)).right ≫ 𝟙 _
    rw [Category.comp_id]
    exact E.overlap_hom_patch d
  · change 𝟙 _ ≫ ((L d).map
      (le_sup_left : A.supports d ≤ A.supports d ⊔ (E.patch.supports d).1)).right =
        ((L d).map le_sup_left).right ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · change 𝟙 _ ≫ ((L d).map
      (le_sup_right : (E.patch.supports d).1 ≤ A.supports d ⊔ (E.patch.supports d).1)).right =
        ((L d).map le_sup_right).right ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- Every successor is a whole original diagram pushout with all original component functions. -/
theorem isPushout :
    IsPushout E.intoBefore.toNatTrans E.intoPatch.toNatTrans
      E.beforeInclusion.toNatTrans E.patchInclusion.toNatTrans :=
  IsPushout.of_forall_isPushout_app E.componentIsPushout

/-- Every genuinely new original label lies in the actual chosen bounded patch. -/
theorem new_mem_patch (d : D) {a : P d} (ha : a ∈ E.after.supports d)
    (hOld : a ∉ A.supports d) : a ∈ (E.patch.supports d).1 := by
  change a ∈ A.supports d ⊔ (E.patch.supports d).1 at ha
  exact ha.resolve_left hOld

/-- The literal original component difference is bounded by the actual selected patch. -/
theorem difference_bound (d : D) :
    HasCardinalLT (CellTree.Increment (A.supports d) (E.after.supports d)) chi :=
  (E.patch.supports d).2.of_injective
    (fun a => (⟨a.1, E.new_mem_patch d a.2.1 a.2.2⟩ :
      ((E.patch.supports d).1 : Set (P d))))
    (fun _ _ h => Subtype.ext (congrArg
      (fun a : ((E.patch.supports d).1 : Set (P d)) => a.1) h))

/-- The actual relative tree on the literal AFTER minus BEFORE original label set. -/
def differenceTree (d : D) :
    CellTree s ((L d).obj (A.supports d)).right
      (P := CellTree.Increment (A.supports d) (E.after.supports d)) :=
  CellTreeIncrement.tree (theta.component d).tree (L d)
    (A.supports d) (E.after.supports d) (E.beforeInclusion.le d)

/-- That original difference tree represents the same entire original successor component. -/
theorem differenceTree_hom (d : D) :
    (E.differenceTree d).hom = E.beforeInclusion.toNatTrans.app d := rfl

/-- The full new-label carrier keeps the original object and the original component label. -/
abbrev NewLabels := {p : Σ d : D, P d //
  p.2 ∈ E.after.supports p.1 ∧ p.2 ∉ A.supports p.1}

/-- The total new-label bound is derived from the actual produced patch's total bound. -/
theorem newLabels_bound : HasCardinalLT E.NewLabels chi :=
  E.patch.labels_lt.of_injective
    (fun p => (⟨p.1.1, ⟨p.1.2, E.new_mem_patch p.1.1 p.2.1 p.2.2⟩⟩ :
      Σ d : D, ((E.patch.supports d).1 : Set (P d))))
    (fun _ _ h => Subtype.ext (congrArg
      (fun p : Σ d : D, ((E.patch.supports d).1 : Set (P d)) =>
        (⟨p.1, p.2.1⟩ : Σ d : D, P d)) h))

end Birth

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hUncountable : Cardinal.aleph0 < chi) (hArrow : HasCardinalLT (Arrow D) chi)
  (good : ∀ d, (theta.component d).tree.IsGood chi)

/-- Produce the actual next bounded compatible birth from the original source data. -/
def nextBirth (A : OriginalSlice theta L) (seed : Supports (P := P) chi) :
    Birth theta L chi A seed := by
  apply Classical.choice
  obtain ⟨N, Nprime, hseed, hinf, hA, hN⟩ :=
    DiagramSliceIntersection.existsGenericBoundedCompatibleIntersection
      theta L A chi hUncountable hArrow good seed
  exact ⟨{ patch := N, overlap := Nprime
           intoBefore := Classical.choice hA, intoPatch := Classical.choice hN
           seed_le := hseed, overlap_support := hinf }⟩

/-- The history carrier is exactly the unbounded disjoint union of original component labels. -/
def HistoryIndex := Σ d : D, P d

/-- Well-order the same full original label carrier, without imposing a cardinal bound on it. -/
instance historyIndexLinearOrder : LinearOrder (HistoryIndex (P := P)) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The chosen order on the full original label carrier is genuinely well-founded. -/
instance historyIndexWellFounded : WellFoundedLT (HistoryIndex (P := P)) :=
  WellOrderingRel.isWellOrder.wf

/-- The seed contains the current original label and all its original component predecessors. -/
abbrev birthSeed (p : HistoryIndex (P := P)) : Supports (P := P) chi :=
  seedFor theta chi good p.1 p.2

/-- A recursion entry contains its actual original BEFORE and its internally produced birth. -/
structure Entry (p : HistoryIndex (P := P)) where
  /-- The accumulated original compatible slice. -/
  before : OriginalSlice theta L
  /-- The actual next bounded patch and original intersection. -/
  birth : Birth theta L chi before (birthSeed theta chi good p)

/-- The actual AFTER of a recursion entry is its original lower-union pushout. -/
abbrev Entry.after {p : HistoryIndex (P := P)} (E : Entry theta L chi good p) :
    OriginalSlice theta L := E.birth.after

/-- A step uses only earlier entries, the actual lower-union UPs and the next bounded birth. -/
def entryStep (p : HistoryIndex (P := P))
    (prior : ∀ j : HistoryIndex (P := P), j < p → Entry theta L chi good j) :
    Entry theta L chi good p :=
  let B := familyBefore (fun j : Set.Iio p => (prior j.1 j.2).after)
  { before := B
    birth := nextBirth theta L chi hUncountable hArrow good B (birthSeed theta chi good p) }

/-- Construct the full original history by genuine well-founded recursion. -/
def history : ∀ p : HistoryIndex (P := P), Entry theta L chi good p :=
  wellFounded_lt.fix (entryStep theta L chi hUncountable hArrow good)

/-- The actual recursively constructed entry retains its original step equation. -/
theorem history_eq (p : HistoryIndex (P := P)) :
    history theta L chi hUncountable hArrow good p =
      entryStep theta L chi hUncountable hArrow good p
        (fun j _ => history theta L chi hUncountable hArrow good j) :=
  WellFounded.fix_eq _ _ _

/-- Induction constructs all earlier original AFTER-to-BEFORE inclusions.
It proves that every actual recursion input is compatible. -/
theorem existsHistoryEarlierInclusion (p : HistoryIndex (P := P)) :
    ∀ j, j < p → Nonempty (OriginalSlice.Inclusion
      (history theta L chi hUncountable hArrow good j).after
      (history theta L chi hUncountable hArrow good p).before) := by
  apply wellFounded_lt.induction p
  intro p ih
  have hc : Compatible
      (fun j : Set.Iio p => (history theta L chi hUncountable hArrow good j.1).after) := by
    intro i j hij
    by_cases heq : i = j
    · subst j
      exact ⟨identityInclusion _⟩
    · have hlt : i.1 < j.1 := lt_of_le_of_ne hij (fun h => heq (Subtype.ext h))
      obtain ⟨h⟩ := ih j.1 j.2 i.1 hlt
      exact ⟨composeInclusion h
        (history theta L chi hUncountable hArrow good j.1).birth.beforeInclusion⟩
  intro j hj
  rw [history_eq theta L chi hUncountable hArrow good p]
  exact ⟨familyBeforeInclusion _ hc ⟨j, hj⟩⟩

/-- The actual full earlier original inclusion is chosen from the proved induction invariant. -/
def historyEarlierInclusion (j p : HistoryIndex (P := P)) (hjp : j < p) :
    OriginalSlice.Inclusion (history theta L chi hUncountable hArrow good j).after
      (history theta L chi hUncountable hArrow good p).before :=
  Classical.choice
    (existsHistoryEarlierInclusion theta L chi hUncountable hArrow good p j hjp)

/-- The constructed AFTER history has every original natural inclusion on ordered pairs. -/
theorem historyCompatible : Compatible
    (fun p => (history theta L chi hUncountable hArrow good p).after) := by
  intro a b hab
  rcases eq_or_lt_of_le hab with h | h
  · subst b
    exact ⟨identityInclusion _⟩
  · exact ⟨composeInclusion
      (historyEarlierInclusion theta L chi hUncountable hArrow good a b h)
      (history theta L chi hUncountable hArrow good b).birth.beforeInclusion⟩

/-- Every actual earlier subfamily is compatible, including the empty initial subfamily. -/
theorem historyBelowCompatible (p : HistoryIndex (P := P)) : Compatible
    (fun j : Set.Iio p => (history theta L chi hUncountable hArrow good j.1).after) := by
  intro a b hab
  exact historyCompatible theta L chi hUncountable hArrow good a.1 b.1 hab

/-- The actual accumulated original slice immediately before an original label. -/
abbrev before (p : HistoryIndex (P := P)) : OriginalSlice theta L :=
  (history theta L chi hUncountable hArrow good p).before

/-- The actual accumulated original slice after its constructed bounded birth. -/
abbrev after (p : HistoryIndex (P := P)) : OriginalSlice theta L :=
  (history theta L chi hUncountable hArrow good p).after

/-- The actual birth retains its bounded patch, original overlap and both full natural maps. -/
abbrev birth (p : HistoryIndex (P := P)) :
    Birth theta L chi (before theta L chi hUncountable hArrow good p)
      (birthSeed theta chi good p) :=
  (history theta L chi hUncountable hArrow good p).birth

/-- BEFORE is literally the constructed original union of all preceding AFTER slices. -/
theorem before_eq_family (p : HistoryIndex (P := P)) :
    before theta L chi hUncountable hArrow good p =
      familyBefore (fun j : Set.Iio p => after theta L chi hUncountable hArrow good j.1) := by
  exact congrArg Entry.before (history_eq theta L chi hUncountable hArrow good p)

/-- Every original BEFORE support is the same actual union of all earlier original supports. -/
theorem before_union (p : HistoryIndex (P := P)) (d : D) :
    (before theta L chi hUncountable hArrow good p).supports d =
      ⨆ j : Set.Iio p, (after theta L chi hUncountable hArrow good j.1).supports d := by
  rw [before_eq_family theta L chi hUncountable hArrow good p]
  exact familyBefore_support _ (historyBelowCompatible theta L chi hUncountable hArrow good p) d

/-- The next original label is genuinely captured by its internally constructed birth. -/
theorem captures (p : HistoryIndex (P := P)) :
    p.2 ∈ (after theta L chi hUncountable hArrow good p).supports p.1 := by
  let E := birth theta L chi hUncountable hArrow good p
  have h := E.seed_le p.1
  change seedFor theta chi good p.1 p.2 p.1 ≤ E.patch.supports p.1 at h
  rw [seedFor_same] at h
  have hp : p.2 ∈ (E.patch.supports p.1).1 := LowerSetColimits.memOfLE h le_rfl
  exact LowerSetColimits.memOfLE (E.patchInclusion.le p.1) hp

/-- The internally constructed history exhausts every original component-label carrier. -/
theorem exhausts (d : D) :
    (⨆ p : HistoryIndex (P := P),
      (after theta L chi hUncountable hArrow good p).supports d) = ⊤ := by
  apply top_unique
  intro a _
  exact LowerSet.mem_iSup_iff.2
    ⟨(⟨d, a⟩ : HistoryIndex (P := P)), captures theta L chi hUncountable hArrow good ⟨d, a⟩⟩

/-- Every original earlier AFTER has its actual whole inclusion into BEFORE. -/
abbrev earlierToBefore (j p : HistoryIndex (P := P)) (hjp : j < p) :=
  historyEarlierInclusion theta L chi hUncountable hArrow good j p hjp

/-- The actual full successor inclusion comes from the original union pushout. -/
abbrev beforeToAfter (p : HistoryIndex (P := P)) :=
  (birth theta L chi hUncountable hArrow good p).beforeInclusion

/-- The actual original diagram of all earlier AFTER slices under the unchanged source F. -/
abbrev beforeDiagram (p : HistoryIndex (P := P)) : Set.Iio p ⥤ Under F :=
  familyDiagram (fun j : Set.Iio p => after theta L chi hUncountable hArrow good j.1)
    (historyBelowCompatible theta L chi hUncountable hArrow good p)

/-- The actual BEFORE cocone has the literal BEFORE point and every original inclusion. -/
abbrev beforeCocone (p : HistoryIndex (P := P)) :
    Cocone (beforeDiagram theta L chi hUncountable hArrow good p) where
  pt := Under.mk (before theta L chi hUncountable hArrow good p).root
  ι :=
    { app j := Under.homMk
        (earlierToBefore theta L chi hUncountable hArrow good j.1 p j.2).toNatTrans
        (inclusion_root (earlierToBefore theta L chi hUncountable hArrow good j.1 p j.2))
      naturality i j h := by
        apply Under.UnderMorphism.ext
        apply NatTrans.ext
        funext d
        change ((L d).map _).right ≫ ((L d).map _).right =
          ((L d).map _).right ≫ 𝟙 _
        rw [Category.comp_id, ← Under.comp_right, (L d).map_comp] }

/-- Each original component BEFORE cocone uses the same chosen lower-colimit point. -/
abbrev beforeComponentCocone (p : HistoryIndex (P := P)) (d : D) :
    Cocone (OriginalSliceFilteredUnion.componentDiagram
      (fun j : Set.Iio p => after theta L chi hUncountable hArrow good j.1)
      (familyInclusion _ (historyBelowCompatible theta L chi hUncountable hArrow good p)) d)
    where
  pt := (L d).obj ((before theta L chi hUncountable hArrow good p).supports d)
  ι :=
    { app j := (L d).map
        ((earlierToBefore theta L chi hUncountable hArrow good j.1 p j.2).le d)
      naturality i j h := by
        change (L d).map _ ≫ (L d).map _ = (L d).map _ ≫ 𝟙 _
        rw [(L d).map_comp, Category.comp_id] }

/-- Original lower UPs construct the actual BEFORE component UP, including the empty case. -/
def beforeComponentIsColimit (p : HistoryIndex (P := P)) (d : D) :
    IsColimit (beforeComponentCocone theta L chi hUncountable hArrow good p d) := by
  classical
  by_cases hn : Nonempty (Set.Iio p)
  · letI : Nonempty (Set.Iio p) := hn
    refine IsColimit.ofIsoColimit
      ((L d).isColimitFilteredCocone (B := supportFunctor
        (fun j : Set.Iio p => after theta L chi hUncountable hArrow good j.1)
        (familyInclusion _
          (historyBelowCompatible theta L chi hUncountable hArrow good p)) d))
      (Cocone.ext ((L d).functor.mapIso
        (eqToIso (before_union theta L chi hUncountable hArrow good p d).symm)) ?_)
    intro j
    change (L d).map _ ≫ (L d).map _ = (L d).map _
    rw [(L d).map_comp]
  · letI : IsEmpty (Set.Iio p) := ⟨fun j => hn ⟨j⟩⟩
    have hi : IsInitial (beforeComponentCocone theta L chi hUncountable hArrow good p d).pt := by
      change IsInitial ((L d).obj ((before theta L chi hUncountable hArrow good p).supports d))
      rw [before_union theta L chi hUncountable hArrow good p d]
      simpa using (L d).isInitialObjBot
    exact
      { desc := fun t => hi.to t.pt
        fac := fun _ j => False.elim (hn ⟨j⟩)
        uniq := fun _ _ _ => hi.hom_ext _ _ }

/-- The complete original BEFORE UP is derived, with every original action and root square. -/
def beforeIsColimit (p : HistoryIndex (P := P)) :
    IsColimit (beforeCocone theta L chi hUncountable hArrow good p) := by
  classical
  by_cases hn : Nonempty (Set.Iio p)
  · letI : Nonempty (Set.Iio p) := hn
    letI : IsConnected (Set.Iio p) := IsFiltered.isConnected (Set.Iio p)
    apply isColimitOfReflects (Under.forget F)
    apply evaluationJointlyReflectsColimits
    intro d
    exact isColimitOfPreserves (Under.forget (F.obj d))
      (beforeComponentIsColimit theta L chi hUncountable hArrow good p d)
  · letI : IsEmpty (Set.Iio p) := ⟨fun j => hn ⟨j⟩⟩
    have he : ¬(Nonempty (Set.Iio p) ∧ Compatible
        (fun j : Set.Iio p => after theta L chi hUncountable hArrow good j.1)) :=
      fun h => hn h.1
    have hb : before theta L chi hUncountable hArrow good p =
        OriginalSliceFilteredUnion.empty (theta := theta) (L := L) := by
      rw [before_eq_family theta L chi hUncountable hArrow good p]
      unfold familyBefore
      rw [dite_eq_right he]
    have hi : IsInitial (beforeCocone theta L chi hUncountable hArrow good p).pt := by
      change IsInitial (Under.mk (before theta L chi hUncountable hArrow good p).root)
      rw [hb]
      exact emptyIsInitial (theta := theta) (L := L)
    exact
      { desc := fun t => hi.to t.pt
        fac := fun _ j => False.elim (hn ⟨j⟩)
        uniq := fun _ _ _ => hi.hom_ext _ _ }

/-- The entire actual original AFTER history is a diagram under the same original F. -/
abbrev afterDiagram : HistoryIndex (P := P) ⥤ Under F :=
  familyDiagram (after theta L chi hUncountable hArrow good)
    (historyCompatible theta L chi hUncountable hArrow good)

/-- The full original union is constructed from the internally proved compatible history. -/
abbrev whole : OriginalSlice theta L :=
  familyBefore (after theta L chi hUncountable hArrow good)

/-- Every whole original component support is exactly top, by actual label exhaustion. -/
theorem whole_support (d : D) :
    (whole theta L chi hUncountable hArrow good).supports d = ⊤ :=
  (familyBefore_support _ (historyCompatible theta L chi hUncountable hArrow good) d).trans
    (exhausts theta L chi hUncountable hArrow good d)

/-- The whole chosen original component has both actual original endpoint comparison maps. -/
def wholeComponentIso (d : D) :
    (L d).obj ((whole theta L chi hUncountable hArrow good).supports d) ≅ Under.mk (f.app d) :=
  (L d).functor.mapIso (eqToIso (whole_support theta L chi hUncountable hArrow good d)) ≪≫
    (theta.component d).tree.endpointIso (L d) ≪≫ (theta.component d).endpointIso

/-- The forward whole comparison is exactly the original whole lower endpoint leg. -/
theorem wholeComponentIso_hom (d : D) :
    (wholeComponentIso theta L chi hUncountable hArrow good d).hom =
      legUnder theta L d ((whole theta L chi hUncountable hArrow good).supports d) := by
  simp only [wholeComponentIso, Iso.trans_hom, Functor.mapIso_hom,
    legUnder, EndpointDiagramTransport.lowerLeg, Category.assoc]

/-- Both whole coefficient endpoint maps are obtained from the same original lower data. -/
abbrev wholeCoefficientIso (d : D) :
    (whole theta L chi hUncountable hArrow good).toFunctor.obj d ≅ G.obj d :=
  (Under.forget (F.obj d)).mapIso (wholeComponentIso theta L chi hUncountable hArrow good d)

/-- The coefficient endpoint comparison is the exact original lower-to-G function. -/
theorem wholeCoefficientIso_hom (d : D) :
    (wholeCoefficientIso theta L chi hUncountable hArrow good d).hom =
      leg theta L d ((whole theta L chi hUncountable hArrow good).supports d) :=
  congrArg Under.Hom.right (wholeComponentIso_hom theta L chi hUncountable hArrow good d)

/-- The full original whole endpoint isomorphism retains every original G action. -/
def wholeFunctorIso : (whole theta L chi hUncountable hArrow good).toFunctor ≅ G :=
  NatIso.ofComponents (wholeCoefficientIso theta L chi hUncountable hArrow good) (by
    intro d e g
    change (whole theta L chi hUncountable hArrow good).map g ≫
        (wholeCoefficientIso theta L chi hUncountable hArrow good e).hom =
      (wholeCoefficientIso theta L chi hUncountable hArrow good d).hom ≫ G.map g
    rw [wholeCoefficientIso_hom, wholeCoefficientIso_hom]
    exact (whole theta L chi hUncountable hArrow good).map_endpoint g)

/-- The full forward endpoint comparison is literally the original whole target transformation. -/
theorem wholeFunctorIso_hom : (wholeFunctorIso theta L chi hUncountable hArrow good).hom =
    (whole theta L chi hUncountable hArrow good).target := by
  apply NatTrans.ext
  funext d
  exact wholeCoefficientIso_hom theta L chi hUncountable hArrow good d

/-- The whole endpoint comparison is an isomorphism under the unchanged original source F. -/
def wholeUnderIso : Under.mk (whole theta L chi hUncountable hArrow good).root ≅ Under.mk f :=
  Under.isoMk (wholeFunctorIso theta L chi hUncountable hArrow good)
    (by
      change (whole theta L chi hUncountable hArrow good).root ≫
        (wholeFunctorIso theta L chi hUncountable hArrow good).hom = f
      rw [wholeFunctorIso_hom]
      exact OriginalSlice.factor (whole theta L chi hUncountable hArrow good))

/-- The endpoint cocone has the literal original arrow f and all original AFTER target legs. -/
abbrev endpointCocone : Cocone (afterDiagram theta L chi hUncountable hArrow good) where
  pt := Under.mk f
  ι :=
    { app p := Under.homMk (after theta L chi hUncountable hArrow good p).target
        (OriginalSlice.factor (after theta L chi hUncountable hArrow good p))
      naturality i j h := by
        apply Under.UnderMorphism.ext
        apply NatTrans.ext
        funext d
        change ((L d).map _).right ≫
            leg theta L d ((after theta L chi hUncountable hArrow good j).supports d) =
          leg theta L d ((after theta L chi hUncountable hArrow good i).supports d) ≫ 𝟙 _
        rw [Category.comp_id]
        exact inclusion_leg theta L d _ }

/-- Original lower exhaustion constructs the whole endpoint UP at the literal original f. -/
def endpointIsColimit : IsColimit (endpointCocone theta L chi hUncountable hArrow good) := by
  refine IsColimit.ofIsoColimit
    (familyBeforeIsColimit (after theta L chi hUncountable hArrow good)
      (historyCompatible theta L chi hUncountable hArrow good))
    (Cocone.ext (wholeUnderIso theta L chi hUncountable hArrow good) ?_)
  intro p
  apply Under.UnderMorphism.ext
  apply NatTrans.ext
  funext d
  change ((L d).map _).right ≫
      (wholeFunctorIso theta L chi hUncountable hArrow good).hom.app d =
    leg theta L d ((after theta L chi hUncountable hArrow good p).supports d)
  rw [wholeFunctorIso_hom]
  exact inclusion_leg theta L d _

section ContinuousPresentation

open CompactRootBaseChange

attribute [local instance] constructionIndexWellFounded constructionIndexSuccOrder

/-- All lower restrictions of the actual AFTER history use their actual original slice unions. -/
def lowerHistoryData : LowerSetColimitData (afterDiagram theta L chi hUncountable hArrow good) where
  cocone B := familyBeforeCocone
    (fun p : B => after theta L chi hUncountable hArrow good p.1)
    (fun i j h => historyCompatible theta L chi hUncountable hArrow good i.1 j.1 h)
  isColimit B := familyBeforeIsColimit
    (fun p : B => after theta L chi hUncountable hArrow good p.1)
    (fun i j h => historyCompatible theta L chi hUncountable hArrow good i.1 j.1 h)

/-- The actual continuous prefixes are lower sets of the same original birth-label carrier. -/
abbrev continuousPrefixFunctor :
    ConstructionIndex (HistoryIndex (P := P)) ⥤ LowerSet (HistoryIndex (P := P)) :=
  originalPrefix_mono.functor

/-- Every continuous stage is the actual chosen original union under the original source F. -/
abbrev continuousDiagramUnder : ConstructionIndex (HistoryIndex (P := P)) ⥤ Under F :=
  continuousPrefixFunctor (P := P) ⋙
    (lowerHistoryData theta L chi hUncountable hArrow good).functor

/-- The whole continuous diagram retains all original coefficient functor actions. -/
abbrev continuousDiagram : ConstructionIndex (HistoryIndex (P := P)) ⥤ (D ⥤ C) :=
  continuousDiagramUnder theta L chi hUncountable hArrow good ⋙ Under.forget F

/-- These are the actual strict-prefix lower sets used at each limit stage. -/
abbrev continuousLimitPrefixes (gamma : ConstructionIndex (HistoryIndex (P := P))) :
    Set.Iio gamma ⥤ LowerSet (HistoryIndex (P := P)) :=
  (Set.principalSegIio gamma).monotone.functor ⋙ continuousPrefixFunctor (P := P)

omit [Category D] [∀ d, PartialOrder (P d)] in
/-- A genuine limit prefix is precisely the union of its actual earlier original prefixes. -/
theorem continuousLimitUnion (gamma : ConstructionIndex (HistoryIndex (P := P)))
    (hgamma : Order.IsSuccLimit gamma) :
    LowerSetColimitData.filteredUnion (continuousLimitPrefixes (P := P) gamma) =
      originalPrefix gamma := by
  ext p
  change p ∈ (⨆ delta : Set.Iio gamma, originalPrefix delta.1) ↔ p ∈ originalPrefix gamma
  rw [LowerSet.mem_iSup_iff]
  exact (originalPrefix_limit_membership gamma hgamma p).symm

/-- The genuine original lower-union data proves the continuous limit UP under original F. -/
def continuousLimitIsColimitUnder (gamma : ConstructionIndex (HistoryIndex (P := P)))
    (hgamma : Order.IsSuccLimit gamma) :
    IsColimit ((Set.principalSegIio gamma).cocone
      (continuousDiagramUnder theta L chi hUncountable hArrow good)) := by
  letI : Nonempty (Set.Iio gamma) := ⟨⟨⊥, hgamma.bot_lt⟩⟩
  let M := lowerHistoryData theta L chi hUncountable hArrow good
  let B := continuousLimitPrefixes (P := P) gamma
  let e : M.obj (LowerSetColimitData.filteredUnion B) ≅ M.obj (originalPrefix gamma) :=
    M.functor.mapIso (eqToIso (continuousLimitUnion gamma hgamma))
  exact IsColimit.ofIsoColimit (M.isColimitFilteredCocone (B := B)) (Cocone.ext e (by
    intro delta
    change M.map _ ≫ M.map _ = M.map _
    rw [M.map_comp]))

/-- The actual whole original coefficient diagram is well-order continuous. -/
theorem continuousDiagram_isWellOrderContinuous :
    (continuousDiagram theta L chi hUncountable hArrow good).IsWellOrderContinuous where
  nonempty_isColimit gamma hgamma := by
    let : Nonempty (Set.Iio gamma) := ⟨⟨⊥, hgamma.bot_lt⟩⟩
    let : IsConnected (Set.Iio gamma) := IsFiltered.isConnected (Set.Iio gamma)
    exact (Under.preservesColimitsOfShape_forget_of_isConnected (J := Set.Iio gamma)
      (B := F)).preservesColimit.preserves
      (continuousLimitIsColimitUnder theta L chi hUncountable hArrow good gamma hgamma)

/-- The actual initial stage compares with the unchanged original identity source under F. -/
def continuousBotIsoUnder :
    (continuousDiagramUnder theta L chi hUncountable hArrow good).obj ⊥ ≅ Under.mk (𝟙 F) :=
  (lowerHistoryData theta L chi hUncountable hArrow good).functor.mapIso
      (eqToIso (originalPrefix_bot (P := HistoryIndex (P := P)))) ≪≫
    (lowerHistoryData theta L chi hUncountable hArrow good).isInitialObjBot.uniqueUpToIso
      Under.mkIdInitial

/-- The whole original lower cocone and actual endpoint UP construct both original top maps. -/
def lowerHistoryTopIso :
    (lowerHistoryData theta L chi hUncountable hArrow good).obj ⊤ ≅ Under.mk f := by
  let M := lowerHistoryData theta L chi hUncountable hArrow good
  exact M.isColimitFullCocone.coconePointUniqueUpToIso
    (endpointIsColimit theta L chi hUncountable hArrow good)

/-- The actual final continuous stage compares with the literal original f under original F. -/
def continuousTopIsoUnder :
    (continuousDiagramUnder theta L chi hUncountable hArrow good).obj ⊤ ≅ Under.mk f :=
  (lowerHistoryData theta L chi hUncountable hArrow good).functor.mapIso
    (eqToIso (originalPrefix_top (P := HistoryIndex (P := P)))) ≪≫
      lowerHistoryTopIso theta L chi hUncountable hArrow good

/-- Both original source maps in the coefficient functor category. -/
abbrev continuousBotIso :
    (continuousDiagram theta L chi hUncountable hArrow good).obj ⊥ ≅ F :=
  (Under.forget F).mapIso (continuousBotIsoUnder theta L chi hUncountable hArrow good)

/-- Both original target maps in the coefficient functor category. -/
abbrev continuousTopIso :
    (continuousDiagram theta L chi hUncountable hArrow good).obj ⊤ ≅ G :=
  (Under.forget F).mapIso (continuousTopIsoUnder theta L chi hUncountable hArrow good)

/-- Every continuous endpoint leg retains the actual original chosen stage comparison. -/
def continuousEndpoint : continuousDiagram theta L chi hUncountable hArrow good ⟶
    (Functor.const _).obj G where
  app gamma := (continuousDiagram theta L chi hUncountable hArrow good).map (homOfLE le_top) ≫
    (continuousTopIso theta L chi hUncountable hArrow good).hom
  naturality gamma delta h := by
    change (continuousDiagram theta L chi hUncountable hArrow good).map h ≫
        ((continuousDiagram theta L chi hUncountable hArrow good).map (homOfLE le_top) ≫
          (continuousTopIso theta L chi hUncountable hArrow good).hom) =
      ((continuousDiagram theta L chi hUncountable hArrow good).map (homOfLE le_top) ≫
        (continuousTopIso theta L chi hUncountable hArrow good).hom) ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp_assoc]
    exact congrArg (fun k => (continuousDiagram theta L chi hUncountable hArrow good).map k ≫
      (continuousTopIso theta L chi hUncountable hArrow good).hom) (Subsingleton.elim _ _)

/-- The genuine final stage proves the continuous whole original endpoint colimit UP. -/
def continuousEndpointIsColimit :
    IsColimit (Cocone.mk G (continuousEndpoint theta L chi hUncountable hArrow good)) :=
  IsColimit.ofIsoColimit
    (colimitOfDiagramTerminal isTerminalTop
      (continuousDiagram theta L chi hUncountable hArrow good))
    (Cocone.ext (continuousTopIso theta L chi hUncountable hArrow good) (by intro gamma; rfl))

/-- The complete continuous composite is exactly the unchanged original f, with source identity. -/
theorem continuous_root_endpoint :
    (continuousBotIso theta L chi hUncountable hArrow good).inv ≫
      (continuousEndpoint theta L chi hUncountable hArrow good).app ⊥ = f := by
  let m : Under.mk (𝟙 F) ⟶ Under.mk f :=
    (continuousBotIsoUnder theta L chi hUncountable hArrow good).inv ≫
      (continuousDiagramUnder theta L chi hUncountable hArrow good).map (homOfLE bot_le) ≫
        (continuousTopIsoUnder theta L chi hUncountable hArrow good).hom
  simpa only [m, continuousBotIso, continuousTopIso, continuousEndpoint, continuousDiagram,
    Functor.mapIso_inv, Functor.mapIso_hom, Functor.comp_map, Under.forget_map,
    Under.comp_right, Under.mk_hom, Category.id_comp] using Under.w m

/-- Produce the original continuous transfinite presentation from the real birth history. -/
def continuousPresentation : TransfiniteCompositionOfShape
    (ConstructionIndex (HistoryIndex (P := P))) f where
  F := continuousDiagram theta L chi hUncountable hArrow good
  isoBot := continuousBotIso theta L chi hUncountable hArrow good
  isWellOrderContinuous :=
    continuousDiagram_isWellOrderContinuous theta L chi hUncountable hArrow good
  incl := continuousEndpoint theta L chi hUncountable hArrow good
  isColimit := continuousEndpointIsColimit theta L chi hUncountable hArrow good
  fac := continuous_root_endpoint theta L chi hUncountable hArrow good

omit [Category D] [∀ d, PartialOrder (P d)] in
/-- The label stage is exactly the actual original strict predecessor set in the chosen history. -/
theorem continuousPrefix_label (p : HistoryIndex (P := P)) :
    originalPrefix (constructionLabel p) = LowerSet.Iio p := by
  ext j
  constructor
  · intro hj
    by_contra hn
    have hle : p ≤ j := le_of_not_gt hn
    exact (not_lt_of_ge (constructionLabel_strictMono.monotone hle)) hj
  · exact fun hj => constructionLabel_strictMono hj

omit [Category D] [∀ d, PartialOrder (P d)] in
/-- The successor label stage is the same actual original non-strict predecessor set. -/
theorem continuousPrefix_succ_label (p : HistoryIndex (P := P)) :
    originalPrefix (Order.succ (constructionLabel p)) = LowerSet.Iic p := by
  rw [originalPrefix_succ_label, continuousPrefix_label]
  apply sup_eq_right.mpr
  intro j hj
  change j ≤ p
  exact (show j < p from hj).le

/-- The actual strict lower-history colimit compares with the already proved original BEFORE UP. -/
def lowerHistoryBeforeIso (p : HistoryIndex (P := P)) :
    (lowerHistoryData theta L chi hUncountable hArrow good).obj (LowerSet.Iio p) ≅
      Under.mk (before theta L chi hUncountable hArrow good p).root := by
  let M := lowerHistoryData theta L chi hUncountable hArrow good
  exact (M.isColimit (LowerSet.Iio p)).coconePointUniqueUpToIso
    (beforeIsColimit theta L chi hUncountable hArrow good p)

/-- Every original earlier leg survives the actual BEFORE comparison. -/
@[reassoc]
theorem lowerHistoryBeforeIso_fac (p : HistoryIndex (P := P)) (j : Set.Iio p) :
    (lowerHistoryData theta L chi hUncountable hArrow good).ι (LowerSet.Iio p) j ≫
      (lowerHistoryBeforeIso theta L chi hUncountable hArrow good p).hom =
        (beforeCocone theta L chi hUncountable hArrow good p).ι.app j :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    ((lowerHistoryData theta L chi hUncountable hArrow good).isColimit (LowerSet.Iio p))
    (beforeIsColimit theta L chi hUncountable hArrow good p) j

/-- Both original source maps identify the native label stage with the actual BEFORE. -/
def continuousBirthSourceIsoUnder (p : HistoryIndex (P := P)) :
    (continuousDiagramUnder theta L chi hUncountable hArrow good).obj (constructionLabel p) ≅
      Under.mk (before theta L chi hUncountable hArrow good p).root :=
  (lowerHistoryData theta L chi hUncountable hArrow good).functor.mapIso
    (eqToIso (continuousPrefix_label p)) ≪≫
      lowerHistoryBeforeIso theta L chi hUncountable hArrow good p

/-- Both original target maps identify the native successor stage with the actual AFTER. -/
def continuousBirthTargetIsoUnder (p : HistoryIndex (P := P)) :
    (continuousDiagramUnder theta L chi hUncountable hArrow good).obj
        (Order.succ (constructionLabel p)) ≅
      Under.mk (after theta L chi hUncountable hArrow good p).root :=
  (lowerHistoryData theta L chi hUncountable hArrow good).functor.mapIso
    (eqToIso (continuousPrefix_succ_label p)) ≪≫
      (lowerHistoryData theta L chi hUncountable hArrow good).principalIso p

/-- The actual birth inclusion is a complete original morphism under the unchanged source F. -/
def beforeToAfterUnder (p : HistoryIndex (P := P)) :
    Under.mk (before theta L chi hUncountable hArrow good p).root ⟶
      Under.mk (after theta L chi hUncountable hArrow good p).root :=
  Under.homMk (beforeToAfter theta L chi hUncountable hArrow good p).toNatTrans
    (inclusion_root (beforeToAfter theta L chi hUncountable hArrow good p))

/-- The native successor square is proved from every actual earlier original cocone leg. -/
theorem continuousBirthSquareUnder (p : HistoryIndex (P := P)) :
    (continuousBirthSourceIsoUnder theta L chi hUncountable hArrow good p).hom ≫
        beforeToAfterUnder theta L chi hUncountable hArrow good p =
      (continuousDiagramUnder theta L chi hUncountable hArrow good).map
        (homOfLE (Order.le_succ (constructionLabel p))) ≫
          (continuousBirthTargetIsoUnder theta L chi hUncountable hArrow good p).hom := by
  let M := lowerHistoryData theta L chi hUncountable hArrow good
  let B := originalPrefix (constructionLabel p)
  let hB : B ≤ LowerSet.Iio p := (continuousPrefix_label p).le
  let hD : originalPrefix (Order.succ (constructionLabel p)) ≤ LowerSet.Iic p :=
    (continuousPrefix_succ_label p).le
  let hStep : B ≤ originalPrefix (Order.succ (constructionLabel p)) :=
    originalPrefix_mono (Order.le_succ (constructionLabel p))
  let u : Under.mk (before theta L chi hUncountable hArrow good p).root ⟶
      Under.mk (after theta L chi hUncountable hArrow good p).root :=
    beforeToAfterUnder theta L chi hUncountable hArrow good p
  apply (M.isColimit B).hom_ext
  intro j
  change M.ι B j ≫ ((M.map hB ≫
      (lowerHistoryBeforeIso theta L chi hUncountable hArrow good p).hom) ≫ u) =
    M.ι B j ≫ (M.map hStep ≫
      (M.map hD ≫ (M.principalIso p).hom))
  rw [← Category.assoc, ← Category.assoc, M.ι_map hB j, Category.assoc,
    lowerHistoryBeforeIso_fac_assoc theta L chi hUncountable hArrow good p]
  conv_rhs =>
    rw [← Category.assoc, M.ι_map, ← Category.assoc, M.ι_map, M.ι_principalIso_hom]
  apply Under.UnderMorphism.ext
  apply NatTrans.ext
  funext d
  change ((L d).map
      ((earlierToBefore theta L chi hUncountable hArrow good j.1 p
        (LowerSetColimits.memOfLE hB j.2)).le d)).right ≫
      ((L d).map ((beforeToAfter theta L chi hUncountable hArrow good p).le d)).right =
    ((L d).map _).right
  rw [← Under.comp_right, (L d).map_comp]

/-- The full native successor Arrow retains both actual original BEFORE/AFTER maps. -/
def continuousBirthArrowIso (p : HistoryIndex (P := P)) :
    Arrow.mk ((continuousDiagram theta L chi hUncountable hArrow good).map
      (homOfLE (Order.le_succ (constructionLabel p)))) ≅
        Arrow.mk (beforeToAfter theta L chi hUncountable hArrow good p).toNatTrans :=
  Arrow.isoMk
    ((Under.forget F).mapIso
      (continuousBirthSourceIsoUnder theta L chi hUncountable hArrow good p))
    ((Under.forget F).mapIso
      (continuousBirthTargetIsoUnder theta L chi hUncountable hArrow good p))
    (congrArg Under.Hom.right
      (continuousBirthSquareUnder theta L chi hUncountable hArrow good p))

/-- The extra initial transition has the same empty original support and is an isomorphism. -/
theorem continuousBotMapIsIso :
    IsIso ((continuousDiagram theta L chi hUncountable hArrow good).map
      (homOfLE (Order.le_succ (⊥ : ConstructionIndex (HistoryIndex (P := P)))))) := by
  let M := lowerHistoryData theta L chi hUncountable hArrow good
  have e : originalPrefix (⊥ : ConstructionIndex (HistoryIndex (P := P))) =
      originalPrefix (Order.succ ⊥) := originalPrefix_bot.trans originalPrefix_succ_bot.symm
  have hm : homOfLE (originalPrefix_mono
      (Order.le_succ (⊥ : ConstructionIndex (HistoryIndex (P := P))))) = eqToHom e :=
    Subsingleton.elim _ _
  change IsIso ((Under.forget F).map (M.functor.map (homOfLE
    (originalPrefix_mono (Order.le_succ (⊥ : ConstructionIndex (HistoryIndex (P := P))))))))
  rw [hm]
  change IsIso (((Under.forget F).mapIso (M.functor.mapIso (eqToIso e))).hom)
  infer_instance

end ContinuousPresentation

end CategoryTheory.SmallObject.OriginalTransfiniteSliceFiltration

namespace HomotopicalAlgebra.FunctorInjective

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.OriginalTransfiniteSliceFiltration
open CategoryTheory.SmallObject.CompactRootBaseChange

attribute [local instance] constructionIndexWellFounded constructionIndexSuccOrder

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d kappaLP s.equivalence)
  {F G : D ⥤ C} (f : F ⟶ G) (hf : ∀ a : D, cofibrations C (f.app a))

/-- The original bounded history retains the entire actual constructed component-label carrier. -/
abbrev boundedSliceHistoryIndex :=
  HistoryIndex (P := originalComponentLabels d kappaLP s.equivalence b f hf)

/-- On a genuinely bounded original index, the original model constructs the full AFTER diagram. -/
def boundedCofibrationSliceFiltration (hArrow : HasCardinalLT (Arrow D) b.cardinal) :
    boundedSliceHistoryIndex d kappaLP s b f hf ⥤ Under F := by
  letI := originalComponentOrders d kappaLP s.equivalence b f hf
  exact afterDiagram (originalComponentPresentation d kappaLP s.equivalence b f hf)
    (originalComponentLowerData d kappaLP s.equivalence b f hf) b.cardinal b.profile.uncountable
        hArrow
    (originalComponentGood d kappaLP s.equivalence b f hf)

/-- Every original bounded BEFORE is constructed internally from the original component trees. -/
abbrev boundedSliceBefore (hArrow : HasCardinalLT (Arrow D) b.cardinal)
    (p : boundedSliceHistoryIndex d kappaLP s b f hf) :=
  letI := originalComponentOrders d kappaLP s.equivalence b f hf
  before (originalComponentPresentation d kappaLP s.equivalence b f hf)
    (originalComponentLowerData d kappaLP s.equivalence b f hf) b.cardinal b.profile.uncountable
        hArrow
    (originalComponentGood d kappaLP s.equivalence b f hf) p

/-- Every original bounded AFTER is the actual original union-pushout construction. -/
abbrev boundedSliceAfter (hArrow : HasCardinalLT (Arrow D) b.cardinal)
    (p : boundedSliceHistoryIndex d kappaLP s b f hf) :=
  letI := originalComponentOrders d kappaLP s.equivalence b f hf
  after (originalComponentPresentation d kappaLP s.equivalence b f hf)
    (originalComponentLowerData d kappaLP s.equivalence b f hf) b.cardinal b.profile.uncountable
        hArrow
    (originalComponentGood d kappaLP s.equivalence b f hf) p

/-- The original bounded birth contains the actual patch, overlap and both full original maps. -/
abbrev boundedSliceBirth (hArrow : HasCardinalLT (Arrow D) b.cardinal)
    (p : boundedSliceHistoryIndex d kappaLP s b f hf) :=
  letI := originalComponentOrders d kappaLP s.equivalence b f hf
  birth (originalComponentPresentation d kappaLP s.equivalence b f hf)
    (originalComponentLowerData d kappaLP s.equivalence b f hf) b.cardinal b.profile.uncountable
        hArrow
    (originalComponentGood d kappaLP s.equivalence b f hf) p

/-- The original model constructs each original bounded BEFORE cocone. -/
abbrev boundedSliceBeforeCocone (hArrow : HasCardinalLT (Arrow D) b.cardinal)
    (p : boundedSliceHistoryIndex d kappaLP s b f hf) :=
  letI := originalComponentOrders d kappaLP s.equivalence b f hf
  beforeCocone (originalComponentPresentation d kappaLP s.equivalence b f hf)
    (originalComponentLowerData d kappaLP s.equivalence b f hf) b.cardinal b.profile.uncountable
        hArrow
    (originalComponentGood d kappaLP s.equivalence b f hf) p

/-- The original lower data proves the complete constructed bounded BEFORE UP. -/
def boundedSliceBeforeIsColimit (hArrow : HasCardinalLT (Arrow D) b.cardinal)
    (p : boundedSliceHistoryIndex d kappaLP s b f hf) :
    IsColimit (boundedSliceBeforeCocone d kappaLP s b f hf hArrow p) := by
  letI := originalComponentOrders d kappaLP s.equivalence b f hf
  exact beforeIsColimit (originalComponentPresentation d kappaLP s.equivalence b f hf)
    (originalComponentLowerData d kappaLP s.equivalence b f hf) b.cardinal b.profile.uncountable
        hArrow
    (originalComponentGood d kappaLP s.equivalence b f hf) p

/-- The bounded original endpoint cocone has the unchanged entire original arrow f. -/
abbrev boundedSliceEndpointCocone (hArrow : HasCardinalLT (Arrow D) b.cardinal) :
    Cocone (boundedCofibrationSliceFiltration d kappaLP s b f hf hArrow) :=
  letI := originalComponentOrders d kappaLP s.equivalence b f hf
  endpointCocone (originalComponentPresentation d kappaLP s.equivalence b f hf)
    (originalComponentLowerData d kappaLP s.equivalence b f hf) b.cardinal b.profile.uncountable
        hArrow
    (originalComponentGood d kappaLP s.equivalence b f hf)

/-- Actual constructed label exhaustion gives the bounded original endpoint UP at f. -/
def boundedSliceEndpointIsColimit (hArrow : HasCardinalLT (Arrow D) b.cardinal) :
    IsColimit (boundedSliceEndpointCocone d kappaLP s b f hf hArrow) := by
  letI := originalComponentOrders d kappaLP s.equivalence b f hf
  exact endpointIsColimit (originalComponentPresentation d kappaLP s.equivalence b f hf)
    (originalComponentLowerData d kappaLP s.equivalence b f hf) b.cardinal b.profile.uncountable
        hArrow
    (originalComponentGood d kappaLP s.equivalence b f hf)

/-- The selected source index is precisely the actual s.index, with its original category. -/
def originalFiltrationSelectedIndex : Functor.EssentialIndexData.{w} s.index C where
  index := s.index
  indexCategory := s.indexCategory
  equivalence := CategoryTheory.Equivalence.refl
  locallySmallCoefficient := s.locallySmallCoefficient

/-- Reconstruct only the genuine source profile on the SAME selected index and SAME ranks. -/
def originalFiltrationSelectedSource :
    BoundedConstruction d kappaLP (originalFiltrationSelectedIndex s).equivalence := by
  let profile := CategoryTheory.Presentable.BoundedDiagramProfile.of_bounds C kappaLP
    (originalFiltrationSelectedIndex s).equivalence kappa d.I d.J b.cardinal b.profile.lp_le
    b.profile.generation_le b.profile.uncountable b.profile.arrows
    (fun i => ⟨b.profile.sourceI i, b.profile.targetI i⟩)
    (fun j => ⟨b.profile.sourceJ j, b.profile.targetJ j⟩)
  letI : IsCardinalLocallyPresentable (s.index ⥤ C) b.cardinal :=
    profile.diagramLocallyPresentable
  exact
    { cardinal := b.cardinal
      regular := inferInstance
      profile := profile
      family := boundedGeneratorData s.index C b.cardinal }

/-- The same actual χ is retained, without increasing the original generation cardinal κ. -/
theorem originalFiltrationSelectedSource_cardinal :
    (originalFiltrationSelectedSource d kappaLP s b).cardinal = b.cardinal := rfl

/-- The selected Arrow bound comes from the original profile's same chosen index. -/
theorem originalFiltrationSelectedArrowBound : HasCardinalLT (Arrow s.index) b.cardinal :=
  b.profile.arrows

/-- The exact original functor-category equivalence retains both original index functors. -/
abbrev originalFiltrationEquivalence := s.equivalence.congrLeft (E := C)

/-- Return every selected slice to the unchanged original source F. -/
def originalFiltrationUnderTransport :
    Under ((originalFiltrationEquivalence s).functor.obj F) ⥤ Under F :=
  Under.post (originalFiltrationEquivalence s).inverse ⋙
    Under.map ((originalFiltrationEquivalence s).unitIso.app F).hom

/-- Both parts of this actual source-fixed transport are equivalences of under categories. -/
instance originalFiltrationUnderTransportIsEquivalence :
    (originalFiltrationUnderTransport s (F := F)).IsEquivalence := by
  dsimp only [originalFiltrationUnderTransport]
  infer_instance

omit [ModelCategory C] in
/-- Every original Hom action is retained by the exact original inverse precomposition. -/
theorem originalFiltrationUnderTransport_action
    (U : Under ((originalFiltrationEquivalence s).functor.obj F))
    {a c : D} (g : a ⟶ c) :
    ((originalFiltrationUnderTransport s).obj U).right.map g =
      U.right.map (s.equivalence.functor.map g) := rfl

omit [ModelCategory C] in
/-- Every whole original inclusion retains its actual selected component function. -/
theorem originalFiltrationUnderTransport_map
    {U V : Under ((originalFiltrationEquivalence s).functor.obj F)} (m : U ⟶ V) (a : D) :
    ((originalFiltrationUnderTransport s).map m).right.app a =
      m.right.app (s.equivalence.functor.obj a) := rfl

omit [ModelCategory C] in
/-- The actual transport has the original source F and its full original root-square function. -/
theorem originalFiltrationUnderTransport_root
    (U : Under ((originalFiltrationEquivalence s).functor.obj F)) (a : D) :
    ((originalFiltrationUnderTransport s).obj U).hom.app a =
      ((originalFiltrationEquivalence s).unitIso.app F).hom.app a ≫
        U.hom.app (s.equivalence.functor.obj a) := rfl

/-- The actual returned whole endpoint retains both original G comparison maps under original F. -/
def originalFiltrationEndpointIso :
    (originalFiltrationUnderTransport s).obj
      (Under.mk ((originalFiltrationEquivalence s).functor.map f)) ≅ Under.mk f :=
  Under.isoMk ((originalFiltrationEquivalence s).unitIso.app G).symm (by
    change (((originalFiltrationEquivalence s).unitIso.app F).hom ≫
        ((originalFiltrationEquivalence s).functor ⋙
          (originalFiltrationEquivalence s).inverse).map f) ≫
        ((originalFiltrationEquivalence s).unitIso.app G).inv = f
    have hn := (originalFiltrationEquivalence s).unitIso.hom.naturality f
    change f ≫ ((originalFiltrationEquivalence s).unitIso.app G).hom =
      ((originalFiltrationEquivalence s).unitIso.app F).hom ≫
        ((originalFiltrationEquivalence s).functor ⋙
          (originalFiltrationEquivalence s).inverse).map f at hn
    calc
      _ = (f ≫ ((originalFiltrationEquivalence s).unitIso.app G).hom) ≫
          ((originalFiltrationEquivalence s).unitIso.app G).inv :=
        congrArg (fun k => k ≫ ((originalFiltrationEquivalence s).unitIso.app G).inv) hn.symm
      _ = f := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- The original objectwise cofibration is restricted along the actual inverse index functor. -/
abbrev originalFiltrationSelectedArrow := (originalFiltrationEquivalence s).functor.map f

include hf in
/-- All selected component cofibrations are actual original coefficient cofibrations. -/
theorem originalFiltrationSelectedCofibration (a : s.index) :
    cofibrations C ((originalFiltrationSelectedArrow s f).app a) :=
  hf (s.equivalence.inverse.obj a)

/-- The original filtration's working-universe index is the full constructed selected-label sum. -/
abbrev originalSliceHistoryIndex : Type w :=
  boundedSliceHistoryIndex d kappaLP (originalFiltrationSelectedIndex s)
    (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
    (originalFiltrationSelectedCofibration s f hf)

/-- Construct the continuous original slice filtration from the original coefficient model.
The SAME selected Arrow bound is derived from b.profile.arrows; no Arrow bound on
the arbitrary original D or completed history is a premise. -/
def originalCofibrationSliceFiltration : originalSliceHistoryIndex d kappaLP s b f hf ⥤ Under F :=
  boundedCofibrationSliceFiltration d kappaLP (originalFiltrationSelectedIndex s)
    (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
    (originalFiltrationSelectedCofibration s f hf) b.profile.arrows ⋙
      originalFiltrationUnderTransport s

/-- The original endpoint cocone has the literal original f, including empty label carriers. -/
def originalSliceEndpointCocone : Cocone (originalCofibrationSliceFiltration d kappaLP s b f hf) :=
  ((originalFiltrationUnderTransport s).mapCocone
    (boundedSliceEndpointCocone d kappaLP (originalFiltrationSelectedIndex s)
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf) b.profile.arrows)).extend
        (originalFiltrationEndpointIso s f).hom

/-- The original target is literally the original endpoint under its unchanged source F. -/
theorem originalSliceEndpointCocone_point :
    (originalSliceEndpointCocone d kappaLP s b f hf).pt = Under.mk f := rfl

/-- Actual original label exhaustion and the original equivalence prove the full endpoint UP. -/
def originalSliceEndpointIsColimit :
    IsColimit (originalSliceEndpointCocone d kappaLP s b f hf) := by
  refine IsColimit.ofIsoColimit
    (isColimitOfPreserves (originalFiltrationUnderTransport s)
      (boundedSliceEndpointIsColimit d kappaLP (originalFiltrationSelectedIndex s)
        (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
        (originalFiltrationSelectedCofibration s f hf) b.profile.arrows))
    (Cocone.ext (originalFiltrationEndpointIso s f) ?_)
  intro p
  rfl

/-- The actual chosen bounded birth on the same original selected index. -/
abbrev originalSliceBirth (p : originalSliceHistoryIndex d kappaLP s b f hf) :=
  boundedSliceBirth d kappaLP (originalFiltrationSelectedIndex s)
    (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
    (originalFiltrationSelectedCofibration s f hf) b.profile.arrows p

/-- The actual component orders are the unchanged orders of the internally produced trees. -/
abbrev originalSliceComponentOrders :=
  originalComponentOrders d kappaLP (originalFiltrationSelectedIndex s).equivalence
    (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
    (originalFiltrationSelectedCofibration s f hf)

/-- Every original successor retains all four actual natural-transformation functions. -/
theorem originalSliceSuccessorIsPushout (p : originalSliceHistoryIndex d kappaLP s b f hf) :
    letI := originalSliceComponentOrders d kappaLP s b f hf
    IsPushout
      ((originalFiltrationEquivalence s).inverse.map
        (originalSliceBirth d kappaLP s b f hf p).intoBefore.toNatTrans)
      ((originalFiltrationEquivalence s).inverse.map
        (originalSliceBirth d kappaLP s b f hf p).intoPatch.toNatTrans)
      ((originalFiltrationEquivalence s).inverse.map
        (originalSliceBirth d kappaLP s b f hf p).beforeInclusion.toNatTrans)
      ((originalFiltrationEquivalence s).inverse.map
        (originalSliceBirth d kappaLP s b f hf p).patchInclusion.toNatTrans) := by
  let := originalSliceComponentOrders d kappaLP s b f hf
  exact (originalSliceBirth d kappaLP s b f hf p).isPushout.map
    (originalFiltrationEquivalence s).inverse

/-- Every total birth-label bound is derived from its actual chosen compact-support patch. -/
theorem originalSliceBirthLabelsBound (p : originalSliceHistoryIndex d kappaLP s b f hf) :
    letI := originalSliceComponentOrders d kappaLP s b f hf
    HasCardinalLT (originalSliceBirth d kappaLP s b f hf p).NewLabels b.cardinal := by
  let := originalSliceComponentOrders d kappaLP s b f hf
  exact (originalSliceBirth d kappaLP s b f hf p).newLabels_bound

/-- Every actual original BEFORE cocone retains the full source-fixed original transport. -/
abbrev originalSliceBeforeCocone (p : originalSliceHistoryIndex d kappaLP s b f hf) :=
  (originalFiltrationUnderTransport s).mapCocone
    (boundedSliceBeforeCocone d kappaLP (originalFiltrationSelectedIndex s)
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf) b.profile.arrows p)

/-- The actual lower-limit UP survives the full original under-category equivalence. -/
def originalSliceBeforeIsColimit (p : originalSliceHistoryIndex d kappaLP s b f hf) :
    IsColimit (originalSliceBeforeCocone d kappaLP s b f hf p) :=
  isColimitOfPreserves (originalFiltrationUnderTransport s)
    (boundedSliceBeforeIsColimit d kappaLP (originalFiltrationSelectedIndex s)
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf) b.profile.arrows p)

/-- The original bounded source constructs its native continuous transfinite presentation. -/
def boundedCofibrationTransfiniteSliceFiltration (hArrow : HasCardinalLT (Arrow D) b.cardinal) :
    TransfiniteCompositionOfShape
      (ConstructionIndex (boundedSliceHistoryIndex d kappaLP s b f hf)) f := by
  letI := originalComponentOrders d kappaLP s.equivalence b f hf
  exact continuousPresentation (originalComponentPresentation d kappaLP s.equivalence b f hf)
    (originalComponentLowerData d kappaLP s.equivalence b f hf) b.cardinal b.profile.uncountable
        hArrow
    (originalComponentGood d kappaLP s.equivalence b f hf)

/-- Both whole-arrow maps come from the same original functor-category equivalence. -/
def originalFiltrationArrowIso :
    Arrow.mk ((originalFiltrationEquivalence s).inverse.map
      (originalFiltrationSelectedArrow s f)) ≅ Arrow.mk f :=
  Arrow.isoMk ((originalFiltrationEquivalence s).unitIso.app F).symm
    ((originalFiltrationEquivalence s).unitIso.app G).symm (by
      have hn := (originalFiltrationEquivalence s).unitIso.inv.naturality f
      change (originalFiltrationEquivalence s).inverse.map
          (originalFiltrationSelectedArrow s f) ≫
          ((originalFiltrationEquivalence s).unitIso.app G).inv =
        ((originalFiltrationEquivalence s).unitIso.app F).inv ≫ f at hn
      exact hn.symm)

/-- Construct the native continuous filtration of the SAME original whole arrow f.
The actual selected index supplies every bound, while both original whole-arrow
comparisons and all original functor actions are retained by the actual equivalence. -/
def originalCofibrationTransfiniteSliceFiltration :
    TransfiniteCompositionOfShape
      (ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf)) f := by
  letI : PreservesWellOrderContinuousOfShape
      (ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf))
      (originalFiltrationEquivalence s).inverse := {}
  exact ((boundedCofibrationTransfiniteSliceFiltration d kappaLP
    (originalFiltrationSelectedIndex s) (originalFiltrationSelectedSource d kappaLP s b)
    (originalFiltrationSelectedArrow s f) (originalFiltrationSelectedCofibration s f hf)
    b.profile.arrows).map (originalFiltrationEquivalence s).inverse).ofArrowIso
      (originalFiltrationArrowIso s f)

/-- The complete native filtration composite is the literal original natural transformation f. -/
theorem originalTransfiniteFiltration_fac :
    (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).isoBot.inv ≫
      (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).incl.app ⊥ = f :=
  (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).fac

/-- The native continuous filtration retains the full original action on every original Hom. -/
theorem originalTransfiniteFiltration_action
    (gamma : ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf))
    {a c : D} (g : a ⟶ c) :
    ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.obj gamma).map g =
      (((boundedCofibrationTransfiniteSliceFiltration d kappaLP
        (originalFiltrationSelectedIndex s) (originalFiltrationSelectedSource d kappaLP s b)
        (originalFiltrationSelectedArrow s f) (originalFiltrationSelectedCofibration s f hf)
        b.profile.arrows).F.obj gamma).map (s.equivalence.functor.map g)) := rfl

/-- Every native filtration inclusion retains its actual original selected component function. -/
theorem originalTransfiniteFiltration_map
    {gamma delta : ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf)}
    (h : gamma ⟶ delta) (a : D) :
    ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map h).app a =
      ((boundedCofibrationTransfiniteSliceFiltration d kappaLP (originalFiltrationSelectedIndex s)
        (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
        (originalFiltrationSelectedCofibration s f hf) b.profile.arrows).F.map h).app
          (s.equivalence.functor.obj a) := rfl

/-- Each genuine native successor Arrow has both original comparison maps to its actual birth. -/
def originalTransfiniteFiltrationBirthIso (p : originalSliceHistoryIndex d kappaLP s b f hf) :
    letI := originalSliceComponentOrders d kappaLP s b f hf
    Arrow.mk ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map
      (homOfLE (Order.le_succ (constructionLabel p)))) ≅
        Arrow.mk ((originalFiltrationEquivalence s).inverse.map
          (originalSliceBirth d kappaLP s b f hf p).beforeInclusion.toNatTrans) := by
  letI := originalSliceComponentOrders d kappaLP s b f hf
  exact (originalFiltrationEquivalence s).inverse.mapArrow.mapIso
    (continuousBirthArrowIso
      (originalComponentPresentation d kappaLP (originalFiltrationSelectedIndex s).equivalence
        (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
        (originalFiltrationSelectedCofibration s f hf))
      (originalComponentLowerData d kappaLP (originalFiltrationSelectedIndex s).equivalence
        (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
        (originalFiltrationSelectedCofibration s f hf))
      b.cardinal b.profile.uncountable b.profile.arrows
      (originalComponentGood d kappaLP (originalFiltrationSelectedIndex s).equivalence
        (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
        (originalFiltrationSelectedCofibration s f hf)) p)

/-- Every native original stage has its actual root under the unchanged original source F. -/
def originalTransfiniteFiltrationUnder :
    ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf) ⥤ Under F := by
  letI := originalSliceComponentOrders d kappaLP s b f hf
  exact continuousDiagramUnder
    (originalComponentPresentation d kappaLP (originalFiltrationSelectedIndex s).equivalence
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf))
    (originalComponentLowerData d kappaLP (originalFiltrationSelectedIndex s).equivalence
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf))
    b.cardinal b.profile.uncountable b.profile.arrows
    (originalComponentGood d kappaLP (originalFiltrationSelectedIndex s).equivalence
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf)) ⋙ originalFiltrationUnderTransport s

/-- The complete native original diagram is the same actual source-fixed slice diagram. -/
theorem originalTransfiniteFiltration_under_forget :
    originalTransfiniteFiltrationUnder d kappaLP s b f hf ⋙ Under.forget F =
      (originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F := rfl

/-- The original initial transition is an isomorphism by actual empty-support equality. -/
theorem originalTransfiniteFiltrationBotMapIsIso :
    IsIso ((originalCofibrationTransfiniteSliceFiltration d kappaLP s b f hf).F.map
      (homOfLE (Order.le_succ
        (⊥ : ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf))))) := by
  let := originalSliceComponentOrders d kappaLP s b f hf
  let h := continuousBotMapIsIso
    (originalComponentPresentation d kappaLP (originalFiltrationSelectedIndex s).equivalence
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf))
    (originalComponentLowerData d kappaLP (originalFiltrationSelectedIndex s).equivalence
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf))
    b.cardinal b.profile.uncountable b.profile.arrows
    (originalComponentGood d kappaLP (originalFiltrationSelectedIndex s).equivalence
      (originalFiltrationSelectedSource d kappaLP s b) (originalFiltrationSelectedArrow s f)
      (originalFiltrationSelectedCofibration s f hf))
  change IsIso ((originalFiltrationEquivalence s).inverse.map _)
  let : IsIso ((boundedCofibrationTransfiniteSliceFiltration d kappaLP
      (originalFiltrationSelectedIndex s) (originalFiltrationSelectedSource d kappaLP s b)
      (originalFiltrationSelectedArrow s f) (originalFiltrationSelectedCofibration s f hf)
      b.profile.arrows).F.map (homOfLE (Order.le_succ
        (⊥ : ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf))))) := h
  infer_instance

end HomotopicalAlgebra.FunctorInjective
