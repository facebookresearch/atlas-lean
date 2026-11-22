/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionColimits

/-!
# Actual predecessor colimits for the weaker one-cell extension order

Each old predecessor cocone is the original selected cocone on the literal
embedded old labels. The new predecessor cocone is the original selected
lower cofan. Their universal properties use the complete original colimit
data and the actual old/new predecessor order isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.GoodCellExtensionPredecessors

open Limits LowerSetColimits GoodCellExtensionOrder GoodCellExtensionDiagram
  GoodCellExtensionColimits

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {P : Type w} [PartialOrder P] {A : Type t} {s : A → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (B : LowerSet P) (i : A) (a : (s i).left ⟶ (L.obj B).right)

/-- Every embedded old predecessor keeps its exact original selected cofan leg. -/
def oldPredLeg (p : P) :
    letI := extensionOrder B
    ∀ u : LowerSet.Iio (Index.old p),
      ((restriction (diagram T L B i a) (LowerSet.Iio (Index.old p))).obj u) ⟶
        T.predecessorObj p := by
  letI := extensionOrder B
  rintro ⟨⟨u⟩, hu⟩
  cases u with
  | none => exact False.elim ((new_not_lt_old B p) hu)
  | some q =>
    exact (T.predecessor p).cocone.ι.app ⟨q, (old_lt_old B q p).1 hu⟩

/-- The old selected predecessor point has its actual full extension predecessor cocone. -/
def oldPredCocone (p : P) :
    letI := extensionOrder B
    Cocone (restriction (diagram T L B i a) (LowerSet.Iio (Index.old p))) := by
  letI := extensionOrder B
  refine {
    pt := T.predecessorObj p
    ι := {
      app := oldPredLeg T L B i a p
      naturality := ?_ } }
  rintro ⟨⟨u⟩, hu⟩ ⟨⟨v⟩, hv⟩ h
  cases u with
  | none => exact False.elim ((new_not_lt_old B p) hu)
  | some u =>
    cases v with
    | none => exact False.elim ((new_not_lt_old B p) hv)
    | some v =>
      have huv : u ≤ v := leOfHom h
      have hu' : u < p := (old_lt_old B u p).1 hu
      have hv' : v < p := (old_lt_old B v p).1 hv
      change T.diagram.map (homOfLE huv) ≫ (T.predecessor p).cocone.ι.app ⟨v, hv'⟩ =
        (T.predecessor p).cocone.ι.app ⟨u, hu'⟩ ≫ 𝟙 _
      exact ((T.predecessor p).cocone.w
        (homOfLE huv : (⟨u, hu'⟩ : LowerSet.Iio p) ⟶ ⟨v, hv'⟩)).trans
          (Category.comp_id _).symm

/-- Convert only the actual new-index cocone to the same original old predecessor diagram. -/
def oldConverted (p : P) :
    letI := extensionOrder B
    Cocone (restriction (diagram T L B i a) (LowerSet.Iio (Index.old p))) →
      Cocone (restriction T.diagram (LowerSet.Iio p)) := by
  letI := extensionOrder B
  intro d
  let e := oldPredecessorsIso B p
  refine {
    pt := d.pt
    ι := {
      app := fun q => d.ι.app (e q)
      naturality := ?_ } }
  intro q r h
  let h' : e q ⟶ e r := homOfLE (e.monotone (leOfHom h))
  have hd := d.w h'
  change (restriction T.diagram (LowerSet.Iio p)).map h ≫ d.ι.app (e r) =
    d.ι.app (e q) at hd
  exact hd.trans (Category.comp_id _).symm

/-- The original old predecessor UP proves the actual extension predecessor UP. -/
def oldPredIsColimit (p : P) :
    letI := extensionOrder B
    IsColimit (oldPredCocone T L B i a p) := by
  letI := extensionOrder B
  refine {
    desc := fun d => (T.predecessor p).isColimit.desc (oldConverted T L B i a p d)
    fac := ?_
    uniq := ?_ }
  · rintro d ⟨⟨u⟩, hu⟩
    cases u with
    | none => exact False.elim ((new_not_lt_old B p) hu)
    | some u =>
      have hu' : u < p := (old_lt_old B u p).1 hu
      exact (T.predecessor p).isColimit.fac (oldConverted T L B i a p d) ⟨u, hu'⟩
  · intro d m hm
    apply (T.predecessor p).isColimit.uniq (oldConverted T L B i a p d) m
    intro q
    exact hm (oldPredecessorsIso B p q)

/-- Every actual new predecessor keeps its original selected lower cofan leg. -/
def newPredLeg :
    letI := extensionOrder B
    ∀ u : LowerSet.Iio (Index.new : Index P),
      ((restriction (diagram T L B i a) (LowerSet.Iio (Index.new : Index P))).obj u) ⟶
        L.obj B := by
  letI := extensionOrder B
  rintro ⟨⟨u⟩, hu⟩
  cases u with
  | none => exact False.elim ((lt_irrefl (Index.new : Index P)) hu)
  | some q => exact L.ι B ⟨q, (old_lt_new B q).1 hu⟩

/-- The new predecessor point is the original complete selected lower cocone. -/
def newPredCocone :
    letI := extensionOrder B
    Cocone (restriction (diagram T L B i a) (LowerSet.Iio (Index.new : Index P))) := by
  letI := extensionOrder B
  refine {
    pt := L.obj B
    ι := {
      app := newPredLeg T L B i a
      naturality := ?_ } }
  rintro ⟨⟨u⟩, hu⟩ ⟨⟨v⟩, hv⟩ h
  cases u with
  | none => exact False.elim ((lt_irrefl (Index.new : Index P)) hu)
  | some u =>
    cases v with
    | none => exact False.elim ((lt_irrefl (Index.new : Index P)) hv)
    | some v =>
      have huv : u ≤ v := leOfHom h
      have hu' : u ∈ B := (old_lt_new B u).1 hu
      have hv' : v ∈ B := (old_lt_new B v).1 hv
      change T.diagram.map (homOfLE huv) ≫ L.ι B ⟨v, hv'⟩ =
        L.ι B ⟨u, hu'⟩ ≫ 𝟙 _
      exact ((L.cocone B).w (homOfLE huv : (⟨u, hu'⟩ : B) ⟶ ⟨v, hv'⟩)).trans
        (Category.comp_id _).symm

/-- Convert the actual new predecessor cocone to the same original lower diagram. -/
def newConverted :
    letI := extensionOrder B
    Cocone (restriction (diagram T L B i a) (LowerSet.Iio (Index.new : Index P))) →
      Cocone (restriction T.diagram B) := by
  letI := extensionOrder B
  intro d
  let e := newPredecessorsIso B
  refine {
    pt := d.pt
    ι := {
      app := fun q => d.ι.app (e q)
      naturality := ?_ } }
  intro q r h
  let h' : e q ⟶ e r := homOfLE (e.monotone (leOfHom h))
  have hd := d.w h'
  change (restriction T.diagram B).map h ≫ d.ι.app (e r) = d.ι.app (e q) at hd
  exact hd.trans (Category.comp_id _).symm

/-- The actual original selected lower UP proves the complete new predecessor colimit. -/
def newPredIsColimit :
    letI := extensionOrder B
    IsColimit (newPredCocone T L B i a) := by
  letI := extensionOrder B
  refine {
    desc := fun d => (L.isColimit B).desc (newConverted T L B i a d)
    fac := ?_
    uniq := ?_ }
  · rintro d ⟨⟨u⟩, hu⟩
    cases u with
    | none => exact False.elim ((lt_irrefl (Index.new : Index P)) hu)
    | some u =>
      have hu' : u ∈ B := (old_lt_new B u).1 hu
      exact (L.isColimit B).fac (newConverted T L B i a d) ⟨u, hu'⟩
  · intro d m hm
    apply (L.isColimit B).uniq (newConverted T L B i a d) m
    intro q
    exact hm (newPredecessorsIso B q)

/-- The old complete predecessor data retains the original point and actual embedded cofan. -/
def oldPredecessorData (p : P) :
    letI := extensionOrder B
    ColimitCocone (restriction (diagram T L B i a) (LowerSet.Iio (Index.old p))) := by
  letI := extensionOrder B
  exact ⟨oldPredCocone T L B i a p, oldPredIsColimit T L B i a p⟩

/-- The new complete predecessor data uses its original selected lower point and cofan. -/
def newPredecessorData :
    letI := extensionOrder B
    ColimitCocone (restriction (diagram T L B i a) (LowerSet.Iio (Index.new : Index P))) := by
  letI := extensionOrder B
  exact ⟨newPredCocone T L B i a, newPredIsColimit T L B i a⟩

end CategoryTheory.SmallObject.GoodCellExtensionPredecessors
