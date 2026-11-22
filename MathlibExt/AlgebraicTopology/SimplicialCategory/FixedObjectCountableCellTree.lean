/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectBoundaryGoodTree
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectBoundaryIterationCountability
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.UnderColimits
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerRestriction

/-!
# Countable full Homs of the actual original lower cell pieces

The original countable root and countable original generator ends remain
in every actual original predecessor colimit and pushout. A tree with
countable original predecessors therefore has countable full Homs at
every vertex. Each countable original lower support retains countable
full Homs in its SAME selected colimit, without a weak-interval premise.
-/

noncomputable section
universe u v
open CategoryTheory Limits SmallObject

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.CountableCellTree
open LowerSetColimits UnderColimits OriginalBoundaryGoodTree
variable {O : Type u} [Countable O]

/-- The complete original root-adjoined colimit of countable stages retains countable full Homs. -/
theorem of_underColimit {J : Type u} [Category.{u} J] [Countable J]
    {X : FixedObjects O} [CountableHoms X] {F : J ⥤ Under X}
    [∀ j, CountableHoms (F.obj j).right] (c : ColimitCocone F) : CountableHoms c.cocone.pt.right := by
  let decode : WithInitial J → Option J
    | .star => none
    | .of j => some j
  have hd : Function.Injective decode := by
    intro j k h
    cases j <;> cases k <;> simp only [decode] at h
    · exact congrArg WithInitial.of (Option.some.inj h)
    · cases h
    · cases h
    · rfl
  let _ : Countable (WithInitial J) := hd.countable
  have hstage (j : WithInitial J) : CountableHoms ((adjoinedDiagram (Y := F)).obj j) := by
    cases j with
    | star => exact inferInstanceAs (CountableHoms X)
    | of j => exact inferInstanceAs (CountableHoms (F.obj j).right)
  let _ : ∀ j, CountableHoms ((adjoinedDiagram (Y := F)).obj j) := hstage
  exact countableHoms_of_isColimit (adjoinedColimit c).isColimit

variable {P : Type u} [PartialOrder P] {A : Type v} {s : A → Arrow (FixedObjects O)}
  {X : FixedObjects O} [CountableHoms X] (T : CellTree s X (P := P))

/-- A genuine original predecessor bound below ℵ₁ is exactly countability of the original label set. -/
theorem countable_of_rank_bound {I : Type u} (h : HasCardinalLT I rank.{u}) : Countable I :=
  Cardinal.mk_le_aleph0_iff.mp (Cardinal.lt_aleph_one_iff.mp
    ((hasCardinalLT_iff_cardinal_mk_lt I rank).mp h))

/-- Every SAME full original vertex Hom is countable through its actual countable predecessor colimit and cell
pushout. -/
theorem vertex (good : T.IsGood rank.{u})
    (hs : ∀ p : P, CountableHoms (s (T.label p)).left)
    (ht : ∀ p : P, CountableHoms (s (T.label p)).right) (p : P) :
    CountableHoms (T.vertex p).right := by
  refine T.wellFounded.induction
    (C := fun q => CountableHoms (T.vertex q).right) p ?_
  intro p ih
  let _ : Countable (Set.Iio p) := countable_of_rank_bound (good.predecessor_lt p)
  have hp : Function.Injective (fun q : LowerSet.Iio p => (⟨q.1, q.2⟩ : Set.Iio p)) := by
    intro q r h
    exact Subtype.ext (congrArg Subtype.val h)
  let _ : Countable (LowerSet.Iio p) := hp.countable
  let _ : ∀ q : LowerSet.Iio p,
      CountableHoms ((restriction T.diagram (LowerSet.Iio p)).obj q).right :=
    fun q => ih q.1 q.2
  let _ : CountableHoms (T.predecessorObj p).right := of_underColimit (T.predecessor p)
  let _ : CountableHoms (s (T.label p)).left := hs p
  let _ : CountableHoms (s (T.label p)).right := ht p
  let _ : CountableHoms (pushout (T.attaching p) (s (T.label p)).hom) := inferInstance
  exact countableHoms_of_iso (T.isPushout p).isoPushout

/-- The SAME actual selected original lower piece retains countable entire Homs at every original ordered pair. -/
theorem lower (good : T.IsGood rank.{u})
    (hs : ∀ p : P, CountableHoms (s (T.label p)).left)
    (ht : ∀ p : P, CountableHoms (s (T.label p)).right)
    (L : LowerSetColimitData T.diagram) (B : LowerSet P)
    (hB : HasCardinalLT (B : Set P) rank.{u}) : CountableHoms (L.obj B).right := by
  let _ : Countable (B : Set P) := countable_of_rank_bound hB
  let _ : ∀ p : B, CountableHoms ((restriction T.diagram B).obj p).right :=
    fun p => vertex T good hs ht p.1
  exact of_underColimit ⟨L.cocone B, L.isColimit B⟩

end CategoryTheory.SimplicialEnrichment.FixedObjects.CountableCellTree
