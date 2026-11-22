/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.KanMarkCells
import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-!
# Kan marking cells and the original equivalence edges

The actual core of a quasicategory is Kan and contains precisely its
original equivalence edges. Applying the Kan marking condition to this
core proves that every such edge is marked. Conversely, every edge of a
Kan source is an equivalence, so marking equivalences suffices for all
these original maps. This is a semantic characterization of the large
Kan-source family, not a small-generation assertion.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Lifting all Kan marking cells marks every original equivalence edge of a quasicategory. -/
theorem equivalence_mem_marking_of_kanMarkCells {Y : Marked.{u}} {B : SSet.{u}}
    (p : Y ⟶ max B) [Quasicategory Y.toSSet]
    (hk : ∀ (K : SSet.{u}) [KanComplex K], HasLiftingProperty (kanMarkCell K) p)
    {x y : Y.toSSet _⦋0⦌} (e : Edge x y) (he : e.IsEquivalence) :
    e.edge ∈ Y.marking := by
  have hs : e.edge ∈ (core Y.toSSet).obj (op ⦋1⦌) :=
    mem_core_obj_one_iff.mpr (he.of_edge_eq rfl)
  exact (kanMarkCell_rlp_iff (core Y.toSSet : SSet.{u}) p).mp
    (hk (core Y.toSSet : SSet.{u})) (core Y.toSSet).ι ⟨e.edge, hs⟩

/-- Marking every equivalence makes every original map from a Kan source marked. -/
theorem kanMarkCell_of_equivalences_marked {Y : Marked.{u}} {B : SSet.{u}}
    (p : Y ⟶ max B)
    (hm : ∀ (e : Y.toSSet _⦋1⦌), (Edge.mk' e).IsEquivalence → e ∈ Y.marking)
    (K : SSet.{u}) [KanComplex K] : HasLiftingProperty (kanMarkCell K) p := by
  apply (kanMarkCell_rlp_iff K p).mpr
  intro f e
  exact hm _ (((Edge.isEquivalence_of_kanComplex (Edge.mk' e)).map f).of_edge_eq rfl)

/-- The large Kan-source lifting family is exactly marking the native equivalence edges. -/
theorem kanMarkCells_rlp_iff_equivalences_marked {Y : Marked.{u}} {B : SSet.{u}}
    (p : Y ⟶ max B) [Quasicategory Y.toSSet] :
    (∀ (K : SSet.{u}) [KanComplex K], HasLiftingProperty (kanMarkCell K) p) ↔
      ∀ (e : Y.toSSet _⦋1⦌), (Edge.mk' e).IsEquivalence → e ∈ Y.marking := by
  constructor
  · intro hk e he
    exact equivalence_mem_marking_of_kanMarkCells p hk (Edge.mk' e) he
  · intro hm K hK
    exact kanMarkCell_of_equivalences_marked p hm K

end SSet.Marked
