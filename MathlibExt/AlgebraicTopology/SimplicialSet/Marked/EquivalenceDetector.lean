/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EquivalenceMarking
import MathlibExt.AlgebraicTopology.Quasicategory.KanEdgeDetector

/-!
# One actual Kan marking cell detects all equivalence markings

The existing horn factorization of the interval supplies one fixed Kan
source in the original value universe. Every native equivalence edge
extends from the original interval into that source. Hence its one marking
cell has exactly the same right lifting condition as the large family of
all Kan-source marking cells, when the original total space is a
quasicategory. No model existence or source presentability is inferred
from this reduction alone.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The one marking cell on the actual Kan interval replacement. -/
def equivalenceMarkCell : min KanEdgeDetector.object.{u} ⟶ max KanEdgeDetector.object.{u} :=
  kanMarkCell KanEdgeDetector.object.{u}

/-- This one cell keeps the entire original native Kan interval replacement. -/
@[simp]
theorem equivalenceMarkCell_hom : equivalenceMarkCell.{u}.hom = 𝟙 KanEdgeDetector.object.{u} := rfl

/-- The reduced equivalence detector is a genuine marked monomorphism. -/
theorem equivalenceMarkCell_mono : Mono equivalenceMarkCell.{u} := kanMarkCell_mono _

/-- The one native detector lifts exactly when every original equivalence edge is marked. -/
theorem equivalenceMarkCell_rlp_iff {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B)
    [Quasicategory Y.toSSet] :
    HasLiftingProperty equivalenceMarkCell.{u} p ↔
      ∀ (e : Y.toSSet _⦋1⦌), (Edge.mk' e).IsEquivalence → e ∈ Y.marking := by
  constructor
  · intro h e he
    obtain ⟨g, hg⟩ := (KanEdgeDetector.isEquivalence_iff_extension e).mp he
    have hmark := (kanMarkCell_rlp_iff KanEdgeDetector.object.{u} p).mp h g
      (yonedaEquiv KanEdgeDetector.edge.{u})
    have hvalue : g.app (op ⦋1⦌) (yonedaEquiv KanEdgeDetector.edge.{u}) = e := by
      rw [← yonedaEquiv_comp, hg, Equiv.apply_symm_apply]
    exact hvalue ▸ hmark
  · intro hm
    exact kanMarkCell_of_equivalences_marked p hm _

/-- The single native marking cell replaces the large Kan-source family without changing its right class. -/
theorem equivalenceMarkCell_rlp_iff_kanMarkCells {Y : Marked.{u}} {B : SSet.{u}}
    (p : Y ⟶ max B) [Quasicategory Y.toSSet] :
    HasLiftingProperty equivalenceMarkCell.{u} p ↔
      ∀ (K : SSet.{u}) [KanComplex K], HasLiftingProperty (kanMarkCell K) p :=
  (equivalenceMarkCell_rlp_iff p).trans (kanMarkCells_rlp_iff_equivalences_marked p).symm

end SSet.Marked
