/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectBoundaryCountablePieces
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRootBaseChange
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceCountableInterval

/-!
# Genuine absolute compactness of the SAME original countable boundary pieces

The original compact root, every actual original cell end and the actual
countable predecessor diagram give absolute compactness of the SAME
original piece. This uses the existing full root-adjoined universal
property. The actual arbitrary-equivalence interval therefore lies in
the original small up-to-isomorphism class of ℵ₁-presentable objects.
-/

noncomputable section
universe u v
open CategoryTheory Limits SmallObject MonoidalCategory
open scoped Simplicial
attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryGoodTree
variable {O : Type u} {C D : FixedObjects O} (f : C ⟶ D)

/-- The SAME actual original bounded piece is absolutely presentable when its unchanged original root is presentable. -/
theorem piece_presentable [IsCardinalPresentable C rank.{u}] (B : Supports f) :
    IsCardinalPresentable (piece f B) rank.{u} := by
  let _ : PartialOrder (Cells f) := (data f).order
  exact CompactRootBaseChange.compactRootLower rank (data f).tree
    (data f).good.presentable_source (data f).good.presentable_target
    (data f).good.predecessor_lt (data f).lowerData B.1 B.2

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryGoodTree

namespace CategoryTheory.SimplicialEnrichment.OriginalEquivalenceCountableInterval
open FixedObjects OriginalWalkingArrowFreeSingleHomIso OriginalBoundaryGoodTree
variable {C : Type v} [EnrichedCategory SSet.{u} C] (a : walking.{u} → C)
variable (e : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
  a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)
variable (he : IsIso (ComponentCategory.arrowOf C e))

/-- The SAME original free-arrow root is genuinely finite and hence ℵ₁-presentable. -/
theorem free_presentable : IsCardinalPresentable free.{u} rank.{u} := by
  let _ : IsFinitelyPresentable.{u} (𝟙_ SSet.{u}) :=
    isCardinalPresentable_of_iso SSet.Δ0IsoUnit Cardinal.aleph0.{u}
  let _ : IsFinitelyPresentable.{u} free.{u} := FreeSingleHom.object_isFinitelyPresentable _ _ _
  exact isCardinalPresentable_of_le free Cardinal.aleph0_lt_aleph_one.le

/-- The SAME genuine original countable interval is absolutely ℵ₁-presentable, with its original root and cell labels
retained. -/
theorem presentable : IsCardinalPresentable (fixedObject a e he) rank.{u} := by
  let _ : IsCardinalPresentable free.{u} rank.{u} := free_presentable
  exact piece_presentable (OriginalEquivalenceLocalization.fromFree a e he) (support a e he)

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceCountableInterval
