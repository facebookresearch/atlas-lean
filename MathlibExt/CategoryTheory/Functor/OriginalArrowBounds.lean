/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Regular bounds on all original index arrows

The original object and Hom universes remain independent of the working
universe. Actual object smallness and local Hom smallness give one
uncountable regular bound above supplied ranks. Every conclusion concerns
the original object and arrow carriers. An essential model is not chosen.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w uD vD

namespace CategoryTheory.Functor.OriginalArrowBounds

variable {D : Type uD} [Category.{vD} D]

/-- Each original Hom carrier injects into the actual original Arrow carrier. -/
theorem homLt {chi : Cardinal.{w}} (hArrow : HasCardinalLT (Arrow D) chi) (d e : D) :
    HasCardinalLT (d ⟶ e) chi :=
  hArrow.of_injective (fun f : d ⟶ e => Arrow.mk f) (Arrow.mk_injective d e)

/-- Actual original smallness gives an uncountable regular bound above the supplied rank. -/
theorem existsRegularBoundAbove [Small.{w} D] [LocallySmall.{w} D]
    (rank : Cardinal.{w}) :
    ∃ chi : Cardinal.{w}, chi.IsRegular ∧ Cardinal.aleph0 < chi ∧
      rank ≤ chi ∧ HasCardinalLT (Arrow D) chi ∧ HasCardinalLT D chi ∧
      ∀ d e : D, HasCardinalLT (d ⟶ e) chi := by
  obtain ⟨k, _, hArrow⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Arrow D)
  let m : Cardinal.{w} := max k (max rank Cardinal.aleph0)
  let chi : Cardinal.{w} := Order.succ m
  have hAleph : Cardinal.aleph0 ≤ m :=
    (le_max_right rank Cardinal.aleph0).trans (le_max_right k (max rank Cardinal.aleph0))
  have hK : k ≤ chi := (le_max_left k (max rank Cardinal.aleph0)).trans (Order.le_succ m)
  have hRank : rank ≤ chi :=
    ((le_max_left rank Cardinal.aleph0).trans
      (le_max_right k (max rank Cardinal.aleph0))).trans (Order.le_succ m)
  have hArrowChi : HasCardinalLT (Arrow D) chi := hArrow.of_le hK
  exact ⟨chi, Cardinal.isRegular_succ hAleph, Order.lt_succ_of_le hAleph, hRank,
    hArrowChi, hasCardinalLT_of_hasCardinalLT_arrow hArrowChi, fun d e => homLt hArrowChi d e⟩

/-- Every member of the original finite rank family is bounded by the same actual rank. -/
theorem existsRegularBoundForFiniteRanks [Small.{w} D] [LocallySmall.{w} D]
    (ranks : Finset (Cardinal.{w})) :
    ∃ chi : Cardinal.{w}, chi.IsRegular ∧ Cardinal.aleph0 < chi ∧
      (∀ rank ∈ ranks, rank ≤ chi) ∧
      HasCardinalLT (Arrow D) chi ∧ HasCardinalLT D chi ∧
      ∀ d e : D, HasCardinalLT (d ⟶ e) chi := by
  obtain ⟨chi, hRegular, hUncountable, hRanks, hArrow, hObjects, hHoms⟩ :=
    existsRegularBoundAbove (D := D) (ranks.sup id)
  exact ⟨chi, hRegular, hUncountable, fun rank h => (Finset.le_sup (f := id) h).trans hRanks,
    hArrow, hObjects, hHoms⟩

end CategoryTheory.Functor.OriginalArrowBounds
