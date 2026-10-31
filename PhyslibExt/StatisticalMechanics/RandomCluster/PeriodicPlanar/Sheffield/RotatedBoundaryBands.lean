/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DualBoundaryBands

/-!
# Boundary-band families under the axis swap

Normal boundary-band families and paired aligned margin schedules are transported along the
exchange of the two axes, giving rotated mixed boundary scores.

## i. Overview

A `NormalBoundaryBandFamily` records, for each side of a rectangle, translated source sets
whose connection to that side is likely; exchanging the axes permutes the four sides
(left ↔ bottom, right ↔ top). A `PairedAlignedMarginSchedule` for a primal/dual pair of families
is transported the same way, with the vertical and horizontal schedules exchanged (and the new
vertical schedule shifted by one index). The existence theorem for paired mixed boundary scores
then applies to the swapped embeddings.

## ii. Key results

- `exists_pairedRotatedMixedBoundaryScores` : conditional on translation invariance of the
  primal and dual measures and on the given boundary-band families and margin schedule (all
  passed as data). The index `k` does not enter the conclusion.

## iii. Table of contents

- A. Axis swap of the unit shifts
- B. Transport of families and schedules
- C. Rotated mixed boundary scores

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

/-! ## A. Axis swap of the unit shifts -/

@[simp] lemma siteAxisSwap_horizontalShift (t : Int) :
    siteAxisSwap (horizontalShift t) = verticalShift t := by
  ext i
  fin_cases i <;> rfl

@[simp] lemma siteAxisSwap_verticalShift (t : Int) :
    siteAxisSwap (verticalShift t) = horizontalShift t := by
  ext i
  fin_cases i <;> rfl

/-! ## B. Transport of families and schedules -/

/-- A normal boundary-band family for `E`, viewed as a family for the swapped embedding: the left
and right bands become the bottom and top bands and conversely. -/
def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.axisSwap
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) :
    E.axisSwap.NormalBoundaryBandFamily mu S p where
  baseLeft := siteAxisSwap family.baseBottom
  baseRight := siteAxisSwap family.baseTop
  baseBottom := siteAxisSwap family.baseLeft
  baseTop := siteAxisSwap family.baseRight
  radiusLeft := family.radiusBottom
  radiusRight := family.radiusTop
  radiusBottom := family.radiusLeft
  radiusTop := family.radiusRight
  left := by
    intro margin i
    have h := family.bottom margin i
    constructor
    · rw [E.axisSwap_rectVertices]
      simpa [PeriodicGraph.axisSwap] using h.1
    · rw [E.axisSwap_leftBoundaryEvent]
      simpa [PeriodicGraph.axisSwap] using h.2
  right := by
    intro margin i
    have h := family.top margin i
    constructor
    · rw [E.axisSwap_rectVertices]
      simpa [PeriodicGraph.axisSwap] using h.1
    · rw [E.axisSwap_rightBoundaryEvent]
      simpa [PeriodicGraph.axisSwap] using h.2
  bottom := by
    intro margin i
    have h := family.left margin i
    constructor
    · rw [E.axisSwap_rectVertices]
      simpa [PeriodicGraph.axisSwap] using h.1
    · rw [E.axisSwap_bottomBoundaryEvent]
      simpa [PeriodicGraph.axisSwap] using h.2
  top := by
    intro margin i
    have h := family.right margin i
    constructor
    · rw [E.axisSwap_rectVertices]
      simpa [PeriodicGraph.axisSwap] using h.1
    · rw [E.axisSwap_topBoundaryEvent]
      simpa [PeriodicGraph.axisSwap] using h.2

/-- A paired aligned margin schedule, transported to the swapped embeddings: the horizontal and
vertical schedules are exchanged, the new vertical schedule shifted by one index. -/
def PairedAlignedMarginSchedule.axisSwap
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    {family : E.NormalBoundaryBandFamily mu S p}
    {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
    {verticalRequirement horizontalRequirement : Nat → Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement) :
    PairedAlignedMarginSchedule E.axisSwap Edual.axisSwap
      family.axisSwap familyDual.axisSwap
      horizontalRequirement verticalRequirement where
  horizontal := schedule.vertical
  vertical := fun n ↦ schedule.horizontal (n + 1)
  horizontal_tendsto := schedule.vertical_tendsto
  vertical_tendsto := by
    apply schedule.horizontal_tendsto.comp
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  vertical_requirement := schedule.horizontal_requirement
  horizontal_requirement := fun n ↦ schedule.vertical_requirement (n + 1)
  primal_left_bottom := schedule.primal_bottom_left
  primal_right_bottom := schedule.primal_top_left
  primal_left_top := schedule.primal_bottom_right
  primal_right_top := schedule.primal_top_right
  primal_bottom_left := fun n ↦ schedule.primal_left_bottom (n + 1)
  primal_top_left := fun n ↦ schedule.primal_right_bottom (n + 1)
  primal_bottom_right := fun n ↦ schedule.primal_left_top (n + 1)
  primal_top_right := fun n ↦ schedule.primal_right_top (n + 1)
  dual_left_bottom := schedule.dual_bottom_left
  dual_right_bottom := schedule.dual_top_left
  dual_left_top := schedule.dual_bottom_right
  dual_right_top := schedule.dual_top_right
  dual_bottom_left := fun n ↦ schedule.dual_left_bottom (n + 1)
  dual_top_left := fun n ↦ schedule.dual_right_bottom (n + 1)
  dual_bottom_right := fun n ↦ schedule.dual_left_top (n + 1)
  dual_top_right := fun n ↦ schedule.dual_right_top (n + 1)

/-! ## C. Rotated mixed boundary scores -/

/-- Paired mixed boundary scores exist for the swapped primal and dual embeddings, given
translation-invariant measures, boundary-band families and an aligned margin schedule. -/
theorem exists_pairedRotatedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat → Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    Nonempty (PairedMixedBoundaryScores E.axisSwap Edual.axisSwap mu muDual
      S Sdual p pDual) := by
  exact exists_pairedMixedBoundaryScores E.axisSwap Edual.axisSwap
    mu muDual (P.axisSwap_isTranslationInvariant mu hTI)
    (Pdual.axisSwap_isTranslationInvariant muDual hTIDual)
    family.axisSwap familyDual.axisSwap
    schedule.axisSwap k

end StatMech.FK.PeriodicPlanar
