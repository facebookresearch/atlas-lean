/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldDualBoundaryBands









open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

@[simp] theorem siteAxisSwap_horizontalShift (t : Int) :
    siteAxisSwap (horizontalShift t) = verticalShift t := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem siteAxisSwap_verticalShift (t : Int) :
    siteAxisSwap (verticalShift t) = horizontalShift t := by
  ext i
  fin_cases i <;> rfl




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
