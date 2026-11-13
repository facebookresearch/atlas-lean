/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDisjointCapPhysicalRepair












namespace StatMech.FrontierD

noncomputable section




structure SixVertexTwoLayerUnitCycleRepair
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat) where
  first : SixVertexDirectedSimpleCycle T
  second : SixVertexDirectedSimpleCycle T
  first_follows : first.Follows omega
  second_follows : second.Follows eta
  tail_disjoint : forall i j,
    (first.edge i).tail != (second.edge j).tail
  first_seam_flow :
    (∑ column : Fin T.width,
      first.verticalFlow (column, svFinLast T.height_pos)) = -1
  second_seam_flow :
    (∑ column : Fin T.width,
      second.verticalFlow (column, svFinLast T.height_pos)) = 1
  fine : sixVertexHorizontalPairBoundedFineRowProfile
      (omega.horizontal, eta.horizontal) =
    sixVertexHorizontalPairBoundedFineRowProfile
      ((sixVertexTorusFlip first.mask omega).horizontal,
        (sixVertexTorusFlip second.mask eta).horizontal)
  loopGrade_eq : loopGrade
      (sixVertexTorusFlip first.mask omega,
        sixVertexTorusFlip second.mask eta) = loopGrade (omega, eta)

def SixVertexTwoLayerUnitCycleRepair.target
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade) :
    SixVertexArrows T × SixVertexArrows T :=
  (sixVertexTorusFlip repair.first.mask omega,
    sixVertexTorusFlip repair.second.mask eta)

namespace SixVertexTwoLayerUnitCycleRepair

theorem target_ice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade)
    (homega : omega.IceRule) (heta : eta.IceRule) :
    repair.target.1.IceRule ∧ repair.target.2.IceRule :=
  ⟨repair.first.flip_ice omega homega repair.first_follows,
    repair.second.flip_ice eta heta repair.second_follows⟩

theorem first_upCount
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade) :
    (sixVertexUpCount
        (svTorusVerticalRows T repair.target.1
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T omega
          (svFinLast T.height_pos)) : Int) + 1 := by
  change
    (sixVertexUpCount
        (svTorusVerticalRows T (sixVertexTorusFlip repair.first.mask omega)
          (svFinLast T.height_pos)) : Int) = _
  rw [sixVertexTorusFlip_upCount,
    repair.first.flip_seamDelta omega repair.first_follows,
    repair.first_seam_flow]
  norm_num

theorem second_upCount
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade) :
    (sixVertexUpCount
        (svTorusVerticalRows T repair.target.2
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T eta
          (svFinLast T.height_pos)) : Int) - 1 := by
  change
    (sixVertexUpCount
        (svTorusVerticalRows T (sixVertexTorusFlip repair.second.mask eta)
          (svFinLast T.height_pos)) : Int) = _
  rw [sixVertexTorusFlip_upCount,
    repair.second.flip_seamDelta eta repair.second_follows,
    repair.second_seam_flow]
  ring

theorem target_twoCycleFine
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade) :
    sixVertexPairAtMostTwoCycleFineRelated (omega, eta) repair.target :=
  ⟨sixVertexDirectedSimpleCycles_flip_pair_related
      repair.first repair.second omega eta repair.first_follows
      repair.second_follows repair.tail_disjoint,
    repair.fine⟩

end SixVertexTwoLayerUnitCycleRepair



def SixVertexDisjointCapUnitRepair.toUnitCycleRepair
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    SixVertexTwoLayerUnitCycleRepair omega eta loopGrade where
  first := repair.first.cycle
  second := repair.second.cycle
  first_follows := repair.first.cycle_follows
  second_follows := repair.second.cycle_follows
  tail_disjoint := repair.cycle_tail_disjoint
  first_seam_flow := repair.first_seam_flow
  second_seam_flow := repair.second_seam_flow
  fine := repair.fine
  loopGrade_eq := repair.loopGrade_eq

@[simp] theorem SixVertexDisjointCapUnitRepair.toUnitCycleRepair_target
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    repair.toUnitCycleRepair.target = repair.target := rfl


def sixVertexUnitCyclePhysicalTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (repair : SixVertexTwoLayerUnitCycleRepair source.1.1 source.2.1
      sixVertexPhysicalArrowPairGrade) :
    SixVertexConfigurationPhysicalTarget T middle := by
  have hice := repair.target_ice source.1.2.1 source.2.2.1
  have hfirstInt :
      (sixVertexUpCount
          (svTorusVerticalRows T repair.target.1
            (svFinLast T.height_pos)) : Int) = middle.val := by
    rw [repair.first_upCount, source.1.2.2]
    push_cast
    omega
  have hsecondInt :
      (sixVertexUpCount
          (svTorusVerticalRows T repair.target.2
            (svFinLast T.height_pos)) : Int) = middle.val := by
    rw [repair.second_upCount, source.2.2.2]
    push_cast
    omega
  exact (⟨repair.target.1, hice.1, by exact_mod_cast hfirstInt⟩,
    ⟨repair.target.2, hice.2, by exact_mod_cast hsecondInt⟩)

structure SixVertexConfigurationUnitCyclePairedRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  repair : forall source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt,
    Bool → SixVertexTwoLayerUnitCycleRepair source.1.1 source.2.1
      sixVertexPhysicalArrowPairGrade
  source_recoverable : forall first second branch,
    sixVertexUnitCyclePhysicalTarget first (repair first branch) =
      sixVertexUnitCyclePhysicalTarget second (repair second branch) →
    first = second
  branch_distinct : forall source,
    sixVertexUnitCyclePhysicalTarget source (repair source false) ≠
      sixVertexUnitCyclePhysicalTarget source (repair source true)

def SixVertexConfigurationUnitCyclePairedRepairs.toPhysicalPairedBranches
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationUnitCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt where
  branch choice :=
    { toFun := fun source =>
        sixVertexUnitCyclePhysicalTarget source (repairs.repair source choice)
      inj' := by
        intro first second heq
        exact repairs.source_recoverable first second choice heq }
  distinct := repairs.branch_distinct
  aggregateTotalC := by
    intro source
    have hfalse := (repairs.repair source false).loopGrade_eq
    have htrue := (repairs.repair source true).loopGrade_eq
    simp only [sixVertexPhysicalArrowPairGrade, Prod.mk.injEq,
      and_true] at hfalse htrue
    change
      2 * (sixVertexTorusCTypeCount source.1.1 +
          sixVertexTorusCTypeCount source.2.1) ≤
        (sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source false).first.mask source.1.1) +
          sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source false).second.mask source.2.1)) +
        (sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source true).first.mask source.1.1) +
          sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source true).second.mask source.2.1))
    rw [hfalse, htrue]
    omega

def SixVertexPositiveEvenTraceUnitCyclePairedRepairs
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  forall M n : Nat, (hn0 : 0 < n) → (hnN : n < N) →
    Nonempty
      (SixVertexConfigurationUnitCyclePairedRepairs
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN)

def SixVertexCanonicalPositiveEvenTraceUnitCyclePairedRepairs : Prop :=
  forall r k : Nat,
    SixVertexPositiveEvenTraceUnitCyclePairedRepairs
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))

theorem canonicalPhysicalPairedBranches_of_unitCyclePairedRepairs
    (hrepairs : SixVertexCanonicalPositiveEvenTraceUnitCyclePairedRepairs) :
    SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches := by
  intro r k M n hn0 hnN
  obtain ⟨repairs⟩ := hrepairs r k M n hn0 hnN
  exact ⟨repairs.toPhysicalPairedBranches⟩



theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_unitCyclePairedRepairs
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale → Even scale →
      12 * scale + 2 < 2 * (k + 3) →
      ∀ᶠ blocks in Filter.atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hrepairs : SixVertexCanonicalPositiveEvenTraceUnitCyclePairedRepairs) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) :=
  fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches
    hq hhard hcross
      (canonicalPhysicalPairedBranches_of_unitCyclePairedRepairs hrepairs)

end

end StatMech.FrontierD
