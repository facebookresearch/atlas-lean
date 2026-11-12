/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexAgreementCapEndpoint
import Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch
















namespace StatMech.FrontierD

noncomputable section

local instance sixVertexDisjointCapPhysicalRepairPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p


def SixVertexDirectedSimpleArc.mask
    {T : EvenTorus} (arc : SixVertexDirectedSimpleArc T) :
    SixVertexArrows T where
  horizontal base := decide
    (exists i, (arc.edge i).physical = (false, base))
  vertical base := decide
    (exists i, (arc.edge i).physical = (true, base))




structure SixVertexFollowedAgreementCapCertificate
    {T : EvenTorus} (omega eta : SixVertexArrows T) where
  arc : SixVertexDirectedSimpleArc T
  cap : SixVertexDirectedSimpleArc T
  cycle : SixVertexDirectedSimpleCycle T
  arc_follows : arc.Follows omega
  arc_disagrees : forall i, Not ((arc.edge i).IsAgreement omega eta)
  cap_follows : cap.Follows omega
  cap_agrees : cap.IsAgreement omega eta
  cap_start : cap.start = arc.finish
  cap_finish : cap.finish = arc.start
  tail_disjoint : forall i j, (arc.edge i).tail != (cap.edge j).tail
  physical_disjoint : forall i j,
    (arc.edge i).physical != (cap.edge j).physical
  cycle_mask : cycle.mask = sixVertexTorusMaskXor arc.mask cap.mask
  cycle_follows : cycle.Follows omega



structure SixVertexDisjointCapUnitRepair
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat) where
  first : SixVertexFollowedAgreementCapCertificate omega eta
  second : SixVertexFollowedAgreementCapCertificate eta omega
  cycle_tail_disjoint : forall i j,
    (first.cycle.edge i).tail != (second.cycle.edge j).tail
  first_seam_flow :
    (∑ column : Fin T.width,
      first.cycle.verticalFlow (column, svFinLast T.height_pos)) = -1
  second_seam_flow :
    (∑ column : Fin T.width,
      second.cycle.verticalFlow (column, svFinLast T.height_pos)) = 1
  fine : sixVertexHorizontalPairBoundedFineRowProfile
      (omega.horizontal, eta.horizontal) =
    sixVertexHorizontalPairBoundedFineRowProfile
      ((sixVertexTorusFlip first.cycle.mask omega).horizontal,
        (sixVertexTorusFlip second.cycle.mask eta).horizontal)
  loopGrade_eq : loopGrade
      (sixVertexTorusFlip first.cycle.mask omega,
        sixVertexTorusFlip second.cycle.mask eta) = loopGrade (omega, eta)


def SixVertexDisjointCapUnitRepair.target
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    SixVertexArrows T × SixVertexArrows T :=
  (sixVertexTorusFlip repair.first.cycle.mask omega,
    sixVertexTorusFlip repair.second.cycle.mask eta)

namespace SixVertexDisjointCapUnitRepair


theorem target_ice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade)
    (homega : omega.IceRule) (heta : eta.IceRule) :
    repair.target.1.IceRule ∧ repair.target.2.IceRule := by
  exact ⟨repair.first.cycle.flip_ice omega homega
      repair.first.cycle_follows,
    repair.second.cycle.flip_ice eta heta
      repair.second.cycle_follows⟩


theorem first_upCount
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    (sixVertexUpCount
        (svTorusVerticalRows T repair.target.1
          (svFinLast T.height_pos)) : Int) =
    (sixVertexUpCount
        (svTorusVerticalRows T omega
          (svFinLast T.height_pos)) : Int) + 1 := by
  change
    (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusFlip repair.first.cycle.mask omega)
          (svFinLast T.height_pos)) : Int) = _
  rw [sixVertexTorusFlip_upCount,
    repair.first.cycle.flip_seamDelta omega
      repair.first.cycle_follows,
    repair.first_seam_flow]
  norm_num


theorem second_upCount
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    (sixVertexUpCount
        (svTorusVerticalRows T repair.target.2
          (svFinLast T.height_pos)) : Int) =
    (sixVertexUpCount
        (svTorusVerticalRows T eta
          (svFinLast T.height_pos)) : Int) - 1 := by
  change
    (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusFlip repair.second.cycle.mask eta)
          (svFinLast T.height_pos)) : Int) = _
  rw [sixVertexTorusFlip_upCount,
    repair.second.cycle.flip_seamDelta eta
      repair.second.cycle_follows,
    repair.second_seam_flow]
  ring



theorem target_twoCycleFine
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    sixVertexPairAtMostTwoCycleFineRelated (omega, eta) repair.target := by
  refine ⟨sixVertexDirectedSimpleCycles_flip_pair_related
      repair.first.cycle repair.second.cycle omega eta
      repair.first.cycle_follows repair.second.cycle_follows
      repair.cycle_tail_disjoint, repair.fine⟩

end SixVertexDisjointCapUnitRepair


def sixVertexPhysicalArrowPairGrade
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T) :
    Nat × Nat :=
  (sixVertexTorusCTypeCount pair.1 + sixVertexTorusCTypeCount pair.2, 0)



def sixVertexDisjointCapPhysicalTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (repair : SixVertexDisjointCapUnitRepair source.1.1 source.2.1
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

@[simp] theorem sixVertexDisjointCapPhysicalTarget_arrows
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (repair : SixVertexDisjointCapUnitRepair source.1.1 source.2.1
      sixVertexPhysicalArrowPairGrade) :
    ((sixVertexDisjointCapPhysicalTarget source repair).1.1,
        (sixVertexDisjointCapPhysicalTarget source repair).2.1) =
      repair.target := by
  rfl


structure SixVertexConfigurationDisjointCapPairedRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  repair : forall source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt,
    Bool → SixVertexDisjointCapUnitRepair source.1.1 source.2.1
      sixVertexPhysicalArrowPairGrade
  source_recoverable : forall first second branch,
    sixVertexDisjointCapPhysicalTarget first (repair first branch) =
      sixVertexDisjointCapPhysicalTarget second (repair second branch) →
    first = second
  branch_distinct : forall source,
    sixVertexDisjointCapPhysicalTarget source (repair source false) ≠
      sixVertexDisjointCapPhysicalTarget source (repair source true)



def SixVertexConfigurationDisjointCapPairedRepairs.toPhysicalPairedBranches
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationDisjointCapPairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt where
  branch choice :=
    { toFun := fun source =>
        sixVertexDisjointCapPhysicalTarget source
          (repairs.repair source choice)
      inj' := by
        intro first second heq
        exact repairs.source_recoverable first second choice heq }
  distinct := repairs.branch_distinct
  aggregateTotalC := by
    intro source
    have hfalse := (repairs.repair source false).loopGrade_eq
    have htrue := (repairs.repair source true).loopGrade_eq
    change 2 * (sixVertexTorusCTypeCount source.1.1 +
        sixVertexTorusCTypeCount source.2.1) ≤ _
    change
      2 * (sixVertexTorusCTypeCount source.1.1 +
          sixVertexTorusCTypeCount source.2.1) ≤
        (sixVertexTorusCTypeCount
            (repairs.repair source false).target.1 +
          sixVertexTorusCTypeCount
            (repairs.repair source false).target.2) +
        (sixVertexTorusCTypeCount
            (repairs.repair source true).target.1 +
          sixVertexTorusCTypeCount
            (repairs.repair source true).target.2)
    simp only [sixVertexPhysicalArrowPairGrade, Prod.mk.injEq,
      and_true] at hfalse htrue
    change
      2 * (sixVertexTorusCTypeCount source.1.1 +
          sixVertexTorusCTypeCount source.2.1) ≤
        (sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source false).first.cycle.mask source.1.1) +
          sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source false).second.cycle.mask source.2.1)) +
        (sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source true).first.cycle.mask source.1.1) +
          sixVertexTorusCTypeCount
            (sixVertexTorusFlip
              (repairs.repair source true).second.cycle.mask source.2.1))
    rw [hfalse, htrue]
    omega



def SixVertexPositiveEvenTraceDisjointCapPairedRepairs
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  forall M n : Nat, (hn0 : 0 < n) → (hnN : n < N) →
    Nonempty
      (SixVertexConfigurationDisjointCapPairedRepairs
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN)


def SixVertexCanonicalPositiveEvenTraceDisjointCapPairedRepairs : Prop :=
  forall r k : Nat,
    SixVertexPositiveEvenTraceDisjointCapPairedRepairs
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))


theorem canonicalPhysicalPairedBranches_of_disjointCapPairedRepairs
    (hrepairs :
      SixVertexCanonicalPositiveEvenTraceDisjointCapPairedRepairs) :
    SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches := by
  intro r k M n hn0 hnN
  obtain ⟨repairs⟩ := hrepairs r k M n hn0 hnN
  exact ⟨repairs.toPhysicalPairedBranches⟩



theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_disjointCapPairedRepairs
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
    (hrepairs :
      SixVertexCanonicalPositiveEvenTraceDisjointCapPairedRepairs) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  exact
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches
      hq hhard hcross
      (canonicalPhysicalPairedBranches_of_disjointCapPairedRepairs hrepairs)

end

end StatMech.FrontierD
