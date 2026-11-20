/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.PeriodicPlanarCoverageShells
import Code.FrontierD.FKQgt4SquareAnchoredShell
import Code.FrontierD.FKQgt4SquarePeriodicBridge
import Code.Walls.kc_latticeconnected

open Filter Finset Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.FK StatMech.FK.PeriodicPlanar StatMech.Lattice
open StatMech.Percolation StatMech.ConfigSpace

noncomputable section



def fkQgt4SquarePeriodicConnectionShellPairs (n : Nat) :
    Finset (square.BufferedVertex (2 * n) × square.BufferedVertex (2 * n)) :=
  (square.orbitShellCandidatePairs (2 * n)).filter
    (fun xy => n ≤ square.graph.dist xy.1.1 xy.2.1)

theorem mem_fkQgt4SquarePeriodicConnectionShellPairs_dist
    (n : Nat)
    (xy : square.BufferedVertex (2 * n) × square.BufferedVertex (2 * n))
    (hxy : xy ∈ fkQgt4SquarePeriodicConnectionShellPairs n) :
    n ≤ square.graph.dist xy.1.1 xy.2.1 := by
  exact (Finset.mem_filter.1 hxy).2


theorem fkQgt4SquarePeriodicConnectionShellPairs_card_le (n : Nat) :
    (fkQgt4SquarePeriodicConnectionShellPairs n).card ≤
      625 * (n + 1) ^ 4 := by
  have horbit :=
    PeriodicPlanarDualPair.PeriodicGraph.orbitBox_card_le_quadratic
      square (2 * n)
  have hlinear : 2 * (2 * n) + 1 ≤ 5 * (n + 1) := by omega
  calc
    (fkQgt4SquarePeriodicConnectionShellPairs n).card ≤
        (square.orbitShellCandidatePairs (2 * n)).card :=
      Finset.card_filter_le _ _
    _ ≤ (square.orbitBox (2 * n)).card ^ 2 :=
      square.orbitShellCandidatePairs_card_le (2 * n)
    _ ≤ (((2 * (2 * n) + 1) ^ 2 * square.fundamentalDomain.card) ^ 2) :=
      Nat.pow_le_pow_left horbit 2
    _ = (2 * (2 * n) + 1) ^ 4 := by
      simp [square]
      ring
    _ ≤ (5 * (n + 1)) ^ 4 := Nat.pow_le_pow_left hlinear 4
    _ = 625 * (n + 1) ^ 4 := by ring



theorem mem_fkQgt4AxisAnchoredSphereConnectionEvent_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat) :
    omega ∈ fkQgt4AxisAnchoredSphereConnectionEvent n ↔
      ∃ z : Site 2, StatMech.Lattice.Connected 2 omega (axisSite n) z ∧
        l1dist 2 (axisSite n) z = n := by
  constructor
  · intro h
    change ConfigSpace.shift (axisToOriginShift n) omega ∈
      fkQgt4CriticalFreeSphereConnectionEvent n at h
    simp only [fkQgt4CriticalFreeSphereConnectionEvent,
      Set.mem_iUnion, Set.mem_setOf_eq] at h
    obtain ⟨x, hxSphere, hxconn⟩ := h
    let z : Site 2 := axisSite n + x
    have hgaxis : axisToOriginShift n • axisSite n = origin 2 := by
      change -axisSite n + axisSite n = origin 2
      rw [neg_add_cancel]
      funext i
      fin_cases i <;> rfl
    have hgz : axisToOriginShift n • z = x := by
      change -axisSite n + (axisSite n + x) = x
      abel
    have hconn : StatMech.Lattice.Connected 2 omega (axisSite n) z := by
      apply (connected_shift (axisToOriginShift n) omega (axisSite n) z).mp
      simpa [hgaxis, hgz] using hxconn
    have hradius : fkQgt4SiteRadius x = n :=
      (Finset.mem_filter.1 hxSphere).2
    have hdist : l1dist 2 (axisSite n) z = n := by
      simp only [l1dist, Fin.sum_univ_two, z, axisSite, Pi.add_apply,
        fkQgt4SiteRadius] at hradius ⊢
      norm_num at hradius ⊢
      simpa [Int.natAbs_neg] using hradius
    exact ⟨z, hconn, hdist⟩
  · rintro ⟨z, hconn, hdist⟩
    exact mem_fkQgt4AxisAnchoredSphereConnectionEvent_of_connected
      omega n hconn hdist



theorem mem_box_two_mul_of_l1dist_axis_le
    (n : Nat) {z : Site 2} (hz : l1dist 2 (axisSite n) z ≤ n) :
    z ∈ box 2 (2 * n) := by
  rw [mem_box]
  intro i
  have hcoord : (axisSite n i - z i).natAbs ≤ n := by
    apply le_trans _ hz
    exact Finset.single_le_sum
      (f := fun k => (axisSite n k - z k).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have htri : (z i).natAbs ≤
      (axisSite n i).natAbs + (axisSite n i - z i).natAbs := by
    have hrewrite : z i = axisSite n i - (axisSite n i - z i) := by ring
    calc
      (z i).natAbs =
          (axisSite n i - (axisSite n i - z i)).natAbs :=
        congrArg Int.natAbs hrewrite
      _ ≤ (axisSite n i).natAbs +
          (axisSite n i - z i).natAbs := Int.natAbs_sub_le _ _
  fin_cases i
  · simp [axisSite] at htri hcoord ⊢
    omega
  · simp [axisSite] at htri hcoord ⊢
    omega



theorem l1dist_le_square_graph_dist (x y : Site 2) :
    l1dist 2 x y ≤ square.graph.dist x y := by
  obtain ⟨w, hw⟩ :=
    StatMech.Walls.kc_lattice_connected.exists_walk_length_eq_dist x y
  exact (l1dist_le_walk_length 2 w).trans_eq hw

private theorem mem_square_buffered_two_mul_of_l1dist_axis_le
    (n : Nat) {z : Site 2} (hz : l1dist 2 (axisSite n) z ≤ n) :
    z ∈ square.orbitBox (square.bufferedRadius (2 * n)) := by
  apply square.orbitBox_mono (square.id_le_bufferedRadius (2 * n))
  exact (fkSquarePeriodic_mem_orbitBox_iff (2 * n) z).2
    (mem_box_two_mul_of_l1dist_axis_le n hz)



theorem fkQgt4AxisAnchoredSphereConnectionEvent_subset_periodicShell
    (n : Nat) :
    fkQgt4AxisAnchoredSphereConnectionEvent n ⊆
      square.bufferedPairShell (2 * n)
        (fkQgt4SquarePeriodicConnectionShellPairs n) := by
  intro omega _homega
  rcases n with _ | n
  · let a0 : square.OrbitVertex 0 :=
      ⟨origin 2, (fkSquarePeriodic_mem_orbitBox_iff 0 (origin 2)).2 (by
        intro i
        fin_cases i <;> rfl)⟩
    let a : square.BufferedVertex 0 := square.orbitVertexToBuffered 0 a0
    have hcand : (a, a) ∈ square.orbitShellCandidatePairs 0 := by
      unfold PeriodicGraph.orbitShellCandidatePairs
      apply Finset.mem_image.2
      exact ⟨(a0, a0), by simp, rfl⟩
    have hpairs : (a, a) ∈ fkQgt4SquarePeriodicConnectionShellPairs 0 := by
      exact Finset.mem_filter.2 ⟨hcand, Nat.zero_le _⟩
    apply Set.mem_iUnion.2
    refine ⟨(a, a), Set.mem_iUnion.2 ⟨hpairs, ?_⟩⟩
    change (FK.openSub (square.bufferedGraph 0)
      (square.bufferedRestrict 0 omega)).Reachable a a
    exact .refl _
  · let radius := n + 1
    obtain ⟨z, hconn, hdist⟩ :=
      (mem_fkQgt4AxisAnchoredSphereConnectionEvent_iff omega radius).1 _homega
    change (square.openSubgraph omega).Reachable (axisSite radius) z at hconn
    let S : Set (Site 2) :=
      {v | l1dist 2 (axisSite radius) v < radius}
    have hcenter : axisSite radius ∈ S := by
      simp [S, radius]
    have hzout : z ∉ S := by
      intro hz
      change l1dist 2 (axisSite radius) z < radius at hz
      omega
    obtain ⟨y, hyreach, w, hyw, hw⟩ :=
      reachable_induce_innerBoundary
        (square.openSubgraph omega) S hcenter hzout hconn
    have hwdist : l1dist 2 (axisSite radius) w = radius := by
      have hylt : l1dist 2 (axisSite radius) y.1 < radius := y.2
      have hstep : l1dist 2 (axisSite radius) w ≤
          l1dist 2 (axisSite radius) y.1 + 1 := by
        calc
          l1dist 2 (axisSite radius) w ≤
              l1dist 2 (axisSite radius) y.1 + l1dist 2 y.1 w :=
            l1dist_triangle 2 (axisSite radius) y.1 w
          _ = l1dist 2 (axisSite radius) y.1 + 1 := by
            rw [l1dist_of_adj 2 hyw.1]
      have hwge : radius ≤ l1dist 2 (axisSite radius) w :=
        Nat.le_of_not_gt hw
      exact Nat.le_antisymm (by omega) hwge
    have hcenterBuffer : axisSite radius ∈
        square.orbitBox (square.bufferedRadius (2 * radius)) :=
      mem_square_buffered_two_mul_of_l1dist_axis_le radius (by simp)
    have hwBuffer : w ∈
        square.orbitBox (square.bufferedRadius (2 * radius)) :=
      mem_square_buffered_two_mul_of_l1dist_axis_le radius hwdist.le
    let a : square.BufferedVertex (2 * radius) :=
      ⟨axisSite radius, hcenterBuffer⟩
    let b : square.BufferedVertex (2 * radius) := ⟨w, hwBuffer⟩
    let incl : (square.openSubgraph omega).induce S →g
        (square.openSubgraph omega).induce
          (square.orbitBox (square.bufferedRadius (2 * radius)) : Set (Site 2)) :=
      { toFun := fun v =>
          ⟨v.1, mem_square_buffered_two_mul_of_l1dist_axis_le radius
            (Nat.le_of_lt v.2)⟩
        map_rel' := fun {_ _} h => h }
    have hyreachBuffer := hyreach.map incl
    have hywBuffer :
        ((square.openSubgraph omega).induce
          (square.orbitBox (square.bufferedRadius (2 * radius)) : Set (Site 2))).Adj
            (incl y) b := by
      exact hyw
    have hreachInduced :
        ((square.openSubgraph omega).induce
          (square.orbitBox (square.bufferedRadius (2 * radius)) : Set (Site 2))).Reachable
            a b := by
      simpa [a, incl] using hyreachBuffer.trans hywBuffer.reachable
    have hreachBuffered :
        (FK.openSub (square.bufferedGraph (2 * radius))
          (square.bufferedRestrict (2 * radius) omega)).Reachable a b :=
      (square.bufferedReachable_iff_inducedReachable
        (2 * radius) omega a b).2 hreachInduced
    have hcenterBox : axisSite radius ∈ square.orbitBox (2 * radius) :=
      (fkSquarePeriodic_mem_orbitBox_iff (2 * radius) _).2
        (mem_box_two_mul_of_l1dist_axis_le radius (by simp))
    have hwBox : w ∈ square.orbitBox (2 * radius) :=
      (fkSquarePeriodic_mem_orbitBox_iff (2 * radius) _).2
        (mem_box_two_mul_of_l1dist_axis_le radius hwdist.le)
    let a0 : square.OrbitVertex (2 * radius) := ⟨axisSite radius, hcenterBox⟩
    let b0 : square.OrbitVertex (2 * radius) := ⟨w, hwBox⟩
    have ha0 : square.orbitVertexToBuffered (2 * radius) a0 = a :=
      Subtype.ext rfl
    have hb0 : square.orbitVertexToBuffered (2 * radius) b0 = b :=
      Subtype.ext rfl
    have hcand : (a, b) ∈ square.orbitShellCandidatePairs (2 * radius) := by
      unfold PeriodicGraph.orbitShellCandidatePairs
      apply Finset.mem_image.2
      refine ⟨(a0, b0), by simp, ?_⟩
      exact Prod.ext ha0 hb0
    have hsep : radius ≤ square.graph.dist a.1 b.1 := by
      calc
        radius = l1dist 2 (axisSite radius) w := hwdist.symm
        _ ≤ square.graph.dist (axisSite radius) w :=
          l1dist_le_square_graph_dist _ _
    have hpairs : (a, b) ∈
        fkQgt4SquarePeriodicConnectionShellPairs radius :=
      Finset.mem_filter.2 ⟨hcand, hsep⟩
    apply Set.mem_iUnion.2
    refine ⟨(a, b), Set.mem_iUnion.2 ⟨hpairs, ?_⟩⟩
    change (FK.openSub (square.bufferedGraph (2 * radius))
      (square.bufferedRestrict (2 * radius) omega)).Reachable a b
    exact hreachBuffered




theorem inverseDualHasInfiniteClusterEvent_compl_subset_periodicShell_limsup :
    inverseDualHasInfiniteClusterEventᶜ ⊆
      limsup (fun n => square.bufferedPairShell (2 * n)
        (fkQgt4SquarePeriodicConnectionShellPairs n)) atTop := by
  intro omega homega
  have haxis :=
    inverseDualHasInfiniteClusterEvent_compl_subset_axis_limsup homega
  rw [mem_limsup_iff_frequently_mem] at haxis ⊢
  exact haxis.mono fun n hn =>
    fkQgt4AxisAnchoredSphereConnectionEvent_subset_periodicShell n hn




theorem inverseDualHasInfiniteClusterEvent_eq_square_preimage :
    inverseDualHasInfiniteClusterEvent =
      inverseFaceDualConfig ⁻¹' {eta | square.HasInfiniteCluster eta} := by
  ext omega
  simp only [inverseDualHasInfiniteClusterEvent, hasInfiniteClusterEvent,
    Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq,
    PeriodicGraph.HasInfiniteCluster, PeriodicGraph.cluster]
  rfl



theorem inverseFaceDual_square_planar_limsup :
    (inverseFaceDualConfig ⁻¹' {eta | square.HasInfiniteCluster eta})ᶜ ⊆
      limsup (fun n => square.bufferedPairShell (2 * n)
        (fkQgt4SquarePeriodicConnectionShellPairs n)) atTop := by
  rw [← inverseDualHasInfiniteClusterEvent_eq_square_preimage]
  exact inverseDualHasInfiniteClusterEvent_compl_subset_periodicShell_limsup

end

end StatMech.FrontierD
