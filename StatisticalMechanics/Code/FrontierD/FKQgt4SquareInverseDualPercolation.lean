/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareAnchoredShell
import Code.FK.PeriodicPlanarCoverage

open Filter MeasureTheory Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.FK.PeriodicPlanar

noncomputable section



theorem inverseDual_allFinite_subset_axisAnchored_limsup :
    {omega : ConfigSpace (Sym2 (Site 2)) |
      ∀ x : Site 2, (cluster 2 (inverseFaceDualConfig omega) x).Finite} ⊆
      limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop := by
  intro omega hfinite
  rw [mem_limsup_iff_frequently_mem, frequently_atTop]
  intro n
  obtain ⟨j, hj, homega⟩ :=
    exists_axisAnchoredSphereConnection_of_inverseDual_clusters_finite
      omega n hfinite
  exact ⟨j, hj, homega⟩



theorem fkQgt4AxisAnchoredSphereConnectionEvent_tsum_ne_top_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    (∑' n : Nat,
      ((FK.freeInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2))))
          (fkQgt4AxisAnchoredSphereConnectionEvent n)) ≠ ⊤ := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) ≤ q := by linarith
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    simpa [mu] using
      (FK.fkgqt_freeIV_isTranslationInvariant (d := 2) hp hp1 hq1)
  have heq : ∀ n,
      mu (fkQgt4AxisAnchoredSphereConnectionEvent n) =
        mu (fkQgt4CriticalFreeSphereConnectionEvent n) :=
    fkQgt4AxisAnchoredSphereConnectionEvent_measure_eq mu htrans
  change (∑' n : Nat,
    mu (fkQgt4AxisAnchoredSphereConnectionEvent n)) ≠ ⊤
  rw [show (fun n : Nat =>
      mu (fkQgt4AxisAnchoredSphereConnectionEvent n)) =
      (fun n : Nat => mu (fkQgt4CriticalFreeSphereConnectionEvent n)) by
    funext n
    exact heq n]
  simpa [mu, hp, hp1, hq0] using
    fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_winding hq hwind



theorem fkQgt4AxisAnchoredSphereConnectionEvent_limsup_zero_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
        (limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop) = 0 := by
  apply measure_limsup_atTop_eq_zero
  exact fkQgt4AxisAnchoredSphereConnectionEvent_tsum_ne_top_of_winding hq hwind



theorem fkQgt4CriticalFree_inverseDual_hasInfiniteCluster_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    let mu := ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
    mu {omega | ∃ x : Site 2,
      (cluster 2 (inverseFaceDualConfig omega) x).Infinite} = 1 := by
  dsimp only
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q)
  let A : Set (ConfigSpace (Sym2 (Site 2))) :=
    {omega | ∃ x : Site 2,
      (cluster 2 (inverseFaceDualConfig omega) x).Infinite}
  have hAeq : A = inverseFaceDualConfig ⁻¹'
      {eta | square.HasInfiniteCluster eta} := by
    ext omega
    simp only [A, Set.mem_setOf_eq, Set.mem_preimage,
      PeriodicGraph.HasInfiniteCluster, PeriodicGraph.cluster,
      PeriodicGraph.openSubgraph]
    rfl
  have hAmeas : MeasurableSet A := by
    rw [hAeq]
    exact square.measurableSet_hasInfiniteCluster.preimage
      measurable_inverseFaceDualConfig
  have hcomplSubset : Aᶜ ⊆
      limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop := by
    intro omega hnot
    apply inverseDual_allFinite_subset_axisAnchored_limsup
    intro x
    by_contra hinfinite
    exact hnot ⟨x, hinfinite⟩
  have hlimzero : mu
      (limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop) = 0 := by
    simpa [mu] using
      fkQgt4AxisAnchoredSphereConnectionEvent_limsup_zero_of_winding hq hwind
  have hcomplZero : mu Aᶜ = 0 :=
    measure_mono_null hcomplSubset hlimzero
  change mu A = 1
  exact (prob_compl_eq_zero_iff hAmeas).mp hcomplZero

end

end StatMech.FrontierD
