/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareDualOpenBoundary
import Code.FrontierD.FKQgt4SquareAnchoredShell
import Code.FrontierA.NearestSetGeometry

open Filter MeasureTheory Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace
open StatMech.Universality StatMech.FK.PeriodicPlanar
open StatMech.FrontierA

noncomputable section



def faceDualAxisAnchor (j : Nat) : Site 2 :=
  square.shift ![1, 1] (axisSite j)


def faceDualAxisToOriginShift (j : Nat) : Multiplicative (Site 2) :=
  Multiplicative.ofAdd (-faceDualAxisAnchor j)



def fkQgt4FaceDualAnchoredSphereConnectionEvent (j : Nat) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  (ConfigSpace.shift (faceDualAxisToOriginShift j)) ⁻¹'
    fkQgt4CriticalFreeSphereConnectionEvent j

theorem fkQgt4FaceDualAnchoredSphereConnectionEvent_measure_eq
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu) (j : Nat) :
    mu (fkQgt4FaceDualAnchoredSphereConnectionEvent j) =
      mu (fkQgt4CriticalFreeSphereConnectionEvent j) := by
  exact htrans.measure_preimage (faceDualAxisToOriginShift j)
    (measurableSet_fkQgt4CriticalFreeSphereConnectionEvent j)

private theorem fkQgt4SiteRadius_sub_site
    (a z : Site 2) :
    fkQgt4SiteRadius (z - a) = l1dist 2 a z := by
  simp only [fkQgt4SiteRadius, l1dist, Fin.sum_univ_two, Pi.sub_apply]
  congr 1 <;>
    rw [show z _ - a _ = -(a _ - z _) by ring, Int.natAbs_neg]

theorem mem_fkQgt4FaceDualAnchoredSphereConnectionEvent_of_connected
    (omega : ConfigSpace (Sym2 (Site 2))) (j : Nat) {z : Site 2}
    (hconn : Connected 2 omega (faceDualAxisAnchor j) z)
    (hdist : l1dist 2 (faceDualAxisAnchor j) z = j) :
    omega ∈ fkQgt4FaceDualAnchoredSphereConnectionEvent j := by
  let g := faceDualAxisToOriginShift j
  have hga : g • faceDualAxisAnchor j = origin 2 := by
    change -faceDualAxisAnchor j + faceDualAxisAnchor j = origin 2
    rw [neg_add_cancel]
    funext i
    fin_cases i <;> rfl
  have hgz : g • z = z - faceDualAxisAnchor j := by
    change -faceDualAxisAnchor j + z = z - faceDualAxisAnchor j
    abel
  have hzSphere : g • z ∈ fkQgt4SiteSphere j := by
    rw [hgz]
    simp only [fkQgt4SiteSphere, Set.Finite.mem_toFinset,
      Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · intro i
      calc
        ((z - faceDualAxisAnchor j) i).natAbs ≤
            fkQgt4SiteRadius (z - faceDualAxisAnchor j) := by
          unfold fkQgt4SiteRadius
          fin_cases i
          · exact Nat.le_add_right _ _
          · exact Nat.le_add_left _ _
        _ = j := by rw [fkQgt4SiteRadius_sub_site, hdist]
    · rw [fkQgt4SiteRadius_sub_site, hdist]
  change ConfigSpace.shift g omega ∈
    fkQgt4CriticalFreeSphereConnectionEvent j
  unfold fkQgt4CriticalFreeSphereConnectionEvent
  rw [Set.mem_iUnion]
  refine ⟨g • z, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hzSphere, ?_⟩
  change Connected 2 (ConfigSpace.shift g omega) (origin 2) (g • z)
  rw [← hga]
  exact (connected_shift g omega (faceDualAxisAnchor j) z).2 hconn

private theorem squareDualClusterCoverage_boundaryHom_apply
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite)
    (x : Site 2) :
    squareDualClusterCoverage_boundaryHom omega n hfinite x =
      square.shift ![1, 1] x := by
  rfl

private theorem squareDualClusterCoverage_boundaryHom_l1dist
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite)
    (x y : Site 2) :
    l1dist 2 (squareDualClusterCoverage_boundaryHom omega n hfinite x)
        (squareDualClusterCoverage_boundaryHom omega n hfinite y) =
      l1dist 2 x y := by
  rw [squareDualClusterCoverage_boundaryHom_apply,
    squareDualClusterCoverage_boundaryHom_apply]
  change l1dist 2 (x + ![1, 1]) (y + ![1, 1]) = l1dist 2 x y
  rw [add_comm x, add_comm y, l1dist_translate]



theorem exists_faceDualAnchoredSphereConnection_of_clusters_finite
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite) :
    ∃ j ≥ n, omega ∈ fkQgt4FaceDualAnchoredSphereConnectionEvent j := by
  let S := squareDualClusterCoverage omega n
  let hS : S.Finite := squareDualClusterCoverage_finite omega n hfinite
  let K := squareHoleFill S hS
  let hK : K.Finite := squareHoleFill_finite S hS
  have hzeroBox : origin 2 ∈ box 2 n := by
    intro i
    fin_cases i <;> simp [origin]
  have hzeroS : origin 2 ∈ S :=
    box_subset_squareDualClusterCoverage omega n hzeroBox
  have hzeroK : origin 2 ∈ K := subset_squareHoleFill S hS hzeroS
  have hKconn : ∀ a b : K,
      ((hypercubicLattice 2).induce K).Reachable a b := by
    simpa [S, hS, K] using
      squareDualClusterCoverage_fill_connected omega n hfinite
  let rho := squareRegionConfig K
  have hrhoCluster : cluster 2 rho (origin 2) = K :=
    squareRegionConfig_cluster_eq K hzeroK hKconn
  have hrhoFinite : (cluster 2 rho (origin 2)).Finite := by
    rw [hrhoCluster]
    exact hK
  let j := exitIndex (ω := rho) hrhoFinite
  have hjge : n ≤ j := by
    by_contra hnot
    have hjlt : j < n := Nat.lt_of_not_ge hnot
    have haxisBox : axisSite (j + 1) ∈ box 2 n := by
      intro i
      fin_cases i <;> simp [axisSite] <;> omega
    have haxisS : axisSite (j + 1) ∈ S :=
      box_subset_squareDualClusterCoverage omega n haxisBox
    have haxisK : axisSite (j + 1) ∈ K :=
      subset_squareHoleFill S hS haxisS
    have hout := axisSite_exit_succ_not_mem (ω := rho) hrhoFinite
    rw [hrhoCluster] at hout
    exact hout haxisK
  have hface : FaceBoundaryConnected K (phb_boundarySupport K hK) := by
    simpa [S, hS, K, hK] using
      squareDualClusterCoverage_faceBoundaryConnected omega n hfinite
  have hright : (faceBoundaryGraph K).Adj
      (exitFaceUp (ω := rho) hrhoFinite)
      (exitFaceDown (ω := rho) hrhoFinite) := by
    have h := exitFaces_faceBoundaryGraph_adj (ω := rho) hrhoFinite
    rwa [hrhoCluster] at h
  have hleft : (faceBoundaryGraph K).Adj
      (leftExitFaceUp (ω := rho) hrhoFinite)
      (leftExitFaceDown (ω := rho) hrhoFinite) := by
    have h := leftExitFaces_faceBoundaryGraph_adj (ω := rho) hrhoFinite
    rwa [hrhoCluster] at h
  have hrT : exitFaceUp (ω := rho) hrhoFinite ∈
      (phb_boundarySupport K hK : Set (Site 2)) := by
    simpa using hright.mem_support_left
  have hlT : leftExitFaceUp (ω := rho) hrhoFinite ∈
      (phb_boundarySupport K hK : Set (Site 2)) := by
    simpa using hleft.mem_support_left
  rw [FaceBoundaryConnected] at hface
  obtain ⟨w⟩ := hface.preconnected
    ⟨exitFaceUp (ω := rho) hrhoFinite, hrT⟩
    ⟨leftExitFaceUp (ω := rho) hrhoFinite, hlT⟩
  let incl : (faceBoundaryGraph K).induce
      (phb_boundarySupport K hK : Set (Site 2)) →g faceBoundaryGraph K :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab => hab }
  let wb := w.map incl
  let boundaryHom := squareDualClusterCoverage_boundaryHom omega n hfinite
  let wo := wb.map boundaryHom
  let wl := wo.map (Hom.ofLE (openSubgraph_le omega))
  have hfar0 : j ≤ l1dist 2
      (exitFaceUp (ω := rho) hrhoFinite)
      (leftExitFaceUp (ω := rho) hrhoFinite) :=
    exitIndex_le_l1dist_of_leftFace (ω := rho) hrhoFinite
      (leftExitFaceUp_coord0_nonpos (ω := rho) hrhoFinite)
  have hfar : j ≤ l1dist 2
      (boundaryHom (exitFaceUp (ω := rho) hrhoFinite))
      (boundaryHom (leftExitFaceUp (ω := rho) hrhoFinite)) := by
    rw [squareDualClusterCoverage_boundaryHom_l1dist]
    exact hfar0
  have hwlStart : l1dist 2
      (boundaryHom (exitFaceUp (ω := rho) hrhoFinite))
      (boundaryHom (exitFaceUp (ω := rho) hrhoFinite)) ≤ j := by simp
  obtain ⟨z, hz, hdist⟩ := latticeWalk_hits_l1Sphere
    (boundaryHom (exitFaceUp (ω := rho) hrhoFinite)) wl j hwlStart hfar
  have hzOpen : z ∈ wo.support := by
    change z ∈ (wo.map (Hom.ofLE (openSubgraph_le omega))).support at hz
    rw [Walk.support_map] at hz
    simpa using hz
  have hconn : Connected 2 omega
      (boundaryHom (exitFaceUp (ω := rho) hrhoFinite)) z :=
    ⟨wo.takeUntil z hzOpen⟩
  have hexit : exitFaceUp (ω := rho) hrhoFinite = axisSite j := by
    funext i
    fin_cases i <;> rfl
  have hanchor :
      boundaryHom (exitFaceUp (ω := rho) hrhoFinite) =
        faceDualAxisAnchor j := by
    rw [squareDualClusterCoverage_boundaryHom_apply, hexit]
    rfl
  refine ⟨j, hjge, ?_⟩
  apply mem_fkQgt4FaceDualAnchoredSphereConnectionEvent_of_connected omega j
  · simpa [hanchor] using hconn
  · simpa [hanchor] using hdist

theorem faceDual_allFinite_subset_anchored_limsup :
    {omega : ConfigSpace (Sym2 (Site 2)) |
      ∀ x : Site 2, (cluster 2 (fci_faceDualConfig omega) x).Finite} ⊆
      limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop := by
  intro omega hfinite
  rw [mem_limsup_iff_frequently_mem, frequently_atTop]
  intro n
  exact exists_faceDualAnchoredSphereConnection_of_clusters_finite
    omega n hfinite



theorem fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_ratePos
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
        (limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop) = 0 := by
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
    simpa [mu, hp, hp1, hq0] using
      (FK.fkgqt_freeIV_isTranslationInvariant (d := 2) hp hp1 hq1)
  have hsum : (∑' j : Nat,
      mu (fkQgt4FaceDualAnchoredSphereConnectionEvent j)) ≠ ⊤ := by
    simp_rw [fkQgt4FaceDualAnchoredSphereConnectionEvent_measure_eq mu htrans]
    simpa [mu, hp, hp1, hq0] using
      fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_ratePos hq hpos
  change mu (limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop) = 0
  exact measure_limsup_atTop_eq_zero hsum



theorem fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_ratePos
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    let mu := ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
    mu {omega | ∃ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Infinite} = 1 := by
  dsimp only
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q)
  let A : Set (ConfigSpace (Sym2 (Site 2))) :=
    {omega | ∃ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Infinite}
  have hAeq : A = fci_faceDualConfig ⁻¹'
      hasInfiniteClusterEvent 2 := by
    ext omega
    simp only [A, Set.mem_setOf_eq, Set.mem_preimage]
    simp [hasInfiniteClusterEvent, FK.clusterInfiniteEvent]
  have hAmeas : MeasurableSet A := by
    rw [hAeq]
    exact (measurableSet_hasInfiniteClusterEvent 2).preimage
      fci_faceDualConfig_measurePreserving.measurable
  have hcomplSubset : Aᶜ ⊆
      limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop := by
    intro omega hnot
    apply faceDual_allFinite_subset_anchored_limsup
    intro x
    by_contra hinfinite
    exact hnot ⟨x, hinfinite⟩
  have hlimzero : mu
      (limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop) = 0 := by
    simpa [mu] using
      fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_ratePos
        hq hpos
  have hcomplZero : mu Aᶜ = 0 :=
    measure_mono_null hcomplSubset hlimzero
  change mu A = 1
  exact (prob_compl_eq_zero_iff hAmeas).mp hcomplZero

theorem fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_winding
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
        (limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop) = 0 := by
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
    simpa [mu, hp, hp1, hq0] using
      (FK.fkgqt_freeIV_isTranslationInvariant (d := 2) hp hp1 hq1)
  have hsum : (∑' j : Nat,
      mu (fkQgt4FaceDualAnchoredSphereConnectionEvent j)) ≠ ⊤ := by
    simp_rw [fkQgt4FaceDualAnchoredSphereConnectionEvent_measure_eq mu htrans]
    simpa [mu, hp, hp1, hq0] using
      fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_winding hq hwind
  change mu (limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop) = 0
  exact measure_limsup_atTop_eq_zero hsum



theorem fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_winding
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
      (cluster 2 (fci_faceDualConfig omega) x).Infinite} = 1 := by
  dsimp only
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q)
  let A : Set (ConfigSpace (Sym2 (Site 2))) :=
    {omega | ∃ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Infinite}
  have hAeq : A = fci_faceDualConfig ⁻¹'
      hasInfiniteClusterEvent 2 := by
    ext omega
    simp only [A, Set.mem_setOf_eq, Set.mem_preimage]
    simp [hasInfiniteClusterEvent, FK.clusterInfiniteEvent]
  have hAmeas : MeasurableSet A := by
    rw [hAeq]
    exact (measurableSet_hasInfiniteClusterEvent 2).preimage
      fci_faceDualConfig_measurePreserving.measurable
  have hcomplSubset : Aᶜ ⊆
      limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop := by
    intro omega hnot
    apply faceDual_allFinite_subset_anchored_limsup
    intro x
    by_contra hinfinite
    exact hnot ⟨x, hinfinite⟩
  have hlimzero : mu
      (limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop) = 0 := by
    simpa [mu] using
      fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_winding
        hq hwind
  have hcomplZero : mu Aᶜ = 0 :=
    measure_mono_null hcomplSubset hlimzero
  change mu A = 1
  exact (prob_compl_eq_zero_iff hAmeas).mp hcomplZero

end

end StatMech.FrontierD
