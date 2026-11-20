/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FreeInfiniteParityTopology
import Code.FrontierB.FreeBoxCurrentParity
import Code.FK.WiredDomChain
import Code.FK.FreeTailTriviality

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

theorem openSubgraph_extendEdge_adj_endpoints_mem_box
    (n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {x y : Site d} (hxy : (openSubgraph d (extendEdge d n omega)).Adj x y) :
    x ∈ box d n ∧ y ∈ box d n := by
  rw [openSubgraph_adj] at hxy
  obtain ⟨_, hopen⟩ := hxy
  obtain ⟨e, he⟩ := range_of_extendEdge_true n omega s(x, y) hopen
  induction e using Sym2.inductionOn with
  | _ a b =>
    unfold edgeIncl at he
    rw [Sym2.map_mk] at he
    have hxmem : x ∈ s((a : Site d), (b : Site d)).toFinset := by
      rw [he, Sym2.toFinset_mk_eq]
      simp
    have hymem : y ∈ s((a : Site d), (b : Site d)).toFinset := by
      rw [he, Sym2.toFinset_mk_eq]
      simp
    rw [Sym2.toFinset_mk_eq] at hxmem hymem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem hymem
    constructor
    · rcases hxmem with rfl | rfl
      · exact a.2
      · exact b.2
    · rcases hymem with rfl | rfl
      · exact a.2
      · exact b.2

theorem openSub_extendEdge_reachable_iff
    (n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (x y : boxVerts d n) :
    (openSub (boxGraph d n) omega).Reachable x y ↔
      (openSubgraph d (extendEdge d n omega)).Reachable (x : Site d) (y : Site d) := by
  constructor
  · intro h
    have hbox : boxRestrict d n (extendEdge d n omega) = omega :=
      boxRestrict_extendEdge d n omega
    rw [← hbox] at h
    exact connected_of_boxConnected n (extendEdge d n omega) h
  · rintro ⟨w⟩
    have hsupp : ∀ z ∈ w.support, z ∈ box d n := by
      intro z hz
      by_cases hzx : z = x
      · simpa [hzx] using x.2
      · have hprefix := (w.takeUntil z hz).reverse
        cases hprefix with
        | nil => exact absurd rfl hzx
        | cons huv p =>
          exact (openSubgraph_extendEdge_adj_endpoints_mem_box n omega huv).1
    let wi := w.induce (box d n) hsupp
    have hmap : (openSub (boxGraph d n)
        (boxRestrict d n (extendEdge d n omega))).Reachable x y := by
      exact wi.reachable.map
        { toFun := id
          map_rel' := fun hab => boxGraph_open_of_openSubgraph n
            (extendEdge d n omega) hab }
    simpa only [boxRestrict_extendEdge] using hmap

theorem markReachableCount_boxSpinSupport_eq
    (n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (A : Finset (Site d)) (hA : (A : Set (Site d)) ⊆ box d n)
    (x : boxVerts d n) :
    markReachableCount (boxGraph d n) omega (boxSpinSupport d n A) x =
      markReachableCount (hypercubicLattice d) (extendEdge d n omega) A x := by
  classical
  letI : DecidableRel (openSub (boxGraph d n) omega).Reachable :=
    Classical.decRel _
  letI : DecidableRel
      (openSub (hypercubicLattice d) (extendEdge d n omega)).Reachable :=
    Classical.decRel _
  unfold markReachableCount
  apply Finset.card_bij (fun (y : boxVerts d n) _ => (y : Site d))
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨by simpa [boxSpinSupport] using hy.1,
      (openSub_extendEdge_reachable_iff n omega x y).1 hy.2⟩
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro y hy
    rw [Finset.mem_filter] at hy
    let z : boxVerts d n := ⟨y, hA hy.1⟩
    have hz : z ∈ (boxSpinSupport d n A).filter
        (fun z => (openSub (boxGraph d n) omega).Reachable x z) := by
      rw [Finset.mem_filter]
      exact ⟨by simp [boxSpinSupport, z, hy.1],
        (openSub_extendEdge_reachable_iff n omega x z).2 hy.2⟩
    exact ⟨z, hz, rfl⟩

theorem allClustersEven_box_iff_extendEdge
    (n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (A : Finset (Site d)) (hA : (A : Set (Site d)) ⊆ box d n) :
    AllClustersEven (boxGraph d n) omega (boxSpinSupport d n A) ↔
      AllClustersEven (hypercubicLattice d) (extendEdge d n omega) A := by
  rw [allClustersEven_iff_mark_reachability,
    allClustersEven_iff_mark_reachability]
  constructor
  · intro h x hx
    let z : boxVerts d n := ⟨x, hA hx⟩
    rw [← markReachableCount_boxSpinSupport_eq n omega A hA z]
    apply h z
    simp [boxSpinSupport, z, hx]
  · intro h x hx
    rw [markReachableCount_boxSpinSupport_eq n omega A hA x]
    exact h x (by simpa [boxSpinSupport] using hx)

theorem boxSpinSupport_card
    (n : Nat) (A : Finset (Site d)) (hA : (A : Set (Site d)) ⊆ box d n) :
    (boxSpinSupport d n A).card = A.card := by
  classical
  apply Finset.card_bij (fun (x : boxVerts d n) _ => (x : Site d))
  · intro x hx
    simpa [boxSpinSupport] using hx
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro x hx
    let y : boxVerts d n := ⟨x, hA hx⟩
    exact ⟨y, by simp [boxSpinSupport, y, hx], rfl⟩

theorem freeFiniteMeasure_real_allClustersEvenEvent
    (n : Nat) {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A : Finset (Site d)) (hA : (A : Set (Site d)) ⊆ box d n) :
    (freeFiniteMeasure d n hp hp1 (by norm_num : (0 : Real) < 2) : Measure _).real
        (allClustersEvenEvent (hypercubicLattice d) A) =
      allClustersEvenProb (boxGraph d n) p (boxSpinSupport d n A) := by
  classical
  let E := allClustersEvenEvent (hypercubicLattice d) A
  have hE : MeasurableSet E := measurableSet_allClustersEvenEvent A
  have hpre : extendEdge d n ⁻¹' E =
      allClustersEvenEvent (boxGraph d n) (boxSpinSupport d n A) := by
    ext omega
    exact allClustersEven_box_iff_extendEdge n omega A hA |>.symm
  unfold freeFiniteMeasure Measure.real
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply (measurable_extendEdge d n) hE]
  rw [hpre, fkPMF_toMeasure_toReal d n hp hp1
    (by norm_num : (0 : Real) < 2)]
  unfold allClustersEvenProb allClustersEvenEvent
  simp only [Set.indicator_apply]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases h : AllClustersEven (boxGraph d n) omega (boxSpinSupport d n A)
  · simp [h]
  · simp [h]



theorem integral_freeState_spinProd_eq_freeInfinite_allClustersEven
    (d : Nat) (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (A : Finset (Site d)) (hAeven : Even A.card) :
    (∫ sigma, spinProd A sigma
      ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) =
      (freeInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            linarith)
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) : Measure _).real
        (allClustersEvenEvent (hypercubicLattice d) A) := by
  let p : Real := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  let phiInf := freeInfiniteVolume d hp hp1 (by norm_num : (0 : Real) < 2)
  obtain ⟨phi, hphi, hconv⟩ :=
    freeInfiniteVolume_isLimit d hp hp1 (by norm_num : (0 : Real) < 2)
  have hunique : (phiInf : Measure _) (atLeastTwoInfinite d) = 0 := by
    exact (freeInfinite_q2_canonical_uniqueness_all_parameters hd hp hp1).2.1
  have hport : Tendsto
      (fun k => (freeFiniteMeasure d (phi k) hp hp1
        (by norm_num : (0 : Real) < 2) : Measure _).real
          (allClustersEvenEvent (hypercubicLattice d) A))
      atTop
      (nhds ((phiInf : Measure _).real
        (allClustersEvenEvent (hypercubicLattice d) A))) := by
    apply WeakConvergesTo.tendsto_real_of_null_frontier hconv
    exact measure_frontier_allClustersEvenEvent_eq_zero phiInf hunique A
  have hspin := (integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta.le A).comp hphi.tendsto_atTop
  obtain ⟨N, hAN⟩ := Lattice.finite_subset_box
    (A : Set (Site d)) A.finite_toSet
  have heq : (fun k => ∫ sigma, spinProd A sigma
        ∂(freeMeasure d (phi k) beta 0 : Measure (ConfigSpace (Site d)))) =ᶠ[atTop]
      (fun k => (freeFiniteMeasure d (phi k) hp hp1
        (by norm_num : (0 : Real) < 2) : Measure _).real
          (allClustersEvenEvent (hypercubicLattice d) A)) := by
    filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with k hk
    have hAk : (A : Set (Site d)) ⊆ box d (phi k) :=
      hAN.trans (box_mono d hk)
    calc
      (∫ sigma, spinProd A sigma
          ∂(freeMeasure d (phi k) beta 0 : Measure (ConfigSpace (Site d)))) =
          isingExpectation (sctBoxGraph d (phi k)) beta 0
            (spinProd (boxSpinSupport d (phi k) A)) :=
        integral_freeMeasure_spinProd d (phi k) beta 0 A hAk
      _ = isingExpectation (boxGraph d (phi k)) beta 0
            (spinProd (boxSpinSupport d (phi k) A)) := by
        simpa only [boxGraph_eq_sctBoxGraph]
      _ = allClustersEvenProb (boxGraph d (phi k)) p
            (boxSpinSupport d (phi k) A) := by
        simpa only [p] using
          isingExpectation_spinProd_eq_allClustersEvenProb
            (boxGraph d (phi k)) beta (boxSpinSupport d (phi k) A)
              (by rwa [boxSpinSupport_card (phi k) A hAk])
      _ = (freeFiniteMeasure d (phi k) hp hp1
            (by norm_num : (0 : Real) < 2) : Measure _).real
          (allClustersEvenEvent (hypercubicLattice d) A) :=
        (freeFiniteMeasure_real_allClustersEvenEvent (phi k) hp hp1 A hAk).symm
  have hspin' := hspin.congr' heq
  have hlimits := tendsto_nhds_unique hspin' hport
  simpa only [phiInf, p] using hlimits

end StatMech.FrontierB
