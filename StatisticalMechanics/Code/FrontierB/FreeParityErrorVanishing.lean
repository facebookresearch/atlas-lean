/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FreeInfiniteMultipointES
import Code.FK.FreePairMixingFromTail

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

theorem twoArmDisconnectedTraceEvent_real_tendsto_zero
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0)
    (x y : Site d) :
    Tendsto (fun m => (mu : Measure _).real
      (twoArmDisconnectedTraceEvent m x y)) atTop (nhds 0) := by
  obtain ⟨R, hR⟩ := Percolation.finite_subset_box
    ({x, y} : Set (Site d)) (Set.toFinite _)
  have hxR : x ∈ box d R := hR (by simp)
  have hyR : y ∈ box d R := hR (by simp)
  have htail : Antitone
      (fun n => twoArmDisconnectedTraceEvent (R + n + 1) x y) :=
    twoArmDisconnectedTraceEvent_tail_antitone hxR hyR
  have hmeas : ∀ n, NullMeasurableSet
      (twoArmDisconnectedTraceEvent (R + n + 1) x y) (mu : Measure _) :=
    fun n => (isClopen_twoArmDisconnectedTraceEvent
      (R + n + 1) x y).isOpen.measurableSet.nullMeasurableSet
  have hdistinct : (mu : Measure _) (distinctInfiniteClusterEvent x y) = 0 :=
    measure_mono_null (distinctInfiniteClusterEvent_subset_atLeastTwoInfinite x y)
      hunique
  have htailMeasure : Tendsto
      (fun n => (mu : Measure _)
        (twoArmDisconnectedTraceEvent (R + n + 1) x y))
      atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop (μ := (mu : Measure _)) hmeas htail
      ⟨0, measure_ne_top (mu : Measure _)
        (twoArmDisconnectedTraceEvent (R + 0 + 1) x y)⟩
    rw [iInter_twoArmDisconnectedTraceEvent hxR hyR, hdistinct] at h
    exact h
  have htailReal : Tendsto
      (fun n => (mu : Measure _).real
        (twoArmDisconnectedTraceEvent (R + n + 1) x y))
      atTop (nhds 0) := (ENNReal.tendsto_toReal (by simp)).comp htailMeasure
  exact (tendsto_add_atTop_iff_nat (R + 1)).1 (by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htailReal)

theorem twoOddCrossClustersEvent_subset_twoArmUnion
    (m : Nat) (hm : 1 ≤ m) (A B : Finset (Site d))
    (hA : (A : Set (Site d)) ⊆ box d (m - 1))
    (hB : (B : Set (Site d)) ⊆ (box d (m - 1))ᶜ) :
    twoOddCrossClustersEvent (hypercubicLattice d) A B ⊆
      ⋃ x ∈ A, ⋃ y ∈ A, twoArmDisconnectedTraceEvent m x y := by
  classical
  intro omega homega
  obtain ⟨C1, C2, hne, hC1A, hC1B, hC2A, hC2B⟩ := homega
  have pick {C : (openSub (hypercubicLattice d) omega).ConnectedComponent}
      {S : Finset (Site d)} (hodd : Odd
        (clusterMarkCount (hypercubicLattice d) omega S C)) :
      ∃ x ∈ S, (openSub (hypercubicLattice d) omega).connectedComponentMk x = C := by
    have hmem := mem_markedComponents_of_odd_clusterMarkCount
      (hypercubicLattice d) omega S C hodd
    simpa only [markedComponents, Finset.mem_image] using hmem
  obtain ⟨x1, hx1A, hx1C⟩ := pick hC1A
  obtain ⟨y1, hy1B, hy1C⟩ := pick hC1B
  obtain ⟨x2, hx2A, hx2C⟩ := pick hC2A
  obtain ⟨y2, hy2B, hy2C⟩ := pick hC2B
  have hx1y1 : Connected d omega x1 y1 := by
    exact SimpleGraph.ConnectedComponent.eq.mp (hx1C.trans hy1C.symm)
  have hx2y2 : Connected d omega x2 y2 := by
    exact SimpleGraph.ConnectedComponent.eq.mp (hx2C.trans hy2C.symm)
  have hnotx : ¬Connected d omega x1 x2 := by
    intro hconn
    apply hne
    rw [← hx1C, ← hx2C]
    exact SimpleGraph.ConnectedComponent.sound hconn
  have hx1arm : omega ∈ traceBoundaryConnectionEvent m x1 :=
    mem_traceBoundaryConnectionEvent_of_connected_outside hm (hA hx1A)
      (hB hy1B) hx1y1
  have hx2arm : omega ∈ traceBoundaryConnectionEvent m x2 :=
    mem_traceBoundaryConnectionEvent_of_connected_outside hm (hA hx2A)
      (hB hy2B) hx2y2
  rw [Set.mem_iUnion]
  refine ⟨x1, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hx1A, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨x2, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hx2A, ?_⟩
  rw [mem_twoArmDisconnectedTraceEvent]
  refine ⟨mem_traceBoundaryConnectionEvent.1 hx1arm,
    mem_traceBoundaryConnectionEvent.1 hx2arm, ?_⟩
  intro hbox
  exact hnotx hbox.2.2.connected

noncomputable def inverseAxisTranslateFinset
    (hd : 1 ≤ d) (n : Nat) (B : Finset (Site d)) : Finset (Site d) :=
  B.image fun x => (FK.freeAxisTranslationPower hd n)⁻¹ • x

theorem inverseAxisTranslateFinset_eventually_outside_box
    (hd : 1 ≤ d) (B : Finset (Site d)) (m : Nat) :
    ∀ᶠ n in atTop, (inverseAxisTranslateFinset hd n B : Set (Site d)) ⊆
      (box d m)ᶜ := by
  let M := B.sup fun x => (x ⟨0, hd⟩).natAbs
  filter_upwards [eventually_ge_atTop (M + m + 1)] with n hn
  intro z hz
  simp only [inverseAxisTranslateFinset, Finset.coe_image, Set.mem_image,
    Finset.mem_coe] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [Set.mem_compl_iff]
  intro hbox
  have hxBound : x ⟨0, hd⟩ ≤ (M : Int) := by
    exact (Int.le_natAbs.trans (by exact_mod_cast
      (Finset.le_sup (f := fun x => (x ⟨0, hd⟩).natAbs) hx)))
  have hcoord := hbox ⟨0, hd⟩
  have hval :
      (((FK.freeAxisTranslationPower hd n)⁻¹ • x) ⟨0, hd⟩) =
        x ⟨0, hd⟩ - n := by
    change (-(Multiplicative.toAdd (FK.freeAxisTranslationPower hd n)) + x)
      ⟨0, hd⟩ = _
    simp [FK.freeAxisTranslationPower]
    ring
  rw [hval] at hcoord
  have hneg : x ⟨0, hd⟩ - (n : Int) ≤ -(m + 1 : Int) := by omega
  have habs : ((x ⟨0, hd⟩ - (n : Int)).natAbs : Int) =
      -(x ⟨0, hd⟩ - (n : Int)) := by
    rw [← Int.natAbs_neg, Int.natAbs_of_nonneg]
    omega
  have hcoord' : ((x ⟨0, hd⟩ - (n : Int)).natAbs : Int) ≤ m := by
    exact_mod_cast hcoord
  rw [habs] at hcoord'
  omega




theorem twoOddCrossClusters_axisTranslate_real_tendsto_zero
    (hd : 1 ≤ d)
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0)
    (A B : Finset (Site d)) :
    Tendsto (fun n => (mu : Measure _).real
      (twoOddCrossClustersEvent (hypercubicLattice d) A
        (inverseAxisTranslateFinset hd n B))) atTop (nhds 0) := by
  have hsum : Tendsto (fun m => ∑ x ∈ A, ∑ y ∈ A,
      (mu : Measure _).real (twoArmDisconnectedTraceEvent m x y))
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum A (fun x hx =>
      tendsto_finsetSum A (fun y hy =>
        twoArmDisconnectedTraceEvent_real_tendsto_zero mu hunique x y))
  obtain ⟨R, hAR⟩ := Percolation.finite_subset_box
    (A : Set (Site d)) A.finite_toSet
  rw [Metric.tendsto_atTop] at hsum ⊢
  intro epsilon hepsilon
  obtain ⟨M, hM⟩ := hsum epsilon hepsilon
  let m := max M (R + 1)
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hAbox : (A : Set (Site d)) ⊆ box d (m - 1) := by
    apply hAR.trans
    apply box_mono d
    dsimp [m]
    omega
  have hsmall : ∑ x ∈ A, ∑ y ∈ A,
      (mu : Measure _).real (twoArmDisconnectedTraceEvent m x y) < epsilon := by
    have hdist := hM m (by dsimp [m]; omega)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (Finset.sum_nonneg fun x hx =>
        Finset.sum_nonneg fun y hy => measureReal_nonneg)] at hdist
    exact hdist
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (inverseAxisTranslateFinset_eventually_outside_box hd B (m - 1))
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hsubset := twoOddCrossClustersEvent_subset_twoArmUnion m hm A
    (inverseAxisTranslateFinset hd n B) hAbox (hN n hn)
  have hfinite : (mu : Measure (ConfigSpace (Sym2 (Site d))))
      (⋃ x ∈ A, ⋃ y ∈ A, twoArmDisconnectedTraceEvent m x y) ≠ ⊤ :=
    measure_ne_top (mu : Measure (ConfigSpace (Sym2 (Site d)))) _
  calc
    (mu : Measure _).real
        (twoOddCrossClustersEvent (hypercubicLattice d) A
          (inverseAxisTranslateFinset hd n B)) ≤
      (mu : Measure _).real
        (⋃ x ∈ A, ⋃ y ∈ A, twoArmDisconnectedTraceEvent m x y) :=
      measureReal_mono (μ := (mu : Measure _)) hsubset
        (by exact hfinite)
    _ ≤ ∑ x ∈ A, (mu : Measure _).real
        (⋃ y ∈ A, twoArmDisconnectedTraceEvent m x y) :=
      measureReal_biUnion_finset_le A _
    _ ≤ ∑ x ∈ A, ∑ y ∈ A,
        (mu : Measure _).real (twoArmDisconnectedTraceEvent m x y) :=
      Finset.sum_le_sum fun x hx => measureReal_biUnion_finset_le A _
    _ < epsilon := hsmall

end StatMech.FrontierB
