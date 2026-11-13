/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.CurrentTraceCoarseUniqueness

open Filter MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem weight_zero_beta_of_edgeCurrent_ne_zero
    (J : Sym2 V -> Real) (m : EdgeCurrent G) (hm : m ≠ 0) :
    weight G 0 J (ofEdgeFun G m) = 0 := by
  classical
  obtain ⟨e, he⟩ : ∃ e, m e ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  rw [weight_ofEdgeFun]
  apply Finset.prod_eq_zero (i := e)
  · exact Finset.mem_univ e
  · rw [zero_mul, zero_pow he, zero_div]


theorem sourcelessCurrentPMF_zero_beta
    (J : Sym2 V -> Real) (hJ : ∀ e, 0 <= J e) :
    sourcelessCurrentPMF G 0 J le_rfl hJ = PMF.pure 0 := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m
    rw [PMF.pure_apply_self]
    rw [← (sourcelessCurrentPMF G 0 J le_rfl hJ).tsum_coe,
      tsum_eq_single (0 : EdgeCurrent G)]
    intro n hn
    rw [sourcelessCurrentPMF, currentPMF_apply]
    simp [currentRawMass,
      weight_zero_beta_of_edgeCurrent_ne_zero G J n hn]
  · rw [PMF.pure_apply_of_ne _ _ hm]
    rw [sourcelessCurrentPMF, currentPMF_apply]
    simp [currentRawMass, weight_zero_beta_of_edgeCurrent_ne_zero G J m hm]


theorem boundaryCurrentPMF_zero_beta
    (J : Sym2 V -> Real) (hJ : ∀ e, 0 <= J e) (interior : Finset V) :
    boundaryCurrentPMF G 0 J le_rfl hJ interior = PMF.pure 0 := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m
    rw [PMF.pure_apply_self]
    rw [← (boundaryCurrentPMF G 0 J le_rfl hJ interior).tsum_coe,
      tsum_eq_single (0 : EdgeCurrent G)]
    intro n hn
    rw [boundaryCurrentPMF_apply]
    simp [boundaryCurrentRawMass,
      weight_zero_beta_of_edgeCurrent_ne_zero G J n hn]
  · rw [PMF.pure_apply_of_ne _ _ hm]
    rw [boundaryCurrentPMF_apply]
    simp [boundaryCurrentRawMass,
      weight_zero_beta_of_edgeCurrent_ne_zero G J m hm]


@[simp] theorem extendBoxCurrent_zero (d n : Nat) :
    extendBoxCurrent d n (0 : EdgeCurrent (StatMech.FK.boxGraph d n)) = 0 := by
  funext e
  simp [extendBoxCurrent]


theorem freeBoxCurrentMeasure_zero_beta (d n : Nat) :
    (freeBoxCurrentMeasure d n 0 le_rfl :
      Measure (InfiniteCurrentConfig (Sym2 (Site d)))) = Measure.dirac 0 := by
  change Measure.map (extendBoxCurrent d n)
      ((sourcelessCurrentPMF (StatMech.FK.boxGraph d n) 0
        (fun _ => 1) le_rfl (fun _ => by positivity)).toMeasure) = _
  rw [sourcelessCurrentPMF_zero_beta, PMF.toMeasure_pure,
    Measure.map_dirac', extendBoxCurrent_zero]
  exact measurable_extendBoxCurrent d n


theorem plusBoxCurrentMeasure_zero_beta (d n : Nat) :
    (plusBoxCurrentMeasure d n 0 le_rfl :
      Measure (InfiniteCurrentConfig (Sym2 (Site d)))) = Measure.dirac 0 := by
  change Measure.map (extendBoxCurrent d n)
      ((boundaryCurrentPMF (StatMech.FK.boxGraph d n) 0
        (fun _ => 1) le_rfl (fun _ => by positivity)
        (boxCurrentInterior d n)).toMeasure) = _
  rw [boundaryCurrentPMF_zero_beta, PMF.toMeasure_pure,
    Measure.map_dirac', extendBoxCurrent_zero]
  exact measurable_extendBoxCurrent d n


theorem infiniteFreeCurrentMeasure_zero_beta (d : Nat) :
    (infiniteFreeCurrentMeasure d 0 le_rfl :
      Measure (InfiniteCurrentConfig (Sym2 (Site d)))) = Measure.dirac 0 := by
  let zeroLaw : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
    ⟨Measure.dirac 0, Measure.dirac.isProbabilityMeasure⟩
  have heq :
      ((fun n => freeBoxCurrentMeasure d n 0 le_rfl) ∘
        infiniteCurrentBoxSubsequence d 0 le_rfl) = fun _ => zeroLaw := by
    funext k
    apply ProbabilityMeasure.toMeasure_injective
    exact freeBoxCurrentMeasure_zero_beta d _
  have hlim : zeroLaw = infiniteFreeCurrentMeasure d 0 le_rfl :=
    tendsto_nhds_unique
      (show Tendsto
        ((fun n => freeBoxCurrentMeasure d n 0 le_rfl) ∘
          infiniteCurrentBoxSubsequence d 0 le_rfl) atTop (nhds zeroLaw) by
        rw [heq]
        exact tendsto_const_nhds)
      (freeBoxCurrentMeasure_tendsto_infiniteFree d 0 le_rfl)
  exact congrArg ProbabilityMeasure.toMeasure hlim.symm


theorem infinitePlusCurrentMeasure_zero_beta (d : Nat) :
    (infinitePlusCurrentMeasure d 0 le_rfl :
      Measure (InfiniteCurrentConfig (Sym2 (Site d)))) = Measure.dirac 0 := by
  let zeroLaw : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
    ⟨Measure.dirac 0, Measure.dirac.isProbabilityMeasure⟩
  have heq :
      ((fun n => plusBoxCurrentMeasure d n 0 le_rfl) ∘
        infiniteCurrentBoxSubsequence d 0 le_rfl) = fun _ => zeroLaw := by
    funext k
    apply ProbabilityMeasure.toMeasure_injective
    exact plusBoxCurrentMeasure_zero_beta d _
  have hlim : zeroLaw = infinitePlusCurrentMeasure d 0 le_rfl :=
    tendsto_nhds_unique
      (show Tendsto
        ((fun n => plusBoxCurrentMeasure d n 0 le_rfl) ∘
          infiniteCurrentBoxSubsequence d 0 le_rfl) atTop (nhds zeroLaw) by
        rw [heq]
        exact tendsto_const_nhds)
      (plusBoxCurrentMeasure_tendsto_infinitePlus d 0 le_rfl)
  exact congrArg ProbabilityMeasure.toMeasure hlim.symm




theorem independentSuperposedTraceLaw_eq_dirac_allClosed_of_eq_zero
    {E : Type*} [Countable E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (hmu : (mu : Measure (InfiniteCurrentConfig E)) = Measure.dirac 0)
    (hnu : (nu : Measure (InfiniteCurrentConfig E)) = Measure.dirac 0) :
    (independentSuperposedTraceLaw mu nu : Measure (ConfigSpace E)) =
      Measure.dirac (fun _ => false) := by
  change Measure.map superposedCurrentTrace
    ((mu : Measure (InfiniteCurrentConfig E)).prod
      (nu : Measure (InfiniteCurrentConfig E))) = _
  rw [hmu, hnu, Measure.dirac_prod_dirac,
    Measure.map_dirac' continuous_superposedCurrentTrace.measurable]
  congr

theorem freeFreeSuperposedTraceLaw_zero_beta (d : Nat) :
    (independentSuperposedTraceLaw
      (infiniteFreeCurrentMeasure d 0 le_rfl)
      (infiniteFreeCurrentMeasure d 0 le_rfl) :
        Measure (ConfigSpace (Sym2 (Site d)))) =
      Measure.dirac (fun _ => false) :=
  independentSuperposedTraceLaw_eq_dirac_allClosed_of_eq_zero _ _
    (infiniteFreeCurrentMeasure_zero_beta d)
    (infiniteFreeCurrentMeasure_zero_beta d)

theorem freePlusSuperposedTraceLaw_zero_beta (d : Nat) :
    (independentSuperposedTraceLaw
      (infiniteFreeCurrentMeasure d 0 le_rfl)
      (infinitePlusCurrentMeasure d 0 le_rfl) :
        Measure (ConfigSpace (Sym2 (Site d)))) =
      Measure.dirac (fun _ => false) :=
  independentSuperposedTraceLaw_eq_dirac_allClosed_of_eq_zero _ _
    (infiniteFreeCurrentMeasure_zero_beta d)
    (infinitePlusCurrentMeasure_zero_beta d)

theorem plusPlusSuperposedTraceLaw_zero_beta (d : Nat) :
    (independentSuperposedTraceLaw
      (infinitePlusCurrentMeasure d 0 le_rfl)
      (infinitePlusCurrentMeasure d 0 le_rfl) :
        Measure (ConfigSpace (Sym2 (Site d)))) =
      Measure.dirac (fun _ => false) :=
  independentSuperposedTraceLaw_eq_dirac_allClosed_of_eq_zero _ _
    (infinitePlusCurrentMeasure_zero_beta d)
    (infinitePlusCurrentMeasure_zero_beta d)


theorem openSubgraph_allClosed (d : Nat) :
    openSubgraph d (fun _ => false) = ⊥ := by
  ext x y
  simp [openSubgraph_adj]


theorem cluster_allClosed (d : Nat) (x : Site d) :
    cluster d (fun _ => false) x = {x} := by
  ext y
  rw [mem_cluster]
  change (openSubgraph d (fun _ => false)).Reachable x y ↔ y ∈ ({x} : Set (Site d))
  rw [openSubgraph_allClosed, SimpleGraph.reachable_bot]
  simp [eq_comm]


@[simp] theorem numInfiniteClusters_allClosed (d : Nat) :
    numInfiniteClusters d (fun _ => false) = 0 := by
  have hempty : infiniteClusters d (fun _ => false) = ∅ := by
    ext C
    simp only [infiniteClusters, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨hC, x, rfl⟩
    rw [cluster_allClosed] at hC
    exact (Set.finite_singleton x).not_infinite hC
  rw [numInfiniteClusters, hempty, Set.encard_empty]


theorem dirac_allClosed_cluster_uniqueness (d : Nat) :
    let mu := Measure.dirac
      (fun _ => false : ConfigSpace (Sym2 (Site d)))
    (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨
        mu {omega | numInfiniteClusters d omega = 1} = 1) ∧
      mu (atLeastTwoInfinite d) = 0 ∧
      mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
  dsimp only
  have hzero : numInfiniteClusters d
      (fun _ => false : ConfigSpace (Sym2 (Site d))) = 0 :=
    numInfiniteClusters_allClosed d
  constructor
  · left
    rw [Measure.dirac_apply']
    · simp [hzero]
    · exact measurable_numInfiniteClusters (MeasurableSet.singleton 0)
  constructor
  · rw [Measure.dirac_apply']
    · simp [atLeastTwoInfinite, hzero]
    · exact measurableSet_atLeastTwoInfinite
  · rw [Measure.dirac_apply']
    · simp [hzero]
    · exact measurable_numInfiniteClusters
        (MeasurableSet.of_discrete)

theorem freeFreeSuperposedTraceLaw_zero_beta_uniqueness (d : Nat) :
    let mu := (independentSuperposedTraceLaw
      (infiniteFreeCurrentMeasure d 0 le_rfl)
      (infiniteFreeCurrentMeasure d 0 le_rfl) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨
        mu {omega | numInfiniteClusters d omega = 1} = 1) ∧
      mu (atLeastTwoInfinite d) = 0 ∧
      mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
  rw [freeFreeSuperposedTraceLaw_zero_beta]
  exact dirac_allClosed_cluster_uniqueness d

theorem freePlusSuperposedTraceLaw_zero_beta_uniqueness (d : Nat) :
    let mu := (independentSuperposedTraceLaw
      (infiniteFreeCurrentMeasure d 0 le_rfl)
      (infinitePlusCurrentMeasure d 0 le_rfl) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨
        mu {omega | numInfiniteClusters d omega = 1} = 1) ∧
      mu (atLeastTwoInfinite d) = 0 ∧
      mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
  rw [freePlusSuperposedTraceLaw_zero_beta]
  exact dirac_allClosed_cluster_uniqueness d

theorem plusPlusSuperposedTraceLaw_zero_beta_uniqueness (d : Nat) :
    let mu := (independentSuperposedTraceLaw
      (infinitePlusCurrentMeasure d 0 le_rfl)
      (infinitePlusCurrentMeasure d 0 le_rfl) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨
        mu {omega | numInfiniteClusters d omega = 1} = 1) ∧
      mu (atLeastTwoInfinite d) = 0 ∧
      mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
  rw [plusPlusSuperposedTraceLaw_zero_beta]
  exact dirac_allClosed_cluster_uniqueness d

end StatMech.FrontierB
