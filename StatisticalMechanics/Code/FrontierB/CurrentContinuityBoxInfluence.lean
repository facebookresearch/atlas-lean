/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.CurrentContinuityOddInsertion
import Code.FrontierB.FinitePlusBoundarySwitchingBridge
import Code.FrontierB.CurrentConnectivityNoEscape
import Code.Percolation.SubcriticalDecayFull
import Code.FK.TailLimit
import Code.FK.TwoPointPositiveFull

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open Finset Sharpness Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance currentContinuityBoxInfluencePropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p



noncomputable def boxCurrentEdgeOfAdjacent
    {d n : ℕ} {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n)
    (hxy : (hypercubicLattice d).Adj x y) :
    (StatMech.FK.boxGraph d n).edgeFinset :=
  ⟨s((⟨x, hx⟩ : StatMech.FK.boxVerts d n), ⟨y, hy⟩),
    StatMech.FK.boxEdge_mem n _ x y hxy (by rfl)⟩

theorem boxCurrentEdgeOfAdjacent_endpoints
    {d n : ℕ} {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n)
    (hxy : (hypercubicLattice d).Adj x y) :
    let e := boxCurrentEdgeOfAdjacent hx hy hxy
    ({e.1.out.1, e.1.out.2} : Finset (StatMech.FK.boxVerts d n)) =
      ({(⟨x, hx⟩ : StatMech.FK.boxVerts d n),
        (⟨y, hy⟩ : StatMech.FK.boxVerts d n)} : Finset _) := by
  dsimp only
  calc
    ({(boxCurrentEdgeOfAdjacent hx hy hxy).1.out.1,
        (boxCurrentEdgeOfAdjacent hx hy hxy).1.out.2} : Finset _) =
        (boxCurrentEdgeOfAdjacent hx hy hxy).1.toFinset := by
      rw [← Sym2.toFinset_mk_eq]
      exact congrArg Sym2.toFinset
        (boxCurrentEdgeOfAdjacent hx hy hxy).1.out_eq
    _ = _ := by
      change s((⟨x, hx⟩ : StatMech.FK.boxVerts d n),
        (⟨y, hy⟩ : StatMech.FK.boxVerts d n)).toFinset = _
      exact Sym2.toFinset_mk_eq


theorem boundarySourceCurrentPairPMF_superpositionEvent_real
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources exactSecondSources : Finset V)
    (hfirst : 0 < boundarySourceCurrentSum G beta J interior internalSources)
    (hsecond : 0 < currentSum G beta J exactSecondSources)
    (P : Current V -> Prop) [DecidablePred P] :
    (boundarySourceCurrentPairPMF G beta J hbeta hJ interior
        internalSources exactSecondSources hfirst hsecond).toMeasure.real
        (sourcePairSuperpositionEvent G P) =
      boundarySourceGatedPairSum G beta J interior internalSources
          exactSecondSources P /
        (boundarySourceCurrentSum G beta J interior internalSources *
          currentSum G beta J exactSecondSources) := by
  have hnonneg : 0 ≤ boundarySourceGatedPairSum G beta J interior
      internalSources exactSecondSources P := by
    rw [boundarySourceGatedPairSum_eq_tsum]
    apply tsum_nonneg
    rintro ⟨m, n⟩
    split <;> split <;> split <;> simp_all only [mul_zero, zero_mul, mul_one]
    all_goals try exact le_refl _
    exact mul_nonneg
      (Ising.acw_weight_nonneg G beta J hbeta hJ _)
      (Ising.acw_weight_nonneg G beta J hbeta hJ _)
  have h := boundarySourceCurrentPairPMF_superpositionEvent
    G beta J hbeta hJ interior internalSources exactSecondSources
      hfirst hsecond P
  rw [Measure.real, h, ENNReal.toReal_ofReal]
  exact div_nonneg hnonneg (mul_pos hfirst hsecond).le



theorem boundarySource_twoPoint_ratio_gap_nonneg
    (beta : ℝ) (hbeta : 0 ≤ beta) (interior : Finset V)
    {u v : V} (huv : u ≠ v) (hu : u ∈ interior) (hv : v ∈ interior) :
    0 ≤ boundarySourceCurrentSum G beta (fun _ => 1) interior {u, v} /
          boundarySourceCurrentSum G beta (fun _ => 1) interior ∅ -
        currentSum G beta (fun _ => 1) {u, v} /
          currentSum G beta (fun _ => 1) ∅ := by
  let a := boundarySourceCurrentSum G beta (fun _ => 1) interior {u, v}
  let b := currentSum G beta (fun _ => 1) {u, v}
  let z := boundarySourceCurrentSum G beta (fun _ => 1) interior ∅
  let w := currentSum G beta (fun _ => 1) ∅
  have hz : 0 < z := lt_of_lt_of_le Real.zero_lt_one
    (one_le_boundaryCurrentSum G beta (fun _ => 1) hbeta
      (fun _ => by positivity) interior)
  have hw : 0 < w := Ising.acr_currentSum_empty_pos G beta (fun _ => 1)
  have hgap : a * w - z * b =
      boundarySourceGatedPairSum G beta (fun _ => 1) interior {u, v} ∅
        (fun m => ¬ CurrentConnected G m u v) := by
    simpa only [a, b, z, w] using
      boundarySource_twoPoint_gap_eq_notConnected G beta (fun _ => 1)
        interior huv hu hv
  have hraw : 0 ≤ boundarySourceGatedPairSum G beta (fun _ => 1)
      interior {u, v} ∅ (fun m => ¬ CurrentConnected G m u v) := by
    rw [boundarySourceGatedPairSum_eq_tsum]
    apply tsum_nonneg
    rintro ⟨m, n⟩
    split <;> split <;> split <;>
      simp_all only [mul_zero, zero_mul, mul_one]
    all_goals try exact le_refl _
    exact mul_nonneg
      (Ising.acw_weight_nonneg G beta (fun _ => 1) hbeta
        (fun _ => by positivity) _)
      (Ising.acw_weight_nonneg G beta (fun _ => 1) hbeta
        (fun _ => by positivity) _)
  have hfrac : a / z - b / w = (a * w - z * b) / (z * w) := by
    field_simp [hz.ne', hw.ne']
  rw [hfrac, hgap]
  exact div_nonneg hraw (mul_pos hz hw).le



theorem sourcePairSuperpositionEvent_exterior_eq_boundaryConnection
    (d n : ℕ) (x : StatMech.FK.boxVerts d n) :
    sourcePairSuperpositionEvent (StatMech.FK.boxGraph d n)
        (fun m => ∃ z, z ∉ boxCurrentInterior d n ∧
          CurrentConnected (StatMech.FK.boxGraph d n) m x z) =
      (Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹'
        (superposedCurrentTrace ⁻¹' traceBoundaryConnectionEvent n (x : Site d)) := by
  ext pq
  change (∃ z, z ∉ boxCurrentInterior d n ∧
      CurrentConnected (StatMech.FK.boxGraph d n)
        (ofEdgeFun (StatMech.FK.boxGraph d n)
          (fun e => pq.1 e + pq.2 e)) x z) ↔ _
  rw [Set.mem_preimage, Set.mem_preimage,
    mem_traceBoundaryConnectionEvent]
  constructor
  · rintro ⟨z, hzout, hxz⟩
    have hzbdry : StatMech.FK.boxBoundary d n z := by
      simpa [boxCurrentInterior] using hzout
    have hevent :=
      (currentConnected_ofEdgeFun_add_iff_boxConnectionEvent
        d n pq.1 pq.2 x z).mp hxz
    rcases hevent with ⟨hx, hz, hconn⟩
    exact ⟨hx, z.1, hz, hzbdry, hconn⟩
  · rintro ⟨hx, z, hz, hzbdry, hconn⟩
    let zb : StatMech.FK.boxVerts d n := ⟨z, hz⟩
    refine ⟨zb, ?_, ?_⟩
    · simpa [boxCurrentInterior, StatMech.FK.boxBoundary, zb] using hzbdry.2
    · apply (currentConnected_ofEdgeFun_add_iff_boxConnectionEvent
        d n pq.1 pq.2 x zb).mpr
      exact ⟨hx, hz, hconn⟩



theorem traceBoundaryConnectionEvent_subset_le
    {d m n : ℕ} {x : Site d}
    (hm : 1 ≤ m) (hx : x ∈ box d (m - 1)) (hmn : m ≤ n) :
    traceBoundaryConnectionEvent n x ⊆ traceBoundaryConnectionEvent m x := by
  intro omega homega
  rw [mem_traceBoundaryConnectionEvent] at homega ⊢
  obtain ⟨_, z, hz, hzbdry, hconn⟩ := homega
  have hzout : z ∉ box d (m - 1) := by
    intro hzin
    exact hzbdry.2 (box_mono d (by omega) hzin)
  exact mem_traceBoundaryConnectionEvent.1
    (mem_traceBoundaryConnectionEvent_of_connected_outside
      hm hx hzout hconn.connected)



theorem traceBoundaryConnectionEvent_subset_crossingEventFrom
    {d n : ℕ} {x : Site d} :
    traceBoundaryConnectionEvent n x ⊆ crossingEventFrom d x n := by
  intro omega homega
  rw [mem_traceBoundaryConnectionEvent] at homega
  obtain ⟨_, z, _, hzbdry, hconn⟩ := homega
  exact ⟨z, hconn.connected, hzbdry.2⟩



theorem crossingEventFrom_real_tendsto_clusterInfinite
    (d : ℕ) (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (x : Site d) :
    Tendsto (fun n => (mu : Measure _).real (crossingEventFrom d x n)) atTop
      (nhds ((mu : Measure _).real (StatMech.FK.clusterInfiniteEvent d x))) := by
  have hinter : (⋂ n : ℕ, crossingEventFrom d x n) =
      StatMech.FK.clusterInfiniteEvent d x := by
    ext omega
    simp only [Set.mem_iInter, mem_crossingEventFrom,
      StatMech.FK.clusterInfiniteEvent, Set.mem_setOf_eq, cluster_infinite_iff]
    constructor
    · intro h m
      obtain ⟨z, hconn, hz⟩ := h (m + 1)
      exact ⟨z, by simpa using hz, hconn⟩
    · intro h n
      obtain ⟨z, hz, hconn⟩ := h (n - 1)
      exact ⟨z, hconn, hz⟩
  have hanti : Antitone (fun n => crossingEventFrom d x n) := by
    intro m n hmn omega homega
    obtain ⟨z, hconn, hz⟩ := homega
    exact ⟨z, hconn, fun hzin => hz (box_mono d (by omega) hzin)⟩
  have htend := tendsto_measure_iInter_atTop
    (μ := (mu : Measure _))
    (fun n => (measurableSet_crossingEventFrom x n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top
      (mu : Measure (ConfigSpace (Sym2 (Site d))))
      (crossingEventFrom d x 0)⟩
  rw [hinter] at htend
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (StatMech.FK.clusterInfiniteEvent d x))).comp htend
  simpa only [Function.comp_apply, Measure.real] using hreal



theorem beta_mul_box_twoPoint_gap_le_boundaryConnection
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (e : (StatMech.FK.boxGraph d n).edgeFinset)
    (hleft : e.1.out.1 ∈ boxCurrentInterior d n)
    (hright : e.1.out.2 ∈ boxCurrentInterior d n) :
    beta *
        (boundarySourceCurrentSum (StatMech.FK.boxGraph d n) beta
              (fun _ => 1) (boxCurrentInterior d n)
              {e.1.out.1, e.1.out.2} /
            boundarySourceCurrentSum (StatMech.FK.boxGraph d n) beta
              (fun _ => 1) (boxCurrentInterior d n) ∅ -
          currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1)
              {e.1.out.1, e.1.out.2} /
            currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) ∅) ≤
      ((plusBoxCurrentMeasure d n beta hbeta.le).prod
        (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _).real
          (superposedCurrentTrace ⁻¹'
            traceBoundaryConnectionEvent n (e.1.out.1 : Site d)) := by
  let G := StatMech.FK.boxGraph d n
  let interior := boxCurrentInterior d n
  let P : Sharpness.Current (StatMech.FK.boxVerts d n) → Prop :=
    fun m => ∃ z, z ∉ interior ∧ CurrentConnected G m e.1.out.1 z
  let hfirst : 0 < boundarySourceCurrentSum G beta (fun _ => 1) interior ∅ :=
    lt_of_lt_of_le Real.zero_lt_one
      (one_le_boundaryCurrentSum G beta (fun _ => 1) hbeta.le
        (fun _ => by positivity) interior)
  let hsecond : 0 < currentSum G beta (fun _ => 1) ∅ :=
    Ising.acr_currentSum_empty_pos G beta (fun _ => 1)
  have hins := beta_mul_boundarySource_twoPoint_gap_le_exteriorConnection_ratio
    G beta hbeta interior e hleft hright
  have hpmf := boundarySourceCurrentPairPMF_superpositionEvent_real
    G beta (fun _ => 1) hbeta.le (fun _ => by positivity)
      interior ∅ ∅ hfirst hsecond P
  have hC : MeasurableSet (superposedCurrentTrace ⁻¹'
      traceBoundaryConnectionEvent n (e.1.out.1 : Site d)) :=
    (isClopen_traceBoundaryConnectionEvent n
      (e.1.out.1 : Site d)).isOpen.measurableSet.preimage
        continuous_superposedCurrentTrace.measurable
  have hpush := plus_free_BoxCurrentMeasure_prod_apply
    d n beta hbeta.le
      (superposedCurrentTrace ⁻¹'
        traceBoundaryConnectionEvent n (e.1.out.1 : Site d)) hC
  have hpushReal := congrArg ENNReal.toReal hpush
  rw [← sourcePairSuperpositionEvent_exterior_eq_boundaryConnection
    d n e.1.out.1] at hpushReal
  unfold Measure.real at hpmf
  dsimp only [G, interior, P] at hpmf
  have hratio :
      boundarySourceGatedPairSum G beta (fun _ => 1) interior ∅ ∅ P /
          (boundarySourceCurrentSum G beta (fun _ => 1) interior ∅ *
            currentSum G beta (fun _ => 1) ∅) =
        ((plusBoxCurrentMeasure d n beta hbeta.le).prod
          (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _).real
            (superposedCurrentTrace ⁻¹'
              traceBoundaryConnectionEvent n (e.1.out.1 : Site d)) := by
    unfold Measure.real
    rw [← hpmf]
    exact hpushReal.symm
  exact hins.trans_eq (by simpa only [G, interior, P] using hratio)




theorem beta_mul_box_pair_gap_le_boundaryConnection_union
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d n) (hy : y ∈ box d n)
    (hxy : (hypercubicLattice d).Adj x y)
    (hxint : (⟨x, hx⟩ : StatMech.FK.boxVerts d n) ∈ boxCurrentInterior d n)
    (hyint : (⟨y, hy⟩ : StatMech.FK.boxVerts d n) ∈ boxCurrentInterior d n) :
    beta *
        (boundarySourceCurrentSum (StatMech.FK.boxGraph d n) beta
              (fun _ => 1) (boxCurrentInterior d n)
              {(⟨x, hx⟩ : StatMech.FK.boxVerts d n), ⟨y, hy⟩} /
            boundarySourceCurrentSum (StatMech.FK.boxGraph d n) beta
              (fun _ => 1) (boxCurrentInterior d n) ∅ -
          currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1)
              {(⟨x, hx⟩ : StatMech.FK.boxVerts d n), ⟨y, hy⟩} /
            currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) ∅) ≤
      ((plusBoxCurrentMeasure d n beta hbeta.le).prod
        (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _).real
          (superposedCurrentTrace ⁻¹'
            (traceBoundaryConnectionEvent n x ∪
              traceBoundaryConnectionEvent n y)) := by
  let e := boxCurrentEdgeOfAdjacent hx hy hxy
  have hends := boxCurrentEdgeOfAdjacent_endpoints hx hy hxy
  have hleft : e.1.out.1 ∈ boxCurrentInterior d n := by
    have hm : e.1.out.1 ∈
        ({e.1.out.1, e.1.out.2} : Finset (StatMech.FK.boxVerts d n)) := by simp
    rw [hends] at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · simpa only [hm] using hxint
    · simpa only [Finset.mem_singleton.mp hm] using hyint
  have hright : e.1.out.2 ∈ boxCurrentInterior d n := by
    have hm : e.1.out.2 ∈
        ({e.1.out.1, e.1.out.2} : Finset (StatMech.FK.boxVerts d n)) := by simp
    rw [hends] at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · simpa only [hm] using hxint
    · simpa only [Finset.mem_singleton.mp hm] using hyint
  have hbase := beta_mul_box_twoPoint_gap_le_boundaryConnection
    d n beta hbeta e hleft hright
  rw [hends] at hbase
  apply hbase.trans
  apply MeasureTheory.measureReal_mono
  · intro pair hpair
    change superposedCurrentTrace pair ∈
        traceBoundaryConnectionEvent n x ∪ traceBoundaryConnectionEvent n y
    change superposedCurrentTrace pair ∈
        traceBoundaryConnectionEvent n (e.1.out.1 : Site d) at hpair
    have hm : e.1.out.1 ∈
        ({e.1.out.1, e.1.out.2} : Finset (StatMech.FK.boxVerts d n)) := by simp
    rw [hends] at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · left
      simpa only [hm] using hpair
    · right
      simpa only [Finset.mem_singleton.mp hm] using hpair
  · exact measure_ne_top _ _

end StatMech.FrontierB
