/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FK.PeriodicPlanarGraph
import Code.FK.BulkDeviationProof
import Code.FK.InclusionExclusion

open Finset Set SimpleGraph MeasureTheory Filter Topology

namespace StatMech
namespace FK
namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

theorem PeriodicGraph.finite_subset_orbitBox (P : PeriodicGraph V)
    (S : Finset V) :
    ∃ n, ∀ v ∈ S, v ∈ P.orbitBox n := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
      obtain ⟨na, haBox⟩ := P.mem_orbitBox_of_eventually a
      obtain ⟨nS, hSBox⟩ := ih
      refine ⟨max na nS, ?_⟩
      intro v hv
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact P.orbitBox_mono (Nat.le_max_left _ _) haBox
      · exact P.orbitBox_mono (Nat.le_max_right _ _) (hSBox v hv)


theorem PeriodicGraph.exists_buffer_radius (P : PeriodicGraph V) (n : ℕ) :
    ∃ m, n < m ∧
      ∀ v ∈ P.orbitBox n, ∀ w, P.graph.Adj v w → w ∈ P.orbitBox m := by
  classical
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  let neighborUnion := (P.orbitBox n).biUnion
    (fun v => P.graph.neighborFinset v)
  obtain ⟨k, hk⟩ := P.finite_subset_orbitBox neighborUnion
  refine ⟨max (n + 1) k, Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
    (Nat.le_max_left _ _), ?_⟩
  intro v hv w hvw
  have hw : w ∈ neighborUnion := by
    rw [Finset.mem_biUnion]
    exact ⟨v, hv, by simpa only [SimpleGraph.mem_neighborFinset] using hvw⟩
  exact P.orbitBox_mono (Nat.le_max_right _ _) (hk w hw)


noncomputable def PeriodicGraph.nextBufferedRadius
    (P : PeriodicGraph V) (n : ℕ) : ℕ :=
  (P.exists_buffer_radius n).choose

theorem PeriodicGraph.lt_nextBufferedRadius (P : PeriodicGraph V) (n : ℕ) :
    n < P.nextBufferedRadius n :=
  (P.exists_buffer_radius n).choose_spec.1

theorem PeriodicGraph.neighbor_mem_nextBufferedRadius
    (P : PeriodicGraph V) (n : ℕ) {v w : V}
    (hv : v ∈ P.orbitBox n) (hvw : P.graph.Adj v w) :
    w ∈ P.orbitBox (P.nextBufferedRadius n) :=
  (P.exists_buffer_radius n).choose_spec.2 v hv w hvw


noncomputable def PeriodicGraph.bufferedRadius
    (P : PeriodicGraph V) : ℕ → ℕ
  | 0 => 0
  | n + 1 => P.nextBufferedRadius (P.bufferedRadius n)

@[simp] theorem PeriodicGraph.bufferedRadius_zero (P : PeriodicGraph V) :
    P.bufferedRadius 0 = 0 := rfl

@[simp] theorem PeriodicGraph.bufferedRadius_succ (P : PeriodicGraph V) (n : ℕ) :
    P.bufferedRadius (n + 1) =
      P.nextBufferedRadius (P.bufferedRadius n) := rfl

theorem PeriodicGraph.bufferedRadius_strictMono (P : PeriodicGraph V) :
    StrictMono P.bufferedRadius := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [P.bufferedRadius_succ]
  exact P.lt_nextBufferedRadius (P.bufferedRadius n)

theorem PeriodicGraph.id_le_bufferedRadius (P : PeriodicGraph V) (n : ℕ) :
    n ≤ P.bufferedRadius n := by
  induction n with
  | zero => simp
  | succ n ih =>
      exact Nat.succ_le_of_lt
        (ih.trans_lt (P.bufferedRadius_strictMono (Nat.lt_succ_self n)))


theorem PeriodicGraph.mem_bufferedBox_of_eventually
    (P : PeriodicGraph V) (v : V) :
    ∃ n, v ∈ P.orbitBox (P.bufferedRadius n) := by
  obtain ⟨n, hn⟩ := P.mem_orbitBox_of_eventually v
  exact ⟨n, P.orbitBox_mono (P.id_le_bufferedRadius n) hn⟩

abbrev PeriodicGraph.BufferedVertex (P : PeriodicGraph V) (n : ℕ) :=
  P.OrbitVertex (P.bufferedRadius n)

noncomputable instance PeriodicGraph.instFintypeBufferedVertex
    (P : PeriodicGraph V) (n : ℕ) : Fintype (P.BufferedVertex n) :=
  P.instFintypeOrbitVertex (P.bufferedRadius n)

instance PeriodicGraph.instDecidableEqBufferedVertex
    (P : PeriodicGraph V) (n : ℕ) : DecidableEq (P.BufferedVertex n) :=
  Subtype.instDecidableEq

noncomputable def PeriodicGraph.bufferedGraph (P : PeriodicGraph V) (n : ℕ) :
    SimpleGraph (P.BufferedVertex n) :=
  P.orbitGraph (P.bufferedRadius n)

noncomputable instance PeriodicGraph.instDecidableRelBufferedGraph
    (P : PeriodicGraph V) (n : ℕ) : DecidableRel (P.bufferedGraph n).Adj :=
  Classical.decRel _


noncomputable def PeriodicGraph.bufferedVertexInclLE (P : PeriodicGraph V)
    {n m : ℕ} (hnm : n ≤ m) : P.BufferedVertex n ↪ P.BufferedVertex m where
  toFun v := ⟨v.1, P.orbitBox_mono
    (P.bufferedRadius_strictMono.monotone hnm) v.2⟩
  inj' := by
    intro x y h
    have hval : (x : V) = (y : V) :=
      congrArg (fun z : P.BufferedVertex m => (z : V)) h
    exact Subtype.ext hval

@[simp] theorem PeriodicGraph.bufferedVertexInclLE_val
    (P : PeriodicGraph V) {n m : ℕ} (hnm : n ≤ m)
    (v : P.BufferedVertex n) :
    (P.bufferedVertexInclLE hnm v : V) = v := rfl

noncomputable def PeriodicGraph.bufferedVertexIncl (P : PeriodicGraph V) (n : ℕ) :
    P.BufferedVertex n ↪ P.BufferedVertex (n + 1) :=
  P.bufferedVertexInclLE (Nat.le_succ n)

theorem PeriodicGraph.bufferedAdjMatch (P : PeriodicGraph V) (n : ℕ) :
    ocd_AdjMatch (P.bufferedGraph n) (P.bufferedGraph (n + 1))
      (P.bufferedVertexIncl n) := by
  intro x y
  rfl


def PeriodicGraph.bufferedBoundary (P : PeriodicGraph V) (n : ℕ)
    (v : P.BufferedVertex n) : Prop :=
  ∃ w : V, P.graph.Adj v.1 w ∧
    w ∉ P.orbitBox (P.bufferedRadius n)

noncomputable instance PeriodicGraph.instDecidablePredBufferedBoundary
    (P : PeriodicGraph V) (n : ℕ) : DecidablePred (P.bufferedBoundary n) :=
  fun _ => Classical.dec _

theorem PeriodicGraph.neighbor_mem_buffered_succ
    (P : PeriodicGraph V) (n : ℕ) {v w : V}
    (hv : v ∈ P.orbitBox (P.bufferedRadius n))
    (hvw : P.graph.Adj v w) :
    w ∈ P.orbitBox (P.bufferedRadius (n + 1)) := by
  rw [P.bufferedRadius_succ]
  exact P.neighbor_mem_nextBufferedRadius (P.bufferedRadius n) hv hvw


theorem PeriodicGraph.not_bufferedBoundary_incl_succ
    (P : PeriodicGraph V) (n : ℕ) (v : P.BufferedVertex n) :
    ¬ P.bufferedBoundary (n + 1) (P.bufferedVertexIncl n v) := by
  rintro ⟨w, hvw, hw⟩
  exact hw (P.neighbor_mem_buffered_succ n v.2 hvw)

theorem PeriodicGraph.bufferedBoundary_of_outsideGraph_adj
    (P : PeriodicGraph V) (n : ℕ)
    (psi : ConfigSpace (Sym2 (P.BufferedVertex (n + 1))))
    {x : P.BufferedVertex n} {z : P.BufferedVertex (n + 1)}
    (h : (ocd_outsideGraph (P.bufferedGraph (n + 1))
      (P.bufferedVertexIncl n) (P.bufferedBoundary (n + 1)) psi).Adj
        (P.bufferedVertexIncl n x) z) :
    P.bufferedBoundary n x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hrange⟩ | ⟨_, hbdry, _⟩
  · have hznot : z.1 ∉ P.orbitBox (P.bufferedRadius n) := by
      intro hz
      let zIn : P.BufferedVertex n := ⟨z.1, hz⟩
      have hzEq : P.bufferedVertexIncl n zIn = z := Subtype.ext rfl
      apply hrange
      refine ⟨s(x, zIn), ?_⟩
      rw [ocd_innerEdge_mk, hzEq]
    exact ⟨z.1, hadj, hznot⟩
  · exact (P.not_bufferedBoundary_incl_succ n x hbdry).elim



theorem PeriodicGraph.bufferedInducedWiring_le (P : PeriodicGraph V) (n : ℕ)
    (psi : ConfigSpace (Sym2 (P.BufferedVertex (n + 1)))) :
    ocd_inducedWiring (P.bufferedGraph (n + 1))
        (P.bufferedVertexIncl n) (P.bufferedBoundary (n + 1)) psi
      ≤ StatMech.Lattice.boundaryCliqueGraph (P.bufferedBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : P.bufferedVertexIncl n x ≠ P.bufferedVertexIncl n y :=
      fun h => hne ((P.bufferedVertexIncl n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact P.bufferedBoundary_of_outsideGraph_adj n psi hadj
  · have hreach' := hreach.symm
    have hne' : P.bufferedVertexIncl n y ≠ P.bufferedVertexIncl n x :=
      fun h => hne ((P.bufferedVertexIncl n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact P.bufferedBoundary_of_outsideGraph_adj n psi hadj


theorem PeriodicGraph.freeBuffered_step
    (P : PeriodicGraph V) (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (P.BufferedVertex n)))}
    (hA : IsIncreasing A) :
    (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
        fkProb (P.bufferedGraph n) p q omega) ≤
      ∑ eta, (ocd_innerRestrict (P.bufferedVertexIncl n) ⁻¹' A).indicator
        (fun _ => (1 : ℝ)) eta *
          fkProb (P.bufferedGraph (n + 1)) p q eta := by
  exact bdp_free_inner_dominated_fkProb
    (P.bufferedVertexIncl n).injective (P.bufferedAdjMatch n) hp hp1 hq hA


theorem PeriodicGraph.wiredBuffered_step
    (P : PeriodicGraph V) (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (P.BufferedVertex n)))}
    (hA : IsIncreasing A) :
    (∑ eta, (ocd_innerRestrict (P.bufferedVertexIncl n) ⁻¹' A).indicator
        (fun _ => (1 : ℝ)) eta *
          wiredFkProb (P.bufferedGraph (n + 1))
            (P.bufferedBoundary (n + 1)) p q eta) ≤
      ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
        wiredFkProb (P.bufferedGraph n) (P.bufferedBoundary n) p q omega := by
  have h := ocd_wired_inner_dominated_bcProb
    (P.bufferedVertexIncl n).injective (P.bufferedAdjMatch n)
    (P.bufferedBoundary n) hp hp1 hq
    (fun psi => P.bufferedInducedWiring_le n psi) hA
  simpa only [bcProb_clique_eq_wiredFkProb] using h



variable [Countable V]


noncomputable def PeriodicGraph.freeBufferedMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  P.freeFiniteMeasure (P.bufferedRadius n) hp hp1 hq


noncomputable def PeriodicGraph.wiredBufferedPMF (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 (P.BufferedVertex n))) :=
  wiredFkPMF (P.bufferedGraph n) (P.bufferedBoundary n) hp hp1 hq


noncomputable def PeriodicGraph.wiredBufferedMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  ⟨((P.wiredBufferedPMF n hp hp1 hq).toMeasure).map
      (P.extendEdge (P.bufferedRadius n)),
    MeasureTheory.Measure.isProbabilityMeasure_map
      (P.measurable_extendEdge (P.bufferedRadius n)).aemeasurable⟩


noncomputable def PeriodicGraph.bufferedRestrict (P : PeriodicGraph V) (n : ℕ)
    (omega : ConfigSpace (Sym2 V)) :
    ConfigSpace (Sym2 (P.BufferedVertex n)) :=
  fun e => omega (P.edgeIncl (P.bufferedRadius n) e)

omit [Countable V] in
theorem PeriodicGraph.continuous_bufferedRestrict
    (P : PeriodicGraph V) (n : ℕ) : Continuous (P.bufferedRestrict n) := by
  exact continuous_pi fun e => continuous_apply (P.edgeIncl (P.bufferedRadius n) e)

theorem PeriodicGraph.measurable_bufferedRestrict
    (P : PeriodicGraph V) (n : ℕ) : Measurable (P.bufferedRestrict n) :=
  (P.continuous_bufferedRestrict n).measurable

omit [Countable V] in
theorem PeriodicGraph.monotone_bufferedRestrict
    (P : PeriodicGraph V) (n : ℕ) : Monotone (P.bufferedRestrict n) := by
  intro omega eta home e
  exact home _


noncomputable def PeriodicGraph.bufferedRestrictLE (P : PeriodicGraph V)
    {n m : ℕ} (hnm : n ≤ m)
    (omega : ConfigSpace (Sym2 (P.BufferedVertex m))) :
    ConfigSpace (Sym2 (P.BufferedVertex n)) :=
  fun e => omega (Sym2.map (P.bufferedVertexInclLE hnm) e)

omit [Countable V] in
theorem PeriodicGraph.monotone_bufferedRestrictLE
    (P : PeriodicGraph V) {n m : ℕ} (hnm : n ≤ m) :
    Monotone (P.bufferedRestrictLE hnm) := by
  intro omega eta home e
  exact home _

omit [Countable V] in
theorem PeriodicGraph.edgeIncl_bufferedVertexInclLE
    (P : PeriodicGraph V) {n m : ℕ} (hnm : n ≤ m)
    (e : Sym2 (P.BufferedVertex n)) :
    P.edgeIncl (P.bufferedRadius m)
        (Sym2.map (P.bufferedVertexInclLE hnm) e) =
      P.edgeIncl (P.bufferedRadius n) e := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl

omit [Countable V] in
@[simp] theorem PeriodicGraph.bufferedRestrict_extendEdge_le
    (P : PeriodicGraph V) {n m : ℕ} (hnm : n ≤ m)
    (omega : ConfigSpace (Sym2 (P.BufferedVertex m))) :
    P.bufferedRestrict n (P.extendEdge (P.bufferedRadius m) omega) =
      P.bufferedRestrictLE hnm omega := by
  funext e
  unfold PeriodicGraph.bufferedRestrict PeriodicGraph.bufferedRestrictLE
  rw [← P.edgeIncl_bufferedVertexInclLE hnm e,
    P.extendEdge_edgeIncl]

omit [Countable V] in
theorem PeriodicGraph.bufferedRestrictLE_succ
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    (omega : ConfigSpace (Sym2 (P.BufferedVertex (m + 1)))) :
    P.bufferedRestrictLE (hNm.trans (Nat.le_succ m)) omega =
      P.bufferedRestrictLE hNm
        (ocd_innerRestrict (P.bufferedVertexIncl m) omega) := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y => rfl


def PeriodicGraph.bufferedCylinder (P : PeriodicGraph V) (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    Set (ConfigSpace (Sym2 V)) :=
  P.bufferedRestrict N ⁻¹' S

omit [Countable V] in
theorem PeriodicGraph.bufferedCylinder_isClopen
    (P : PeriodicGraph V) (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    IsClopen (P.bufferedCylinder N S) :=
  IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩
    (P.continuous_bufferedRestrict N)

theorem PeriodicGraph.bufferedCylinder_measurableSet
    (P : PeriodicGraph V) (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    MeasurableSet (P.bufferedCylinder N S) :=
  (P.bufferedCylinder_isClopen N S).isOpen.measurableSet

omit [Countable V] in
theorem PeriodicGraph.bufferedCylinder_isIncreasing
    (P : PeriodicGraph V) (N : ℕ)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    IsIncreasing (P.bufferedCylinder N S) :=
  fun _ _ home hmem => hS (P.monotone_bufferedRestrict N home) hmem

private theorem fkPMF_toMeasure_toReal_generic
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 W))) :
    ((fkPMF G hp hp1 hq).toMeasure S).toReal =
      ∑ omega, S.indicator (fun _ => (1 : ℝ)) omega * fkProb G p q omega := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun a _ => ?_)]
  · apply Finset.sum_congr rfl
    intro omega _
    by_cases homega : omega ∈ S
    · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega,
        fkPMF_apply, ENNReal.toReal_ofReal (fkProb_nonneg G hp hp1 hq omega), one_mul]
    · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]
      simp
  · by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, fkPMF_apply]
      exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem ha]
      simp

private theorem wiredFkPMF_toMeasure_toReal_generic
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (bdry : W → Prop) [DecidablePred bdry]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 W))) :
    ((wiredFkPMF G bdry hp hp1 hq).toMeasure S).toReal =
      ∑ omega, S.indicator (fun _ => (1 : ℝ)) omega *
        wiredFkProb G bdry p q omega := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun a _ => ?_)]
  · apply Finset.sum_congr rfl
    intro omega _
    by_cases homega : omega ∈ S
    · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega,
        wiredFkPMF, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal (wiredFkProb_nonneg G bdry hp hp1 hq omega), one_mul]
    · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]
      simp
  · by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, wiredFkPMF, PMF.ofFintype_apply]
      exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem ha]
      simp

theorem PeriodicGraph.freeBufferedMeasure_real_cylinder
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    (P.freeBufferedMeasure m hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder N S) =
      ∑ omega,
        (P.bufferedRestrictLE hNm ⁻¹' S).indicator (fun _ => (1 : ℝ)) omega *
          fkProb (P.bufferedGraph m) p q omega := by
  have hmap : (P.freeBufferedMeasure m hp hp1 hq : Measure _).real
        (P.bufferedCylinder N S) =
      ((fkPMF (P.bufferedGraph m) hp hp1 hq).toMeasure
        (P.extendEdge (P.bufferedRadius m) ⁻¹' P.bufferedCylinder N S)).toReal := by
    unfold PeriodicGraph.freeBufferedMeasure PeriodicGraph.freeFiniteMeasure
      PeriodicGraph.freeFinitePMF PeriodicGraph.bufferedGraph Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (P.measurable_extendEdge (P.bufferedRadius m))
      (P.bufferedCylinder_measurableSet N S)]
    rfl
  have hpre : P.extendEdge (P.bufferedRadius m) ⁻¹' P.bufferedCylinder N S =
      P.bufferedRestrictLE hNm ⁻¹' S := by
    ext omega
    simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage,
      P.bufferedRestrict_extendEdge_le hNm]
  rw [hmap, hpre]
  exact fkPMF_toMeasure_toReal_generic (P.bufferedGraph m) hp hp1 hq _

theorem PeriodicGraph.wiredBufferedMeasure_real_cylinder
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    (P.wiredBufferedMeasure m hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder N S) =
      ∑ omega,
        (P.bufferedRestrictLE hNm ⁻¹' S).indicator (fun _ => (1 : ℝ)) omega *
          wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega := by
  have hmap : (P.wiredBufferedMeasure m hp hp1 hq : Measure _).real
        (P.bufferedCylinder N S) =
      ((P.wiredBufferedPMF m hp hp1 hq).toMeasure
        (P.extendEdge (P.bufferedRadius m) ⁻¹' P.bufferedCylinder N S)).toReal := by
    unfold PeriodicGraph.wiredBufferedMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (P.measurable_extendEdge (P.bufferedRadius m))
      (P.bufferedCylinder_measurableSet N S)]
  have hpre : P.extendEdge (P.bufferedRadius m) ⁻¹' P.bufferedCylinder N S =
      P.bufferedRestrictLE hNm ⁻¹' S := by
    ext omega
    simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage,
      P.bufferedRestrict_extendEdge_le hNm]
  rw [hmap, hpre]
  exact wiredFkPMF_toMeasure_toReal_generic (P.bufferedGraph m)
    (P.bufferedBoundary m) hp hp1 hq _

theorem PeriodicGraph.freeBufferedMeasure_step_cylinder
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) ≤
      (P.freeBufferedMeasure (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  rw [P.freeBufferedMeasure_real_cylinder hNm hp hp1 (zero_lt_one.trans_le hq),
    P.freeBufferedMeasure_real_cylinder (hNm.trans (Nat.le_succ m))
      hp hp1 (zero_lt_one.trans_le hq)]
  let A := P.bufferedRestrictLE hNm ⁻¹' S
  have hA : IsIncreasing A := fun _ _ home hmem =>
    hS (P.monotone_bufferedRestrictLE hNm home) hmem
  have hstep := P.freeBuffered_step m hp hp1 hq hA
  have hpre : ocd_innerRestrict (P.bufferedVertexIncl m) ⁻¹' A =
      P.bufferedRestrictLE (hNm.trans (Nat.le_succ m)) ⁻¹' S := by
    ext omega
    simp only [A, Set.mem_preimage, P.bufferedRestrictLE_succ hNm]
  rwa [hpre] at hstep

theorem PeriodicGraph.wiredBufferedMeasure_step_cylinder
    (P : PeriodicGraph V) {N m : ℕ} (hNm : N ≤ m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.wiredBufferedMeasure (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) ≤
      (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  rw [P.wiredBufferedMeasure_real_cylinder (hNm.trans (Nat.le_succ m))
      hp hp1 (zero_lt_one.trans_le hq),
    P.wiredBufferedMeasure_real_cylinder hNm hp hp1 (zero_lt_one.trans_le hq)]
  let A := P.bufferedRestrictLE hNm ⁻¹' S
  have hA : IsIncreasing A := fun _ _ home hmem =>
    hS (P.monotone_bufferedRestrictLE hNm home) hmem
  have hstep := P.wiredBuffered_step m hp hp1 hq hA
  have hpre : ocd_innerRestrict (P.bufferedVertexIncl m) ⁻¹' A =
      P.bufferedRestrictLE (hNm.trans (Nat.le_succ m)) ⁻¹' S := by
    ext omega
    simp only [A, Set.mem_preimage, P.bufferedRestrictLE_succ hNm]
  rwa [hpre] at hstep




noncomputable def PeriodicGraph.freeBufferedInfiniteVolume
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  (prokhorov_seq_compact (fun n => P.freeBufferedMeasure n hp hp1 hq)).choose

theorem PeriodicGraph.freeBufferedInfiniteVolume_isLimit
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.freeBufferedMeasure (phi n) hp hp1 hq)
        (P.freeBufferedInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (prokhorov_seq_compact
      (fun n => P.freeBufferedMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩


noncomputable def PeriodicGraph.wiredBufferedInfiniteVolume
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  (prokhorov_seq_compact (fun n => P.wiredBufferedMeasure n hp hp1 hq)).choose

theorem PeriodicGraph.wiredBufferedInfiniteVolume_isLimit
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.wiredBufferedMeasure (phi n) hp hp1 hq)
        (P.wiredBufferedInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (prokhorov_seq_compact
      (fun n => P.wiredBufferedMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩


theorem PeriodicGraph.freeBufferedMeasure_tendsto_cylinder
    (P : PeriodicGraph V) (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    Tendsto
      (fun m => (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S)) atTop
      (nhds ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S))) := by
  set f := fun m => (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) with hf
  have hmono : Monotone (fun k => f (N + k)) := by
    apply monotone_nat_of_le_succ
    intro k
    simpa [f, Nat.add_assoc] using
      P.freeBufferedMeasure_step_cylinder (Nat.le_add_right N k) hp hp1 hq hS
  have hbdd : BddAbove (Set.range fun k => f (N + k)) :=
    ⟨1, by rintro x ⟨k, rfl⟩; exact measureReal_le_one⟩
  set L := ⨆ k, f (N + k) with hL
  have hshift : Tendsto (fun k => f (N + k)) atTop (nhds L) := by
    rw [hL]
    exact tendsto_atTop_ciSup hmono hbdd
  have hfull : Tendsto f atTop (nhds L) := by
    have hk : Tendsto (fun k => f (k + N)) atTop (nhds L) := by
      simpa [Nat.add_comm] using hshift
    exact (Filter.tendsto_add_atTop_iff_nat N).mp hk
  obtain ⟨phi, hphi, hconv⟩ :=
    P.freeBufferedInfiniteVolume_isLimit hp hp1 (zero_lt_one.trans_le hq)
  have hport := hconv.tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hsub := hfull.comp hphi.tendsto_atTop
  have heq : L =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) :=
    tendsto_nhds_unique hsub hport
  rwa [heq] at hfull


theorem PeriodicGraph.wiredBufferedMeasure_tendsto_cylinder
    (P : PeriodicGraph V) (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    Tendsto
      (fun m => (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S)) atTop
      (nhds ((P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S))) := by
  set f := fun m => (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) with hf
  have hanti : Antitone (fun k => f (N + k)) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa [f, Nat.add_assoc] using
      P.wiredBufferedMeasure_step_cylinder (Nat.le_add_right N k) hp hp1 hq hS
  have hbdd : BddBelow (Set.range fun k => f (N + k)) :=
    ⟨0, by rintro x ⟨k, rfl⟩; exact measureReal_nonneg⟩
  set L := ⨅ k, f (N + k) with hL
  have hshift : Tendsto (fun k => f (N + k)) atTop (nhds L) := by
    rw [hL]
    exact tendsto_atTop_ciInf hanti hbdd
  have hfull : Tendsto f atTop (nhds L) := by
    have hk : Tendsto (fun k => f (k + N)) atTop (nhds L) := by
      simpa [Nat.add_comm] using hshift
    exact (Filter.tendsto_add_atTop_iff_nat N).mp hk
  obtain ⟨phi, hphi, hconv⟩ :=
    P.wiredBufferedInfiniteVolume_isLimit hp hp1 (zero_lt_one.trans_le hq)
  have hport := hconv.tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hsub := hfull.comp hphi.tendsto_atTop
  have heq : L =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) :=
    tendsto_nhds_unique hsub hport
  rwa [heq] at hfull



theorem PeriodicGraph.freeBuffered_subseq_cylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (N : ℕ) {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  have hport := hconv.tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hsub := (P.freeBufferedMeasure_tendsto_cylinder N hp hp1 hq hS).comp
    hphi.tendsto_atTop
  exact tendsto_nhds_unique hport hsub

theorem PeriodicGraph.wiredBuffered_subseq_cylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (N : ℕ) {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  have hport := hconv.tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hsub := (P.wiredBufferedMeasure_tendsto_cylinder N hp hp1 hq hS).comp
    hphi.tendsto_atTop
  exact tendsto_nhds_unique hport hsub


def PeriodicGraph.edgeVertexFinset (T : Finset (Sym2 V)) : Finset V :=
  T.biUnion Sym2.toFinset

omit [Countable V] in
theorem PeriodicGraph.exists_bufferedLevel_edges (P : PeriodicGraph V)
    (T : Finset (Sym2 V)) :
    ∃ N, ∀ e ∈ T, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N)) := by
  classical
  obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (PeriodicGraph.edgeVertexFinset T)
  refine ⟨N, ?_⟩
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxmem : x ∈ PeriodicGraph.edgeVertexFinset T := by
        simp only [PeriodicGraph.edgeVertexFinset, Finset.mem_biUnion]
        exact ⟨s(x, y), he, by simp⟩
      have hymem : y ∈ PeriodicGraph.edgeVertexFinset T := by
        simp only [PeriodicGraph.edgeVertexFinset, Finset.mem_biUnion]
        exact ⟨s(x, y), he, by simp⟩
      let xb : P.BufferedVertex N :=
        ⟨x, P.orbitBox_mono (P.id_le_bufferedRadius N) (hN x hxmem)⟩
      let yb : P.BufferedVertex N :=
        ⟨y, P.orbitBox_mono (P.id_le_bufferedRadius N) (hN y hymem)⟩
      exact ⟨s(xb, yb), rfl⟩

private theorem PeriodicGraph.bufferedCylinder_real_eq_signedSum
    (P : PeriodicGraph V)
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 V))) (N : ℕ)
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N))))
    {I : Type*} (t : Finset I) (c : I → ℝ)
    (A : I → Set (ConfigSpace (Sym2 (P.BufferedVertex N))))
    (hexp : S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ) =
      ∑ i ∈ t, c i • (A i).indicator 1) :
    (mu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      ∑ i ∈ t, c i *
        (mu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N (A i)) := by
  have hpoint : (P.bufferedCylinder N S).indicator
        (1 : ConfigSpace (Sym2 V) → ℝ) =
      ∑ i ∈ t, c i • (P.bufferedCylinder N (A i)).indicator 1 := by
    funext omega
    have h := congrFun hexp (P.bufferedRestrict N omega)
    simpa only [PeriodicGraph.bufferedCylinder, Set.indicator_apply,
      Set.mem_preimage, Finset.sum_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul] using h
  calc
    (mu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
        ∫ omega, (P.bufferedCylinder N S).indicator (fun _ => (1 : ℝ)) omega ∂mu := by
          rw [integral_indicator_const (1 : ℝ)
            (P.bufferedCylinder_measurableSet N S)]
          simp
    _ = ∫ omega, (∑ i ∈ t,
          c i • (P.bufferedCylinder N (A i)).indicator
            (1 : ConfigSpace (Sym2 V) → ℝ)) omega ∂mu := by
          apply integral_congr_ae
          filter_upwards with omega
          simpa using congrFun hpoint omega
    _ = ∑ i ∈ t, c i *
          (mu : Measure (ConfigSpace (Sym2 V))).real
            (P.bufferedCylinder N (A i)) := by
          simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [integral_const_mul]
            congr 1
            simpa using (integral_indicator_const (μ := (mu : Measure _)) (1 : ℝ)
              (P.bufferedCylinder_measurableSet N (A i)))
          · intro i hi
            exact ((integrable_const (1 : ℝ)).indicator
              (P.bufferedCylinder_measurableSet N (A i))).const_mul _

theorem PeriodicGraph.freeBuffered_subseq_allCylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (N : ℕ) (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  classical
  have hdep : DependsOn
      (S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ))
      (Finset.univ : Finset (Sym2 (P.BufferedVertex N))) := by
    intro omega eta heq
    congr 1
    funext e
    exact heq e (by simp)
  have hsigned := indicator_signedIncreasingCombo_of_dependsOn S Finset.univ hdep
  obtain ⟨I, t, c, A, hA, hexp⟩ :=
    (signedIncreasingCombo_iff
      (S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ))).mp hsigned
  rw [P.bufferedCylinder_real_eq_signedSum nu N S t c A hexp,
    P.bufferedCylinder_real_eq_signedSum
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) N S t c A hexp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [P.freeBuffered_subseq_cylinder_eq hp hp1 hq nu phi hphi hconv N (hA i hi)]

theorem PeriodicGraph.wiredBuffered_subseq_allCylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (N : ℕ) (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  classical
  have hdep : DependsOn
      (S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ))
      (Finset.univ : Finset (Sym2 (P.BufferedVertex N))) := by
    intro omega eta heq
    congr 1
    funext e
    exact heq e (by simp)
  have hsigned := indicator_signedIncreasingCombo_of_dependsOn S Finset.univ hdep
  obtain ⟨I, t, c, A, hA, hexp⟩ :=
    (signedIncreasingCombo_iff
      (S.indicator (1 : ConfigSpace (Sym2 (P.BufferedVertex N)) → ℝ))).mp hsigned
  rw [P.bufferedCylinder_real_eq_signedSum nu N S t c A hexp,
    P.bufferedCylinder_real_eq_signedSum
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) N S t c A hexp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [P.wiredBuffered_subseq_cylinder_eq hp hp1 hq nu phi hphi hconv N (hA i hi)]

omit [Countable V] in


theorem PeriodicGraph.fullCylinder_eq_bufferedCylinder
    (P : PeriodicGraph V) (N : ℕ) (s : Finset (Sym2 V))
    (S : Set (∀ _i : s, Bool))
    (hs : ∀ e ∈ s, e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
    cylinder s S = P.bufferedCylinder N
      (P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder s S) := by
  ext omega
  simp only [PeriodicGraph.bufferedCylinder, Set.mem_preimage]
  have hrestr : s.restrict
      (P.extendEdge (P.bufferedRadius N) (P.bufferedRestrict N omega)) =
      s.restrict omega := by
    funext e
    obtain ⟨eb, heb⟩ := hs e.1 e.2
    change P.extendEdge (P.bufferedRadius N) (P.bufferedRestrict N omega) e.1 = omega e.1
    rw [← heb, P.extendEdge_edgeIncl]
    rfl
  simp only [mem_cylinder, hrestr]

theorem PeriodicGraph.freeBuffered_subseq_finiteCylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (s : Finset (Sym2 V)) (S : Set (∀ _i : s, Bool)) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (cylinder s S) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S) := by
  obtain ⟨N, hs⟩ := P.exists_bufferedLevel_edges s
  rw [P.fullCylinder_eq_bufferedCylinder N s S hs]
  exact P.freeBuffered_subseq_allCylinder_eq hp hp1 hq nu phi hphi hconv N _

theorem PeriodicGraph.wiredBuffered_subseq_finiteCylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (s : Finset (Sym2 V)) (S : Set (∀ _i : s, Bool)) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (cylinder s S) =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S) := by
  obtain ⟨N, hs⟩ := P.exists_bufferedLevel_edges s
  rw [P.fullCylinder_eq_bufferedCylinder N s S hs]
  exact P.wiredBuffered_subseq_allCylinder_eq hp hp1 hq nu phi hphi hconv N _

private theorem probabilityMeasure_eq_of_finiteCylinder_real_eq
    {E : Type*} [Countable E]
    (mu nu : ProbabilityMeasure (ConfigSpace E))
    (h : ∀ (s : Finset E) (S : Set (∀ _i : s, Bool)),
      (mu : Measure (ConfigSpace E)).real (cylinder s S) =
        (nu : Measure (ConfigSpace E)).real (cylinder s S)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (measurableCylinders (fun _ : E => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    rw [mem_measurableCylinders] at hC
    obtain ⟨s, S, hS, rfl⟩ := hC
    have hreal := h s S
    unfold Measure.real at hreal
    exact (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (mu : Measure (ConfigSpace E)) (cylinder s S))
      (measure_ne_top (nu : Measure (ConfigSpace E)) (cylinder s S))).mp hreal
  · rw [measure_univ, measure_univ]



theorem PeriodicGraph.freeBuffered_subseq_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu) :
    nu = P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) := by
  apply probabilityMeasure_eq_of_finiteCylinder_real_eq
  exact P.freeBuffered_subseq_finiteCylinder_eq hp hp1 hq nu phi hphi hconv



theorem PeriodicGraph.wiredBuffered_subseq_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu) :
    nu = P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) := by
  apply probabilityMeasure_eq_of_finiteCylinder_real_eq
  exact P.wiredBuffered_subseq_finiteCylinder_eq hp hp1 hq nu phi hphi hconv


theorem PeriodicGraph.freeBufferedMeasure_weakConverges
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    WeakConvergesTo
      (fun n => P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq))
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) := by
  rw [WeakConvergesTo]
  apply tendsto_nhds_of_unique_mapClusterPt
  intro nu hnu
  obtain ⟨phi, hphi, hconv⟩ := hnu.tendsto_subseq
  apply P.freeBuffered_subseq_eq hp hp1 hq nu phi hphi
  simpa [Function.comp_def] using hconv


theorem PeriodicGraph.wiredBufferedMeasure_weakConverges
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    WeakConvergesTo
      (fun n => P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq))
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)) := by
  rw [WeakConvergesTo]
  apply tendsto_nhds_of_unique_mapClusterPt
  intro nu hnu
  obtain ⟨phi, hphi, hconv⟩ := hnu.tendsto_subseq
  apply P.wiredBuffered_subseq_eq hp hp1 hq nu phi hphi
  simpa [Function.comp_def] using hconv


theorem PeriodicGraph.freeBufferedMeasure_tendsto_finiteCylinder
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (s : Finset (Sym2 V)) (S : Set (∀ _i : s, Bool)) :
    Tendsto
      (fun n => (P.freeBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S)) atTop
      (nhds ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S))) :=
  (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (isClopen_cylinderEvent s S)


theorem PeriodicGraph.wiredBufferedMeasure_tendsto_finiteCylinder
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (s : Finset (Sym2 V)) (S : Set (∀ _i : s, Bool)) :
    Tendsto
      (fun n => (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S)) atTop
      (nhds ((P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (cylinder s S))) :=
  (P.wiredBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (isClopen_cylinderEvent s S)

end PeriodicPlanar
end FK
end StatMech
