/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.OSSS.FKSharpnessWeightedSelectedLaws
import Code.FK.FKGeneralQTranslation

open MeasureTheory Set Filter Topology
open scoped BigOperators Classical

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedWeakLimit

open Lattice FK Percolation
open RevealmentConstruction WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre
open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedCoherentLimit FKSharpnessWeightedSelectedLaws

variable {d : Nat}


theorem cdc_multiOpenEvent_isClopen (s : Finset (Sym2 (Site d))) :
    IsClopen (cdc_multiOpenEvent s) := by
  have heq : cdc_multiOpenEvent s = cylinder s
      {eta : s -> Bool | forall e, eta e = true} := by
    ext omega
    simp [cdc_multiOpenEvent, cylinder, Finset.restrict]
  rw [heq]
  exact isClopen_cylinderEvent s _


theorem edgeIncl_mem_lattice_edgeSet
    (N : Nat) (e : Sym2 (boxVerts d N))
    (he : e ∈ (boxGraph d N).edgeFinset) :
    edgeIncl d N e ∈ (hypercubicLattice d).edgeSet := by
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ x y => exact he



theorem box_edges_of_image_lattice_edges
    (N : Nat) (t : Finset (Sym2 (boxVerts d N)))
    (ht : forall e, e ∈ t.image (edgeIncl d N) ->
      e ∈ (hypercubicLattice d).edgeSet) :
    t ⊆ (boxGraph d N).edgeFinset := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset]
  have hamb := ht (edgeIncl d N e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  induction e using Sym2.ind with
  | _ x y => exact hamb



theorem liftActive_mem_multiOpen_iff
    (d N R : Nat) (hNR : N <= R)
    (t : Finset (Sym2 (boxVerts d N)))
    (ht : t ⊆ (boxGraph d N).edgeFinset)
    (rho : ConfigSpace (Sym2 (boxVerts d R))) :
    liftCfg (boxActiveEdge d R) (restrictActive (boxGraph d R) rho) ∈
        cdc_multiOpenEvent (t.image (edgeIncl d N)) <->
      ocd_innerRestrict (flc_incl (box_mono d hNR)) rho ∈
        cdc_boxMultiOpenEvent N t := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict]
  simp only [Set.mem_preimage, cdc_boxMultiOpenEvent, Set.mem_setOf_eq]
  have hrestrict :
      ocd_innerRestrict (flc_incl (box_mono d hNR)) rho =
        boxRestrictLE d hNR rho := by
    funext e
    simp [ocd_innerRestrict, ocd_innerEdge, flc_incl, boxRestrictLE,
      innerEdgeLE, boxVertInclLE]
  rw [hrestrict]
  constructor <;> intro h e he
  · have hh := h e he
    rw [boxRestrict_liftActive_eq_on_inner_edges d hNR rho e (ht he)] at hh
    exact hh
  · have hh := h e he
    rw [boxRestrict_liftActive_eq_on_inner_edges d hNR rho e (ht he)]
    exact hh



theorem weightedPhaseFiniteMeasure_multiOpen_eq
    (d N R : Nat) (hNR : N <= R) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta)
    (t : Finset (Sym2 (boxVerts d N)))
    (ht : t ⊆ (boxGraph d N).edgeFinset) :
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta hq hbeta :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))) =
      ∑ rho : ConfigSpace (Sym2 (boxVerts d R)),
        (ocd_innerRestrict (flc_incl (box_mono d hNR)) ⁻¹'
          cdc_boxMultiOpenEvent N t).indicator (fun _ => (1 : Real)) rho *
        bcProbW (boxGraph d R) (wiredBoxBoundaryGraph d R)
          (betaParams (phaseBoxCoupling phaseJ a R) beta) q rho := by
  rw [weightedPhaseFiniteMeasure_real_eq d R phaseJ a hJ q beta hq hbeta
    (cdc_multiOpenEvent (t.image (edgeIncl d N)))
    (cdc_multiOpenEvent_measurable _)]
  change activeBCMean (boxGraph d R) (wiredBoxBoundaryGraph d R)
      (betaParams (phaseBoxCoupling phaseJ a R) beta) q
      (fun omega => (liftCfg (boxActiveEdge d R) ⁻¹'
        cdc_multiOpenEvent (t.image (edgeIncl d N))).indicator
          (fun _ => (1 : Real)) omega) = _
  rw [activeBCMean_eq_bcProbW_lift]
  · apply Finset.sum_congr rfl
    intro rho _
    congr 1
    by_cases hmem : rho ∈ ocd_innerRestrict
        (flc_incl (box_mono d hNR)) ⁻¹' cdc_boxMultiOpenEvent N t
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem]
      exact (liftActive_mem_multiOpen_iff d N R hNR t ht rho).mpr hmem
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem]
      intro hlift
      exact hmem ((liftActive_mem_multiOpen_iff d N R hNR t ht rho).mp hlift)
  · exact betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  · exact betaParams_lt_one _ beta
  · exact hq



theorem weightedPhaseFiniteMeasure_multiOpen_mono
    (d N r R : Nat) (hN : 1 <= N) (hNr : N <= r) (hrR : r < R)
    {P : Type*} (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (t : Finset (Sym2 (boxVerts d N)))
    (ht : t ⊆ (boxGraph d N).edgeFinset) :
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))) <=
      ((weightedPhaseFiniteMeasure d r phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [weightedPhaseFiniteMeasure_multiOpen_eq d N R
      (hNr.trans (Nat.le_of_lt hrR)) phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta t ht,
    weightedPhaseFiniteMeasure_multiOpen_eq d N r hNr phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta t ht]
  let iotaNr := flc_incl (box_mono d hNr)
  let A : Set (ConfigSpace (Sym2 (boxVerts d r))) :=
    ocd_innerRestrict iotaNr ⁻¹' cdc_boxMultiOpenEvent N t
  have hA : IsIncreasing A := by
    intro omega eta homega hmem e he
    have hcoord := homega (innerEdgeLE d hNr e)
    have hm : omega (innerEdgeLE d hNr e) = true := by
      simpa [A, iotaNr, ocd_innerRestrict, ocd_innerEdge, flc_incl,
        innerEdgeLE, boxVertInclLE] using hmem e he
    rw [hm] at hcoord
    simpa [A, iotaNr, ocd_innerRestrict, ocd_innerEdge, flc_incl,
      innerEdgeLE, boxVertInclLE] using (le_antisymm (by simp) hcoord)
  have hpre :
      ocd_innerRestrict (flc_incl (box_mono d (Nat.le_of_lt hrR))) ⁻¹' A =
        ocd_innerRestrict
          (flc_incl (box_mono d (hNr.trans (Nat.le_of_lt hrR)))) ⁻¹'
            cdc_boxMultiOpenEvent N t := by
    ext rho
    simp only [A, Set.mem_preimage]
    change boxRestrictLE d hNr
        (ocd_innerRestrict
          (flc_incl (box_mono d (Nat.le_of_lt hrR))) rho) ∈
          cdc_boxMultiOpenEvent N t <->
      boxRestrictLE d (hNr.trans (Nat.le_of_lt hrR)) rho ∈
        cdc_boxMultiOpenEvent N t
    rw [ocd_innerRestrict_box_comp d hNr (Nat.le_of_lt hrR) rho]
  rw [← hpre]
  exact weighted_boxEvent_domain_dominated d r R (hN.trans hNr) hrR
    (phaseJ a) hJ beta q hbeta hq hA



theorem weightedPhaseFiniteMeasure_multiOpen_tendsto
    (d N : Nat) (hN : 1 <= N) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (t : Finset (Sym2 (boxVerts d N)))
    (ht : t ⊆ (boxGraph d N).edgeFinset) :
    Tendsto
      (fun R => ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))))
      atTop
      (nhds (((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  let mass := fun R =>
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
        (cdc_multiOpenEvent (t.image (edgeIncl d N)))
  have hanti : Antitone (fun j => mass (N + j)) := by
    apply antitone_nat_of_succ_le
    intro j
    exact weightedPhaseFiniteMeasure_multiOpen_mono d N (N + j) (N + (j + 1))
      hN (Nat.le_add_right N j) (by omega) phaseJ a hJ q beta hq hbeta t ht
  have hbdd : BddBelow (Set.range (fun j => mass (N + j))) :=
    ⟨0, by rintro x ⟨j, rfl⟩; exact measureReal_nonneg⟩
  obtain ⟨phi, hphi, hconv⟩ := weightedPhaseInfiniteVolume_isLimit
    d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
  have hphitop : Tendsto phi atTop atTop := hphi.tendsto_atTop
  obtain ⟨m0, hm0⟩ := (hphitop.eventually_ge_atTop N).exists_forall_of_atTop
  have hshift : Tendsto (fun j => mass (N + j)) atTop
      (nhds (((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
    refine tendsto_of_antitone_of_subseq
      (φ := fun m => phi (m + m0) - N) ?_ hanti hbdd ?_
    · intro i j hij
      have hi : N <= phi (i + m0) := hm0 (i + m0) (by omega)
      have hj : N <= phi (j + m0) := hm0 (j + m0) (by omega)
      have hlt : phi (i + m0) < phi (j + m0) := hphi (by omega)
      change phi (i + m0) - N < phi (j + m0) - N
      omega
    · have hport := (hconv.tendsto_real_of_isClopen
        (cdc_multiOpenEvent_isClopen (t.image (edgeIncl d N)))).comp
          (tendsto_add_atTop_nat m0)
      refine hport.congr (fun m => ?_)
      have hge : N <= phi (m + m0) := hm0 (m + m0) (by omega)
      change mass (phi (m + m0)) = mass (N + (phi (m + m0) - N))
      rw [show N + (phi (m + m0) - N) = phi (m + m0) by omega]
  have hcomm : (fun j => mass (j + N)) = (fun j => mass (N + j)) := by
    funext j
    rw [Nat.add_comm]
  apply (tendsto_add_atTop_iff_nat N).mp
  rw [hcomm]
  exact hshift



theorem weightedPhaseFiniteMeasure_nonLattice_multiOpen_zero
    (d n : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta)
    (T : Finset (Sym2 (Site d))) (e : Sym2 (Site d))
    (heT : e ∈ T) (he : e ∉ (hypercubicLattice d).edgeSet) :
    ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta hq hbeta :
        ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent T) = 0 := by
  rw [weightedPhaseFiniteMeasure_real_eq d n phaseJ a hJ q beta hq hbeta
    (cdc_multiOpenEvent T) (cdc_multiOpenEvent_measurable T)]
  apply Finset.sum_eq_zero
  intro omega _
  rw [Set.indicator_of_notMem, zero_mul]
  intro hopen
  have heopen : liftCfg (boxActiveEdge d n) omega e = true := hopen e heT
  unfold liftCfg at heopen
  split at heopen
  · next hrep =>
      obtain ⟨f, hf⟩ := hrep
      have hfedge := edgeIncl_mem_lattice_edgeSet (d := d) n f.1 (by
        rw [SimpleGraph.mem_edgeFinset]
        exact f.2)
      exact he (hf ▸ hfedge)
  · simp at heopen



theorem weightedPhaseInfiniteVolume_nonLattice_multiOpen_zero
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta)
    (T : Finset (Sym2 (Site d))) (e : Sym2 (Site d))
    (heT : e ∈ T) (he : e ∉ (hypercubicLattice d).edgeSet) :
    ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta hq hbeta :
        ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent T) = 0 := by
  obtain ⟨phi, _, hconv⟩ := weightedPhaseInfiniteVolume_isLimit
    d phaseJ a hJ q beta hq hbeta
  have hport := hconv.tendsto_real_of_isClopen (cdc_multiOpenEvent_isClopen T)
  have hzero : Tendsto
      (fun k => ((weightedPhaseFiniteMeasure d (phi k) phaseJ a hJ q beta
        hq hbeta : ProbabilityMeasure _) : Measure _).real (cdc_multiOpenEvent T))
      atTop (nhds 0) := tendsto_const_nhds.congr' <|
        Filter.Eventually.of_forall fun k =>
          weightedPhaseFiniteMeasure_nonLattice_multiOpen_zero
            d (phi k) phaseJ a hJ q beta hq hbeta T e heT he |>.symm
  exact tendsto_nhds_unique hport hzero



theorem lattice_finset_in_positive_box
    (T : Finset (Sym2 (Site d)))
    (hT : forall e, e ∈ T -> e ∈ (hypercubicLattice d).edgeSet) :
    exists N : Nat, 1 <= N ∧
      exists t : Finset (Sym2 (boxVerts d N)),
        t ⊆ (boxGraph d N).edgeFinset ∧
          T = t.image (edgeIncl d N) := by
  obtain ⟨M, t, hMt⟩ := cdc_finset_in_box T
  let N := max 1 M
  let tN : Finset (Sym2 (boxVerts d N)) :=
    t.image (innerEdgeLE d (le_max_right 1 M))
  have hrep : T = tN.image (edgeIncl d N) := by
    rw [hMt]
    exact (plc_relift_image M N (le_max_right 1 M) t).symm
  have htN : tN ⊆ (boxGraph d N).edgeFinset :=
    box_edges_of_image_lattice_edges (d := d) N tN fun e he =>
      hT e (by rw [hrep]; exact he)
  exact ⟨N, le_max_left 1 M, tN, htN, hrep⟩




theorem weightedPhaseFiniteMeasure_tendsto_selected
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    WeakConvergesTo
      (fun n => weightedPhaseFiniteMeasure d n phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta)
      (weightedPhaseInfiniteVolume d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta) := by
  rw [WeakConvergesTo]
  apply tendsto_nhds_of_unique_mapClusterPt
  intro xi hxi
  obtain ⟨psi, hpsi, hconv⟩ := hxi.tendsto_subseq
  let nu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
    weightedPhaseInfiniteVolume d phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta
  change xi = nu
  apply ProbabilityMeasure.toMeasure_injective
  apply fkgqt_measure_eq_of_multiOpen_eq
  intro T
  change (xi : Measure _) (cdc_multiOpenEvent T) =
    (nu : Measure _) (cdc_multiOpenEvent T)
  suffices hreal : (xi : Measure _).real (cdc_multiOpenEvent T) =
      (nu : Measure _).real (cdc_multiOpenEvent T) by
    unfold Measure.real at hreal
    let mux : Measure (ConfigSpace (Sym2 (Site d))) := xi
    let munu : Measure (ConfigSpace (Sym2 (Site d))) := nu
    let x := mux (cdc_multiOpenEvent T)
    let y := munu (cdc_multiOpenEvent T)
    change x = y
    change x.toReal = y.toReal at hreal
    have hx : x ≠ ⊤ := by
      dsimp [x]
      exact measure_ne_top mux _
    have hy : y ≠ ⊤ := by
      dsimp [y]
      exact measure_ne_top munu _
    exact (ENNReal.toReal_eq_toReal_iff' hx hy).mp hreal
  change (xi : Measure _).real (cdc_multiOpenEvent T) =
    (nu : Measure _).real (cdc_multiOpenEvent T)
  by_cases hT : forall e, e ∈ T -> e ∈ (hypercubicLattice d).edgeSet
  · obtain ⟨N, hN, t, ht, hrep⟩ :=
      lattice_finset_in_positive_box (d := d) T hT
    rw [hrep]
    have hfull := weightedPhaseFiniteMeasure_multiOpen_tendsto
      d N hN phaseJ a hJ q beta hq hbeta t ht
    have hsub := hfull.comp hpsi.tendsto_atTop
    have hw : WeakConvergesTo
        ((fun n => weightedPhaseFiniteMeasure d n phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta) ∘ psi) xi := hconv
    have hport := hw.tendsto_real_of_isClopen
      (cdc_multiOpenEvent_isClopen (t.image (edgeIncl d N)))
    simpa [nu] using tendsto_nhds_unique hport hsub
  · push Not at hT
    obtain ⟨e, heT, he⟩ := hT
    have hselected := weightedPhaseInfiniteVolume_nonLattice_multiOpen_zero
      d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta T e heT he
    have hw : WeakConvergesTo
        ((fun n => weightedPhaseFiniteMeasure d n phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta) ∘ psi) xi := hconv
    have hport := hw.tendsto_real_of_isClopen (cdc_multiOpenEvent_isClopen T)
    have hzero : Tendsto
        (fun k => ((weightedPhaseFiniteMeasure d (psi k) phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
            (cdc_multiOpenEvent T)) atTop (nhds 0) :=
      tendsto_const_nhds.congr' <| Filter.Eventually.of_forall fun k =>
        weightedPhaseFiniteMeasure_nonLattice_multiOpen_zero d (psi k)
          phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta T e heT he |>.symm
    rw [show (nu : Measure _).real (cdc_multiOpenEvent T) = 0 by
      simpa [nu] using hselected]
    exact tendsto_nhds_unique hport hzero



theorem weightedPhaseFiniteMeasure_weakLimit_unique
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hmu : WeakConvergesTo
      (fun n => weightedPhaseFiniteMeasure d n phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta) mu) :
    mu = weightedPhaseInfiniteVolume d phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta := by
  exact tendsto_nhds_unique hmu
    (weightedPhaseFiniteMeasure_tendsto_selected
      d phaseJ a hJ q beta hq hbeta)

end FKSharpnessWeightedWeakLimit
end OSSS
end StatMech
