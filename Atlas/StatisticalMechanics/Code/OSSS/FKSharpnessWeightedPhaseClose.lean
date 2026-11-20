/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.OSSS.FKSharpnessWeightedWeakLimit
import Code.OSSS.FKSharpnessWeightedPhaseTransport

open MeasureTheory Set Filter Topology
open scoped BigOperators Classical

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedPhaseClose

open Lattice FK Percolation
open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedCoherentLimit FKSharpnessWeightedSelectedLaws
open FKSharpnessWeightedWeakLimit FKSharpnessWeightedPhaseTransport
open FKSharpnessWeightedDomain FKSharpnessWeightedPeriodicRepair

variable {d : Nat}



noncomputable def weightedTransBoxMass
    (K : Sym2 (Site d) -> Real) (v : Site d) (N : Nat)
    (t : Finset (Sym2 (boxVerts d N))) (q beta : Real)
    (m : Nat) (hNm : N <= m) : Real :=
  med_multiMassProb
    (bcProbW (fvs_transBoxGraph d m v)
      (boundaryCliqueGraph (fvs_transBoxBoundary d m v))
      (betaParams (transBoxCoupling K m v) beta) q)
    (flc_transEdges v N t m hNm)



theorem weightedPhaseFiniteMeasure_relabel
    {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (x y : Site d) (N m : Nat) (hNm : N <= m)
    (t : Finset (Sym2 (boxVerts d N)))
    (ht : t ⊆ (boxGraph d N).edgeFinset)
    (hphaseJ : forall a e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    ((weightedPhaseFiniteMeasure d m phaseJ (phase y)
        (hphaseJ (phase y)) q beta hq hbeta : ProbabilityMeasure _) :
        Measure _).real
      (cdc_multiOpenEvent (t.image (edgeIncl d N))) =
    weightedTransBoxMass (phaseJ (phase x)) (y - x) N t q beta m hNm := by
  rw [weightedPhaseFiniteMeasure_multiOpen_eq d N m hNm phaseJ
    (phase y) (hphaseJ (phase y)) q beta hq hbeta t ht]
  let sigma := fvs_transEquiv d m (y - x)
  let event : Set (ConfigSpace (Sym2 (boxVerts d m))) :=
    med_genericMultiOpenEvent (t.image (innerEdgeLE d hNm))
  have hevent :
      ocd_innerRestrict (flc_incl (box_mono d hNm)) ⁻¹'
          cdc_boxMultiOpenEvent N t = event := by
    ext omega
    simp only [event, Set.mem_preimage, cdc_boxMultiOpenEvent,
      med_genericMultiOpenEvent, Set.mem_setOf_eq, Finset.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro h e he
      simpa [ocd_innerRestrict, ocd_innerEdge, flc_incl, innerEdgeLE,
        boxVertInclLE] using h e he
    · intro h e he
      simpa [ocd_innerRestrict, ocd_innerEdge, flc_incl, innerEdgeLE,
        boxVertInclLE] using h e he
  rw [hevent]
  have hparam : forall e : Sym2 (boxVerts d m),
      betaParams (transBoxCoupling (phaseJ (phase x)) m (y - x)) beta
          (Sym2.map sigma e) =
        betaParams (phaseBoxCoupling phaseJ (phase y) m) beta e := by
    intro e
    unfold betaParams transBoxCoupling phaseBoxCoupling boxCoupling sigma
    rw [Sym2.map_map]
    have hfun :
        (Subtype.val ∘
            (fvs_transEquiv d m (y - x) :
              boxVerts d m -> fvs_transBoxVerts d m (y - x))) =
          (fun z : boxVerts d m => (z : Site d) + (y - x)) := by
      funext z
      rfl
    rw [hfun]
    have hc :=
      FKSharpnessWeightedInfiniteVolume.PhaseCovariant.phaseCoupling_translate
        hcov x y (Sym2.map Subtype.val e)
    have hc' :
        phaseJ (phase y) (Sym2.map Subtype.val e) =
          phaseJ (phase x)
            (Sym2.map (fun z : boxVerts d m => (z : Site d) + (y - x)) e) := by
      simpa [translateAmbientEdge, Sym2.map_map, Function.comp_def] using hc
    rw [← hc']
  have hmass := cdc_eventMassProb_reCfgIso_inv sigma
    (bcProbW (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m))
      (betaParams (phaseBoxCoupling phaseJ (phase y) m) beta) q)
    (bcProbW (fvs_transBoxGraph d m (y - x))
      (boundaryCliqueGraph (fvs_transBoxBoundary d m (y - x)))
      (betaParams (transBoxCoupling (phaseJ (phase x)) m (y - x)) beta) q)
    (fun omega => bcProbW_boundaryClique_reCfgIso
      (boxGraph d m) (fvs_transBoxGraph d m (y - x))
      (boxBoundary d m) (fvs_transBoxBoundary d m (y - x))
      sigma (fvs_transEquiv_adj d m (y - x))
      (fvs_transEquiv_boundary d m (y - x))
      (betaParams (phaseBoxCoupling phaseJ (phase y) m) beta)
      (betaParams (transBoxCoupling (phaseJ (phase x)) m (y - x)) beta)
      hparam q omega)
    event
  rw [med_reCfgIso_preimage sigma (t.image (innerEdgeLE d hNm))] at hmass
  simpa [weightedTransBoxMass, event, flc_transEdges] using hmass.symm


theorem weightedPhaseFiniteMeasure_eq_med
    (d N R : Nat) (hNR : N <= R) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta)
    (t : Finset (Sym2 (boxVerts d N)))
    (ht : t ⊆ (boxGraph d N).edgeFinset) :
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta hq hbeta :
        ProbabilityMeasure _) : Measure _).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))) =
      med_multiMassProb
        (bcProbW (boxGraph d R) (boundaryCliqueGraph (boxBoundary d R))
          (betaParams (phaseBoxCoupling phaseJ a R) beta) q)
        (t.image (innerEdgeLE d hNR)) := by
  rw [weightedPhaseFiniteMeasure_multiOpen_eq d N R hNR phaseJ a hJ
    q beta hq hbeta t ht]
  unfold med_multiMassProb
  apply Finset.sum_congr rfl
  intro omega homega
  congr 1
  by_cases h : omega ∈ ocd_innerRestrict
      (flc_incl (box_mono d hNR)) ⁻¹' cdc_boxMultiOpenEvent N t
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
    simpa [med_genericMultiOpenEvent, cdc_boxMultiOpenEvent,
      ocd_innerRestrict, ocd_innerEdge, flc_incl, innerEdgeLE,
      boxVertInclLE] using h
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    intro hm
    apply h
    simpa [med_genericMultiOpenEvent, cdc_boxMultiOpenEvent,
      ocd_innerRestrict, ocd_innerEdge, flc_incl, innerEdgeLE,
      boxVertInclLE] using hm



theorem weightedTransBoxMass_lower
    (K : Sym2 (Site d) -> Real) (hK : forall e, 0 < K e)
    (v : Site d) (N : Nat) (t : Finset (Sym2 (boxVerts d N)))
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (m : Nat) (hNm : N <= m) (hm : 1 <= m) :
    med_multiMassProb
        (bcProbW (boxGraph d (m + flc_vrad v + 1))
          (boundaryCliqueGraph (boxBoundary d (m + flc_vrad v + 1)))
          (betaParams (boxCoupling K (m + flc_vrad v + 1)) beta) q)
        ((flc_transEdges v N t m hNm).image
          (ocd_innerEdge (flc_incl
            ((flc_transBox_subset_box v m).trans
              (box_mono d (by omega)))))) <=
      weightedTransBoxMass K v N t q beta m hNm := by
  let c := flc_vrad v
  let hsub : fvs_transBox d m v ⊆ box d (m + c + 1) :=
    (flc_transBox_subset_box v m).trans (box_mono d (by omega))
  let iota := flc_incl hsub
  let A : Set (ConfigSpace (Sym2 (fvs_transBoxVerts d m v))) :=
    med_genericMultiOpenEvent (flc_transEdges v N t m hNm)
  have hparam : ocd_ParamCompatible iota
      (betaParams (transBoxCoupling K m v) beta)
      (betaParams (boxCoupling K (m + c + 1)) beta) := by
    intro e
    unfold betaParams transBoxCoupling boxCoupling iota hsub
    congr 3
    simp [ocd_innerEdge, Sym2.map_map, flc_incl_val]
  have hdom := ocd_latticeWired_inner_dominatedW
    (Sin := fvs_transBox d m v) (Sout := box d (m + c + 1))
    iota (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d (m + c + 1)) (fvs_transBoxBoundary d m v)
    (flc_hmargin_transBox_in_box v hsub) (flc_hbdryIn_transBox hm v)
    hparam
    (betaParams_pos (fun e => hK (Sym2.map Subtype.val e)) hbeta)
    (betaParams_lt_one _ beta)
    (betaParams_pos (fun e => hK (Sym2.map Subtype.val e)) hbeta)
    (betaParams_lt_one _ beta) hq
    (A := A) (fmu_multiOpen_isIncreasing _)
  have hpre : ocd_innerRestrict iota ⁻¹' A =
      med_genericMultiOpenEvent
        ((flc_transEdges v N t m hNm).image (ocd_innerEdge iota)) := by
    ext omega
    simp only [A, Set.mem_preimage, med_genericMultiOpenEvent,
      Set.mem_setOf_eq, Finset.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    rfl
  rw [hpre] at hdom
  simpa [weightedTransBoxMass, med_multiMassProb, A, iota, hsub, c,
    boxGraph, fvs_transBoxGraph] using hdom



theorem weightedTransBoxMass_upper
    (K : Sym2 (Site d) -> Real) (hK : forall e, 0 < K e)
    (v : Site d) (N : Nat) (t : Finset (Sym2 (boxVerts d N)))
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (m a : Nat) (hNm : N <= m) (ha : 1 <= a)
    (hcond : a + flc_vrad v + 1 <= m)
    (tb : Finset (Sym2 (boxVerts d a)))
    (htb : tb.image (edgeIncl d a) =
      (t.image (edgeIncl d N)).image
        (fun e => (Multiplicative.ofAdd v) • e)) :
    weightedTransBoxMass K v N t q beta m hNm <=
      med_multiMassProb
        (bcProbW (boxGraph d a) (boundaryCliqueGraph (boxBoundary d a))
          (betaParams (boxCoupling K a) beta) q) tb := by
  let hsub : box d a ⊆ fvs_transBox d m v :=
    flc_box_subset_transBox v (by omega)
  let iota := flc_incl hsub
  let A : Set (ConfigSpace (Sym2 (boxVerts d a))) :=
    med_genericMultiOpenEvent tb
  have hparam : ocd_ParamCompatible iota
      (betaParams (boxCoupling K a) beta)
      (betaParams (transBoxCoupling K m v) beta) := by
    intro e
    unfold betaParams transBoxCoupling boxCoupling iota hsub
    congr 3
    simp [ocd_innerEdge, Sym2.map_map, flc_incl_val]
  have hdom := ocd_latticeWired_inner_dominatedW
    (Sin := box d a) (Sout := fvs_transBox d m v)
    iota (flc_incl_val hsub) (flc_incl_injective hsub)
    (fvs_transBoxBoundary d m v) (boxBoundary d a)
    (flc_hmargin_box_in_transBox v hsub (by omega)) (flc_hbdryIn_box ha)
    hparam
    (betaParams_pos (fun e => hK (Sym2.map Subtype.val e)) hbeta)
    (betaParams_lt_one _ beta)
    (betaParams_pos (fun e => hK (Sym2.map Subtype.val e)) hbeta)
    (betaParams_lt_one _ beta) hq
    (A := A) (fmu_multiOpen_isIncreasing _)
  have hkey : tb.image (ocd_innerEdge iota) =
      flc_transEdges v N t m hNm := by
    apply flc_image_eq_of_val_image_eq
    rw [flc_valImage_transEdges v N t m hNm,
      flc_valImage_ocd_innerEdge_image hsub tb,
      show Sym2.map (Subtype.val : boxVerts d a -> Site d) =
        edgeIncl d a from rfl, htb]
  have hpre : ocd_innerRestrict iota ⁻¹' A =
      med_genericMultiOpenEvent (flc_transEdges v N t m hNm) := by
    rw [← hkey]
    ext omega
    simp only [A, Set.mem_preimage, med_genericMultiOpenEvent,
      Set.mem_setOf_eq, Finset.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    rfl
  rw [hpre] at hdom
  simpa [weightedTransBoxMass, med_multiMassProb, A, iota, hsub,
    boxGraph, fvs_transBoxGraph] using hdom

theorem translateAmbientEdge_mem_lattice_edgeSet
    (v : Site d) (e : Sym2 (Site d))
    (he : e ∈ (hypercubicLattice d).edgeSet) :
    translateAmbientEdge v e ∈ (hypercubicLattice d).edgeSet := by
  induction e using Sym2.ind with
  | _ x y =>
      change NearestNeighbour d (x + v) (y + v)
      change NearestNeighbour d x y at he
      simpa [NearestNeighbour] using he

theorem ofAdd_smul_edge_eq_translateAmbientEdge
    (v : Site d) (e : Sym2 (Site d)) :
    (Multiplicative.ofAdd v) • e = translateAmbientEdge v e := by
  induction e using Sym2.ind with
  | _ x y =>
      change s(v + x, v + y) = s(x + v, y + v)
      rw [add_comm v x, add_comm v y]



theorem weightedTransBoxMass_tendsto
    {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (v : Site d) (N N' M : Nat)
    (t : Finset (Sym2 (boxVerts d N)))
    (tb : Finset (Sym2 (boxVerts d N')))
    (htb : tb ⊆ (boxGraph d N').edgeFinset)
    (hrep : tb.image (edgeIncl d N') =
      (t.image (edgeIncl d N)).image
        (fun e => (Multiplicative.ofAdd v) • e))
    (hN' : 1 <= N') (hNM : N <= M)
    (hbuf : N' + flc_vrad v + 1 <= M)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto
      (fun k => weightedTransBoxMass (phaseJ a) v N t q beta
        (M + k) (hNM.trans (Nat.le_add_right M k)))
      atTop
      (nhds (((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real
          (cdc_multiOpenEvent (tb.image (edgeIncl d N'))))) := by
  let mass := fun R =>
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
      Measure _).real (cdc_multiOpenEvent (tb.image (edgeIncl d N')))
  have hmass : Tendsto mass atTop
      (nhds (((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real
          (cdc_multiOpenEvent (tb.image (edgeIncl d N'))))) := by
    simpa [mass] using weightedPhaseFiniteMeasure_multiOpen_tendsto
      d N' hN' phaseJ a hJ q beta hq hbeta tb htb
  have hlo : Tendsto (fun k => mass (M + k + flc_vrad v + 1)) atTop
      (nhds (((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real
          (cdc_multiOpenEvent (tb.image (edgeIncl d N'))))) :=
    hmass.comp (tendsto_atTop_mono
      (fun k => by
        show k <= M + k + flc_vrad v + 1
        omega) tendsto_id)
  have hhi : Tendsto (fun k => mass (N' + k)) atTop
      (nhds (((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real
          (cdc_multiOpenEvent (tb.image (edgeIncl d N'))))) :=
    by
      simpa [Nat.add_comm] using hmass.comp (tendsto_add_atTop_nat N')
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards with k
    let m := M + k
    let hmN : N <= m := hNM.trans (Nat.le_add_right M k)
    have hm : 1 <= m := hN'.trans
      (le_trans (by omega : N' <= M) (Nat.le_add_right M k))
    have hlower := weightedTransBoxMass_lower (phaseJ a) hJ v N t
      q beta hq hbeta m hmN hm
    have hedge :
        (flc_transEdges v N t m hmN).image
            (ocd_innerEdge (flc_incl
              ((flc_transBox_subset_box v m).trans
                (box_mono d (by omega))))) =
          tb.image (innerEdgeLE d (by omega : N' <= m + flc_vrad v + 1)) := by
      apply flc_image_eq_of_val_image_eq
      rw [flc_valImage_ocd_innerEdge_image
          ((flc_transBox_subset_box v m).trans
            (box_mono d (by omega)))
          (flc_transEdges v N t m hmN),
        flc_valImage_transEdges v N t m hmN,
        show Sym2.map
            (Subtype.val : boxVerts d (m + flc_vrad v + 1) -> Site d) =
          edgeIncl d (m + flc_vrad v + 1) from rfl,
        plc_relift_image N' (m + flc_vrad v + 1)
          (by omega : N' <= m + flc_vrad v + 1) tb,
        hrep]
    dsimp [mass]
    rw [weightedPhaseFiniteMeasure_eq_med d N'
      (m + flc_vrad v + 1) (by omega) phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta tb htb, ← hedge]
    simpa [m, Nat.add_assoc] using hlower
  · filter_upwards with k
    let m := M + k
    let aa := N' + k
    let hmN : N <= m := hNM.trans (Nat.le_add_right M k)
    let tb' := tb.image (innerEdgeLE d (Nat.le_add_right N' k))
    have htb' : tb'.image (edgeIncl d aa) =
        (t.image (edgeIncl d N)).image
          (fun e => (Multiplicative.ofAdd v) • e) := by
      dsimp [tb', aa]
      calc
        (tb.image (innerEdgeLE d (Nat.le_add_right N' k))).image
              (edgeIncl d (N' + k)) = tb.image (edgeIncl d N') := by
          rw [Finset.image_image]
          exact Finset.image_congr fun e he =>
            edgeIncl_innerEdgeLE d (Nat.le_add_right N' k) e
        _ = _ := hrep
    have hupper := weightedTransBoxMass_upper (phaseJ a) hJ v N t
      q beta hq hbeta m aa hmN (by omega) (by omega) tb' htb'
    have hmed :
        med_multiMassProb
          (bcProbW (boxGraph d aa) (boundaryCliqueGraph (boxBoundary d aa))
          (betaParams (boxCoupling (phaseJ a) aa) beta) q) tb' =
          mass aa := by
      symm
      simpa [mass, aa, tb'] using
        (weightedPhaseFiniteMeasure_eq_med d N' aa
          (Nat.le_add_right N' k) phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta tb htb)
    rw [hmed] at hupper
    simpa [m, aa] using hupper



theorem covariantWeightedSelectedPhaseTranslation
    {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 1 <= q) :
    CovariantWeightedSelectedPhaseTranslation d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) phase q
      (zero_lt_one.trans_le hq) := by
  intro beta hbeta x y
  let hp : forall a e, 0 < phaseJ a e :=
    hcov.phaseCoupling_pos hsurj hJ
  let mux : Measure (ConfigSpace (Sym2 (Site d))) :=
    weightedPhaseInfiniteVolume d phaseJ (phase x) (hp (phase x))
      q beta (zero_lt_one.trans_le hq) hbeta
  let muy : Measure (ConfigSpace (Sym2 (Site d))) :=
    weightedPhaseInfiniteVolume d phaseJ (phase y) (hp (phase y))
      q beta (zero_lt_one.trans_le hq) hbeta
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (x - y)
  change muy = mux.map (ConfigSpace.shift g)
  haveI : IsProbabilityMeasure muy := by dsimp [muy]; infer_instance
  haveI : IsProbabilityMeasure mux := by dsimp [mux]; infer_instance
  haveI : IsProbabilityMeasure (mux.map (ConfigSpace.shift g)) :=
    Measure.isProbabilityMeasure_map
      (ConfigSpace.measurable_shift g).aemeasurable
  apply fkgqt_measure_eq_of_multiOpen_eq
  intro T
  rw [Measure.map_apply (ConfigSpace.measurable_shift g)
    (fmu_multiOpen_measurable T), fmu_shift_multiOpen]
  let v : Site d := y - x
  let Tv := T.image (fun e => (Multiplicative.ofAdd v) • e)
  have hTshift : T.image (fun e => g⁻¹ • e) = Tv := by
    apply Finset.image_congr
    intro e he
    simp [g, v, sub_eq_add_neg, div_eq_mul_inv]
  rw [hTshift]
  suffices hreal : muy.real (cdc_multiOpenEvent T) =
      mux.real (cdc_multiOpenEvent Tv) by
    unfold Measure.real at hreal
    exact (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top muy _) (measure_ne_top mux _)).mp hreal
  by_cases hT : forall e, e ∈ T -> e ∈ (hypercubicLattice d).edgeSet
  · obtain ⟨N, hN, t, ht, hrep⟩ :=
      lattice_finset_in_positive_box (d := d) T hT
    have hTv : forall e, e ∈ Tv ->
        e ∈ (hypercubicLattice d).edgeSet := by
      intro e he
      change e ∈ T.image (fun f => (Multiplicative.ofAdd v) • f) at he
      rw [Finset.mem_image] at he
      obtain ⟨f, hfT, rfl⟩ := he
      simpa [ofAdd_smul_edge_eq_translateAmbientEdge] using
        translateAmbientEdge_mem_lattice_edgeSet v f (hT f hfT)
    obtain ⟨N', hN', tb, htb, hrep'⟩ :=
      lattice_finset_in_positive_box (d := d) Tv hTv
    let M := max N (N' + flc_vrad v + 1)
    have hNM : N <= M := le_max_left _ _
    have hbuf : N' + flc_vrad v + 1 <= M := le_max_right _ _
    have hyfull := weightedPhaseFiniteMeasure_multiOpen_tendsto
      d N hN phaseJ (phase y) (hp (phase y)) q beta hq hbeta t ht
    have hy : Tendsto
        (fun k => ((weightedPhaseFiniteMeasure d (M + k) phaseJ
          (phase y) (hp (phase y)) q beta (zero_lt_one.trans_le hq)
          hbeta : ProbabilityMeasure _) : Measure _).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))))
        atTop (nhds (muy.real (cdc_multiOpenEvent T))) := by
      rw [hrep]
      exact hyfull.comp (tendsto_atTop_mono
        (fun k => by show k <= M + k; omega) tendsto_id)
    have hrelabel : forall k,
        ((weightedPhaseFiniteMeasure d (M + k) phaseJ
          (phase y) (hp (phase y)) q beta (zero_lt_one.trans_le hq)
          hbeta : ProbabilityMeasure _) : Measure _).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))) =
          weightedTransBoxMass (phaseJ (phase x)) v N t q beta
            (M + k) (hNM.trans (Nat.le_add_right M k)) := by
      intro k
      exact weightedPhaseFiniteMeasure_relabel J phase phaseJ hcov x y
        N (M + k) (hNM.trans (Nat.le_add_right M k)) t ht hp q beta
        (zero_lt_one.trans_le hq) hbeta
    have hxlim := weightedTransBoxMass_tendsto phaseJ (phase x)
      (hp (phase x)) v N N' M t tb htb
      (by simpa [Tv, hrep] using hrep'.symm) hN' hNM hbuf q beta hq hbeta
    have hylimit : Tendsto
        (fun k => weightedTransBoxMass (phaseJ (phase x)) v N t q beta
          (M + k) (hNM.trans (Nat.le_add_right M k)))
        atTop (nhds (muy.real (cdc_multiOpenEvent T))) :=
      hy.congr' (Filter.Eventually.of_forall fun k => hrelabel k)
    have heq := tendsto_nhds_unique hylimit hxlim
    simpa [mux, Tv, hrep'] using heq
  · push Not at hT
    obtain ⟨e, heT, he⟩ := hT
    have hy0 := weightedPhaseInfiniteVolume_nonLattice_multiOpen_zero
      d phaseJ (phase y) (hp (phase y)) q beta
      (zero_lt_one.trans_le hq) hbeta T e heT he
    let ev := translateAmbientEdge v e
    have hevTv : ev ∈ Tv := by
      exact Finset.mem_image.mpr ⟨e, heT, by
        simp [ev, ofAdd_smul_edge_eq_translateAmbientEdge]⟩
    have hev : ev ∉ (hypercubicLattice d).edgeSet := by
      intro hev
      have hinv := translateAmbientEdge_mem_lattice_edgeSet (-v) ev hev
      apply he
      simpa [ev, translateAmbientEdge, Sym2.map_map, Function.comp_def]
        using hinv
    have hx0 := weightedPhaseInfiniteVolume_nonLattice_multiOpen_zero
      d phaseJ (phase x) (hp (phase x)) q beta
      (zero_lt_one.trans_le hq) hbeta Tv ev hevTv hev
    simpa [mux, muy] using hy0.trans hx0.symm


theorem covariantWeightedSelectedPhaseLaws
    {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 1 <= q) :
    CovariantWeightedSelectedPhaseLaws d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) phase q
      (zero_lt_one.trans_le hq) := by
  rw [covariantWeightedSelectedPhaseLaws_iff]
  exact ⟨covariantWeightedSelectedPhaseTranslation
      J phase phaseJ hJ hsurj hcov q hq,
    weightedSelectedPhaseFiniteEnergy d phaseJ
      (hcov.phaseCoupling_pos hsurj hJ) q hq⟩



theorem covariantWeightedPhasePositivityTransport
    {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 1 <= q) :
    CovariantWeightedPhasePositivityTransport
      d J phase phaseJ hJ hsurj hcov q (zero_lt_one.trans_le hq) := by
  exact covariantWeightedPhasePositivityTransport_of_selectedLaws'
    J phase phaseJ hJ hsurj hcov q (zero_lt_one.trans_le hq)
    (covariantWeightedSelectedPhaseLaws
      J phase phaseJ hJ hsurj hcov q hq)



theorem covariant_weighted_phase_common_critical
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall e, 0 < J e) (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q : Real) (hq : 1 <= q) (a : P) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun b => weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj hJ) q
          (zero_lt_one.trans_le hq) b beta) = 0} =
      sSup {beta | weightedPhaseThetaProfile d phaseJ
        (hcov.phaseCoupling_pos hsurj hJ) q
        (zero_lt_one.trans_le hq) a beta = 0} := by
  exact covariant_weighted_phase_common_critical_of_selectedLaws
    J phase phaseJ hJ hsurj hcov q (zero_lt_one.trans_le hq)
    (covariantWeightedSelectedPhaseLaws
      J phase phaseJ hJ hsurj hcov q hq) a

end FKSharpnessWeightedPhaseClose
end OSSS
end StatMech
