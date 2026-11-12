/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.OSSS.FKSharpnessWeightedPhaseTransport
import Code.FK.PlacementClose

open MeasureTheory Set Filter Topology
open scoped BigOperators Classical

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedSelectedLaws

open Lattice FK Percolation
open RevealmentConstruction WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre
open FKSharpnessWeightedPeriodic
open FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedCoherentLimit
open FKSharpnessWeightedPhaseTransport

variable {d : Nat}



private theorem closedFiber_pairMass_eq_sum
    {E : Type*} [Fintype E] [DecidableEq E]
    (m : ConfigSpace E -> Real) (e : E) :
    (∑ psi ∈ Finset.univ.filter
        (fun psi : ConfigSpace E => psi e = false),
      (m (setOpen e psi) + m (setClosed e psi))) =
      ∑ omega, m omega := by
  rw [Finset.sum_add_distrib, <- openMarginal_eq_closedFiber]
  have hclosed :
      (∑ psi ∈ Finset.univ.filter
          (fun psi : ConfigSpace E => psi e = false),
        m (setClosed e psi)) =
        ∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace E => omega e = false), m omega := by
    apply Finset.sum_congr rfl
    intro psi hpsi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpsi
    congr 1
    funext x
    by_cases hx : x = e
    · subst x
      simp [hpsi]
    · simp [setClosed_of_ne hx]
  rw [hclosed]
  unfold openMarginal
  rw [show Finset.univ.filter (fun omega : ConfigSpace E => omega e = false) =
      Finset.univ.filter (fun omega : ConfigSpace E => ¬ omega e = true) by
        ext omega
        simp]
  rw [Finset.sum_filter_add_sum_filter_not]

private theorem finite_singleOpen_preimage_bound
    {E : Type*} [Fintype E] [DecidableEq E]
    (mu : ConfigSpace E -> Real) (e : E) (c : Real)
    (hmu : forall omega, 0 <= mu omega)
    (hpair : forall psi,
      c * (mu (setOpen e psi) + mu (setClosed e psi)) <=
        mu (setOpen e psi))
    (A : Set (ConfigSpace E)) :
    c * (∑ omega,
        (setOpen e ⁻¹' A).indicator (fun _ => (1 : Real)) omega * mu omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega * mu omega := by
  let S := Finset.univ.filter (fun psi : ConfigSpace E => psi e = false)
  have hlhs := closedFiber_pairMass_eq_sum
    (fun omega => (setOpen e ⁻¹' A).indicator (fun _ => (1 : Real)) omega * mu omega) e
  have hrhs := closedFiber_pairMass_eq_sum
    (fun omega => A.indicator (fun _ => (1 : Real)) omega * mu omega) e
  rw [<- hlhs, <- hrhs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  have hopenopen : setOpen e (setOpen e psi) = setOpen e psi := by
    funext x
    by_cases hx : x = e
    · subst x
      simp
    · simp [setOpen_of_ne hx]
  have hopenclosed : setOpen e (setClosed e psi) = setOpen e psi := by
    funext x
    by_cases hx : x = e
    · subst x
      simp
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  have hpreopen : setOpen e psi ∈ setOpen e ⁻¹' A ↔ setOpen e psi ∈ A := by
    change setOpen e (setOpen e psi) ∈ A ↔ _
    rw [hopenopen]
  have hpreclosed : setClosed e psi ∈ setOpen e ⁻¹' A ↔ setOpen e psi ∈ A := by
    change setOpen e (setClosed e psi) ∈ A ↔ _
    rw [hopenclosed]
  by_cases hAopen : setOpen e psi ∈ A
  · rw [Set.indicator_of_mem (hpreopen.mpr hAopen),
      Set.indicator_of_mem (hpreclosed.mpr hAopen),
      Set.indicator_of_mem hAopen]
    by_cases hAclosed : setClosed e psi ∈ A
    · rw [Set.indicator_of_mem hAclosed]
      simpa only [one_mul] using (hpair psi).trans
        (le_add_of_nonneg_right (hmu (setClosed e psi)))
    · rw [Set.indicator_of_notMem hAclosed, zero_mul, add_zero]
      simpa only [one_mul] using hpair psi
  · rw [Set.indicator_of_notMem (not_congr hpreopen |>.mpr hAopen),
      Set.indicator_of_notMem (not_congr hpreclosed |>.mpr hAopen),
      Set.indicator_of_notMem hAopen, zero_mul, zero_mul, add_zero]
    by_cases hAclosed : setClosed e psi ∈ A
    · rw [Set.indicator_of_mem hAclosed]
      simpa only [one_mul, zero_mul, mul_zero, zero_add] using hmu (setClosed e psi)
    · rw [Set.indicator_of_notMem hAclosed, zero_mul, add_zero]
      simp




noncomputable def weightedOpenTolerance (p q : Real) : Real :=
  p / (p + q * (1 - p))

theorem weightedOpenTolerance_pos {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    0 < weightedOpenTolerance p q := by
  unfold weightedOpenTolerance
  positivity

private theorem activeBCWeight_open_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf : Sym2 V -> Real} (hpf : forall e, 0 < pf e)
    (hpf1 : forall e, pf e < 1) {q : Real} (hq : 1 <= q)
    (e : G.edgeSet) (omega : ConfigSpace G.edgeSet) :
    pf e.1 * activeBCWeight G C pf q (setClosed e omega) <=
      q * (1 - pf e.1) * activeBCWeight G C pf q (setOpen e omega) := by
  unfold activeBCWeight
  rw [extendActive_setOpen, extendActive_setClosed,
    edgeProductW_setOpen, edgeProductW_setClosed]
  let R := ∏ a ∈ G.edgeFinset.erase e.1,
    if extendActive G omega a then pf a else 1 - pf a
  have hR : 0 <= R := by
    unfold R
    apply Finset.prod_nonneg
    intro a ha
    split
    · exact (hpf a).le
    · linarith [hpf1 a]
  have hpow : q ^ numClustersBC G C
        (setClosed e.1 (extendActive G omega)) <=
      q ^ (numClustersBC G C (setOpen e.1 (extendActive G omega)) + 1) :=
    pow_le_pow_right₀ hq
      (numClustersBC_setOpen_bounds G C e.1 (extendActive G omega)).2
  rw [pow_succ] at hpow
  have hpclosed : 0 <= 1 - pf e.1 := sub_nonneg.mpr (hpf1 e.1).le
  have hp : 0 <= pf e.1 * (1 - pf e.1) :=
    mul_nonneg (hpf e.1).le hpclosed
  nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg hR hp)]

private theorem activeBCProb_open_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf : Sym2 V -> Real} (hpf : forall e, 0 < pf e)
    (hpf1 : forall e, pf e < 1) {q : Real} (hq : 1 <= q)
    (e : G.edgeSet) (omega : ConfigSpace G.edgeSet) :
    weightedOpenTolerance (pf e.1) q *
        (activeBCProb G C pf q (setOpen e omega) +
          activeBCProb G C pf q (setClosed e omega)) <=
      activeBCProb G C pf q (setOpen e omega) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hZ := activeBCZ_pos G C hpf hpf1 hq0
  have hratio := activeBCWeight_open_pair G C hpf hpf1 hq e omega
  unfold activeBCProb
  rw [show activeBCWeight G C pf q (setOpen e omega) / activeBCZ G C pf q +
      activeBCWeight G C pf q (setClosed e omega) / activeBCZ G C pf q =
      (activeBCWeight G C pf q (setOpen e omega) +
        activeBCWeight G C pf q (setClosed e omega)) / activeBCZ G C pf q by ring]
  have hpclosed : 0 < 1 - pf e.1 := sub_pos.mpr (hpf1 e.1)
  have hden : 0 < pf e.1 + q * (1 - pf e.1) :=
    add_pos (hpf e.1) (mul_pos hq0 hpclosed)
  have hleft : weightedOpenTolerance (pf e.1) q *
        ((activeBCWeight G C pf q (setOpen e omega) +
          activeBCWeight G C pf q (setClosed e omega)) / activeBCZ G C pf q) =
      (weightedOpenTolerance (pf e.1) q *
        (activeBCWeight G C pf q (setOpen e omega) +
          activeBCWeight G C pf q (setClosed e omega))) /
        activeBCZ G C pf q := by ring
  rw [hleft, div_le_div_iff_of_pos_right hZ]
  unfold weightedOpenTolerance
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith

theorem activeBCProb_singleOpen_preimage_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {pf : Sym2 V -> Real} (hpf : forall e, 0 < pf e)
    (hpf1 : forall e, pf e < 1) {q : Real} (hq : 1 <= q)
    (e : G.edgeSet) (A : Set (ConfigSpace G.edgeSet)) :
    weightedOpenTolerance (pf e.1) q *
        (∑ omega, (setOpen e ⁻¹' A).indicator (fun _ => (1 : Real)) omega *
          activeBCProb G C pf q omega) <=
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        activeBCProb G C pf q omega := by
  exact finite_singleOpen_preimage_bound
    (activeBCProb G C pf q) e (weightedOpenTolerance (pf e.1) q)
    (fun omega => (activeBCProb_pos G C hpf hpf1
      (zero_lt_one.trans_le hq) omega).le)
    (activeBCProb_open_pair G C hpf hpf1 hq e) A



theorem liftCfg_setOpen
    {E : Type*} [Fintype E] [DecidableEq E]
    (edge : E -> Sym2 (Site d)) (hinj : Function.Injective edge)
    (e : E) (omega : ConfigSpace E) :
    liftCfg edge (setOpen e omega) = setOpen (edge e) (liftCfg edge omega) := by
  funext x
  by_cases hx : exists f, edge f = x
  · obtain ⟨f, rfl⟩ := hx
    by_cases hfe : f = e
    · subst f
      simp [liftCfg_apply_edge hinj]
    · have hedge : edge f ≠ edge e := fun h => hfe (hinj h)
      rw [liftCfg_apply_edge hinj, setOpen_of_ne hfe, setOpen_of_ne hedge,
        liftCfg_apply_edge hinj]
  · unfold liftCfg
    rw [dif_neg hx]
    have hne : x ≠ edge e := by
      intro h
      exact hx ⟨e, h.symm⟩
    rw [setOpen_of_ne hne]
    rw [dif_neg hx]

theorem weightedPhaseFiniteMeasure_singleOpen_bound
    (d n : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (e : (boxGraph d n).edgeSet)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : MeasurableSet A) :
    weightedOpenTolerance
        (betaParams (phaseJ a) beta (boxActiveEdge d n e)) q *
      ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
        (setOpen (boxActiveEdge d n e) ⁻¹' A) <=
      ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real A := by
  let pf := betaParams (phaseBoxCoupling phaseJ a n) beta
  have hpf : forall f, 0 < pf f :=
    betaParams_pos (fun f => hJ (Sym2.map Subtype.val f)) hbeta
  have hpf1 : forall f, pf f < 1 := betaParams_lt_one _ beta
  have hpre :
      liftCfg (boxActiveEdge d n) ⁻¹'
          (setOpen (boxActiveEdge d n e) ⁻¹' A) =
        setOpen e ⁻¹' (liftCfg (boxActiveEdge d n) ⁻¹' A) := by
    ext omega
    change setOpen (boxActiveEdge d n e)
        (liftCfg (boxActiveEdge d n) omega) ∈ A ↔
      liftCfg (boxActiveEdge d n) (setOpen e omega) ∈ A
    rw [liftCfg_setOpen (boxActiveEdge d n) (boxActiveEdge_injective d n)]
  rw [weightedPhaseFiniteMeasure_real_eq d n phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta _
      (hA.preimage (measurable_setOpen (boxActiveEdge d n e))),
    weightedPhaseFiniteMeasure_real_eq d n phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta A hA, hpre]
  have hbound := activeBCProb_singleOpen_preimage_bound
    (boxGraph d n) (wiredBoxBoundaryGraph d n) hpf hpf1 hq e
    (liftCfg (boxActiveEdge d n) ⁻¹' A)
  simpa [pf, phaseBoxCoupling, boxCoupling, boxActiveEdge] using hbound



theorem weightedPhaseInfinite_singleOpen_cylinder_bound
    (d N : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    weightedOpenTolerance
        (betaParams (phaseJ a) beta (edgeIncl d N eb)) q *
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
        (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) <=
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ := weightedPhaseInfiniteVolume_isLimit
    d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
  have hpre := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N (setOpen eb ⁻¹' S))
  have hbase := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N S)
  have hc : Tendsto (fun _ : Nat => weightedOpenTolerance
      (betaParams (phaseJ a) beta (edgeIncl d N eb)) q) atTop
      (nhds (weightedOpenTolerance
        (betaParams (phaseJ a) beta (edgeIncl d N eb)) q)) :=
    tendsto_const_nhds
  apply le_of_tendsto_of_tendsto (hc.mul hpre) hbase
  filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with k hk
  let eN : (boxGraph d N).edgeSet := ⟨eb, by
    rwa [SimpleGraph.mem_edgeFinset] at heb⟩
  let eR : (boxGraph d (phi k)).edgeSet := boxActiveEdgeLE d hk eN
  have hedge : boxActiveEdge d (phi k) eR = edgeIncl d N eb := by
    calc
      boxActiveEdge d (phi k) eR = boxActiveEdge d N eN :=
        boxActiveEdgeLE_ambient d hk eN
      _ = edgeIncl d N eb := rfl
  have hset :
      setOpen (boxActiveEdge d (phi k) eR) ⁻¹'
          (boxRestrict d N ⁻¹' S) =
        boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S) := by
    rw [hedge]
    ext omega
    change boxRestrict d N (setOpen (edgeIncl d N eb) omega) ∈ S ↔
      setOpen eb (boxRestrict d N omega) ∈ S
    rw [boxRestrict_setOpen]
  have hbound := weightedPhaseFiniteMeasure_singleOpen_bound
    d (phi k) phaseJ a hJ q beta hq hbeta eR
    (boxRestrict d N ⁻¹' S) (fkWiredLimit_measurableSet_preimage N S)
  rw [← hset]
  simpa only [hedge] using hbound

theorem weightedPhaseInfinite_singleOpen_fullCylinder_bound
    (d N : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (eN : (boxGraph d N).edgeSet)
    (C : Set (ConfigSpace (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
    weightedOpenTolerance
        (betaParams (phaseJ a) beta (boxActiveEdge d N eN)) q *
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
        (setOpen (boxActiveEdge d N eN) ⁻¹' C) <=
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, S, hsS, rfl⟩ := hC
  obtain ⟨M, t, hst⟩ := cdc_finset_in_box s
  let K := max N M
  let tK : Finset (Sym2 (boxVerts d K)) :=
    t.image (innerEdgeLE d (le_max_right N M))
  have hstK : s = tK.image (edgeIncl d K) := by
    rw [hst]
    exact (plc_relift_image M K (le_max_right N M) t).symm
  have hsrange : forall x, x ∈ s -> x ∈ Set.range (edgeIncl d K) := by
    intro x hx
    rw [hstK] at hx
    obtain ⟨xb, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨xb, rfl⟩
  let eK : (boxGraph d K).edgeSet :=
    boxActiveEdgeLE d (le_max_left N M) eN
  have hedge : boxActiveEdge d K eK = boxActiveEdge d N eN :=
    boxActiveEdgeLE_ambient d (le_max_left N M) eN
  let T := extendEdge d K ⁻¹' cylinder s S
  have hCeq : cylinder s S = boxRestrict d K ⁻¹' T :=
    cylinder_eq_boxRestrict_preimage_extend K s S hsrange
  have hpre : setOpen (boxActiveEdge d N eN) ⁻¹' cylinder s S =
      boxRestrict d K ⁻¹' (setOpen eK.1 ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage]
    rw [hCeq]
    change boxRestrict d K (setOpen (boxActiveEdge d N eN) omega) ∈ T ↔
      setOpen eK.1 (boxRestrict d K omega) ∈ T
    rw [← hedge]
    change boxRestrict d K (setOpen (edgeIncl d K eK.1) omega) ∈ T ↔
      setOpen eK.1 (boxRestrict d K omega) ∈ T
    rw [boxRestrict_setOpen]
  rw [hpre, hCeq, ← hedge]
  exact weightedPhaseInfinite_singleOpen_cylinder_bound
    d K phaseJ a hJ q beta hq hbeta eK.1
      (by rw [SimpleGraph.mem_edgeFinset]; exact eK.2) T

theorem weightedPhaseInfinite_setOpen_absolutelyContinuous
    (d N : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (eN : (boxGraph d N).edgeSet) :
    ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).map
          (setOpen (boxActiveEdge d N eN)) ≪
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _) := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    weightedPhaseInfiniteVolume d phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta
  let c := weightedOpenTolerance
    (betaParams (phaseJ a) beta (boxActiveEdge d N eN)) q
  have hp : 0 < betaParams (phaseJ a) beta (boxActiveEdge d N eN) := by
    unfold betaParams
    have hprod := mul_pos hbeta (hJ (boxActiveEdge d N eN))
    have hexp : Real.exp (-(beta * phaseJ a (boxActiveEdge d N eN))) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_neg_of_pos hprod)
    linarith
  have hp1 : betaParams (phaseJ a) beta (boxActiveEdge d N eN) < 1 := by
    unfold betaParams
    linarith [Real.exp_pos (-(beta * phaseJ a (boxActiveEdge d N eN)))]
  have hc : 0 < c := weightedOpenTolerance_pos hp hp1 hq
  apply map_absolutelyContinuous_of_real_preimage_bound mu
    (setOpen (boxActiveEdge d N eN))
    (measurable_setOpen (boxActiveEdge d N eN)) c hc
  intro A hA
  exact pattern_bound_of_cylinders mu (setOpen (boxActiveEdge d N eN))
    (measurable_setOpen (boxActiveEdge d N eN)) c hc.le
    (weightedPhaseInfinite_singleOpen_fullCylinder_bound
      d N phaseJ a hJ q beta hq hbeta eN) A hA

private theorem boxEdge_has_active_rep
    (d n : Nat) (e : Sym2 (Site d)) (he : e ∈ boxEdges d n) :
    exists eN : (boxGraph d n).edgeSet, boxActiveEdge d n eN = e := by
  induction e with
  | h x y =>
      obtain ⟨hx, hy, hxy⟩ := (mem_boxEdges_iff.mp he)
      let xb : boxVerts d n := ⟨x, hx⟩
      let yb : boxVerts d n := ⟨y, hy⟩
      have hb : (boxGraph d n).Adj xb yb := hxy
      let eN : (boxGraph d n).edgeSet := ⟨s(xb, yb), by
        rw [SimpleGraph.mem_edgeSet]
        exact hb⟩
      refine ⟨eN, ?_⟩
      change edgeIncl d n s(xb, yb) = s(x, y)
      simp [edgeIncl, xb, yb]

theorem weightedPhaseInfinite_hasBoxFiniteEnergy
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    HasBoxFiniteEnergy
      (weightedPhaseInfiniteVolume d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    weightedPhaseInfiniteVolume d phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta
  intro n
  have hone : forall e, e ∈ boxEdges d n -> mu.map (setOpen e) ≪ mu := by
    intro e he
    obtain ⟨eN, rfl⟩ := boxEdge_has_active_rep d n e he
    exact weightedPhaseInfinite_setOpen_absolutelyContinuous
      d n phaseJ a hJ q beta hq hbeta eN
  have hforce : forall F : Finset (Sym2 (Site d)), F ⊆ boxEdges d n ->
      mu.map (forceOpenFinset F) ≪ mu := by
    intro F hF
    induction F using Finset.induction with
    | empty =>
        have hempty : forceOpenFinset (∅ : Finset (Sym2 (Site d))) = id := by
          funext omega e
          simp [forceOpenFinset]
        rw [hempty, Measure.map_id]
    | @insert e F he ih =>
        have hFac : F ⊆ boxEdges d n :=
          fun x hx => hF (Finset.mem_insert_of_mem hx)
        have hebox : e ∈ boxEdges d n := hF (Finset.mem_insert_self e F)
        have hmap := (ih hFac).map (measurable_setOpen e)
        have htrans := hmap.trans (hone e hebox)
        rw [Measure.map_map (measurable_setOpen e)
          (measurable_forceOpenFinset F)] at htrans
        rwa [← forceOpenFinset_insert e F] at htrans
  exact hforce (boxEdges d n) (fun _ => id)

theorem weightedSelectedPhaseFiniteEnergy
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q : Real) (hq : 1 <= q) :
    WeightedSelectedPhaseFiniteEnergy d phaseJ hJ q
      (zero_lt_one.trans_le hq) := by
  intro beta hbeta a
  exact weightedPhaseInfinite_hasBoxFiniteEnergy
    d phaseJ a (hJ a) q beta hq hbeta






noncomputable def coherentTranslatedLaw
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) (x : Site d) :
    ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
  ⟨(mu : Measure (ConfigSpace (Sym2 (Site d)))).map
      (ConfigSpace.shift (Multiplicative.ofAdd (-x))),
    Measure.isProbabilityMeasure_map
      (ConfigSpace.measurable_shift (Multiplicative.ofAdd (-x))).aemeasurable⟩

theorem coherentTranslatedLaw_covariant
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) (x y : Site d) :
    (coherentTranslatedLaw mu y :
        Measure (ConfigSpace (Sym2 (Site d)))) =
      (coherentTranslatedLaw mu x :
        Measure (ConfigSpace (Sym2 (Site d)))).map
          (ConfigSpace.shift (Multiplicative.ofAdd (x - y))) := by
  unfold coherentTranslatedLaw
  change (mu : Measure (ConfigSpace (Sym2 (Site d)))).map
      (ConfigSpace.shift (Multiplicative.ofAdd (-y))) =
    ((mu : Measure (ConfigSpace (Sym2 (Site d)))).map
      (ConfigSpace.shift (Multiplicative.ofAdd (-x)))).map
        (ConfigSpace.shift (Multiplicative.ofAdd (x - y)))
  rw [Measure.map_map (ConfigSpace.measurable_shift _)
    (ConfigSpace.measurable_shift _)]
  congr 1
  rw [← ConfigSpace.shift_mul]
  apply congrArg (fun g : Multiplicative (Site d) =>
    (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
      ConfigSpace (Sym2 (Site d))))
  apply Multiplicative.toAdd.injective
  change -y = (x - y) + (-x)
  abel

end FKSharpnessWeightedSelectedLaws
end OSSS
end StatMech
