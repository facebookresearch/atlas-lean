/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.OSSS.FKSharpnessWeightedInfiniteVolume
import Code.FK.WiredDomChain

open MeasureTheory
open scoped BigOperators Classical
open Set Filter Topology

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedCoherentLimit

open Lattice FK Percolation RevealmentConstruction
open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre
open FKSharpnessWeightedPeriodic FKSharpnessWeightedPeriodicRepair
open FKSharpnessWeightedDomain FKSharpnessWeightedInfiniteVolume



theorem weightedWiredActivePMF_toMeasure_toReal
    (d n : Nat) (J : Sym2 (boxVerts d n) -> Real)
    (hJ : forall e, 0 < J e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta)
    (S : Set (ConfigSpace (boxGraph d n).edgeSet)) :
    ((weightedWiredActivePMF d n J hJ q beta hq hbeta).toMeasure S).toReal =
      ∑ omega : ConfigSpace (boxGraph d n).edgeSet,
        S.indicator (fun _ => (1 : Real)) omega *
          activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
            (betaParams J beta) q omega := by
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun a _ => ?_)]
  · apply Finset.sum_congr rfl
    intro omega _
    by_cases homega : omega ∈ S
    · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega,
        weightedWiredActivePMF, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal
          ((activeBCProb_pos (boxGraph d n) (wiredBoxBoundaryGraph d n)
            (betaParams_pos hJ hbeta) (betaParams_lt_one J beta) hq omega).le),
        one_mul]
    · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]
      simp
  · by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, weightedWiredActivePMF,
        PMF.ofFintype_apply]
      exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem ha]
      simp


theorem weightedPhaseFiniteMeasure_real_eq
    (d n : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : MeasurableSet A) :
    ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta hq hbeta :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
        Measure (ConfigSpace (Sym2 (Site d)))).real A =
      ∑ omega : ConfigSpace (boxGraph d n).edgeSet,
        (liftCfg (boxActiveEdge d n) ⁻¹' A).indicator
            (fun _ => (1 : Real)) omega *
          activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
            (betaParams (phaseBoxCoupling phaseJ a n) beta) q omega := by
  let J := phaseBoxCoupling phaseJ a n
  let hJbox : forall e, 0 < J e :=
    fun e => hJ (Sym2.map Subtype.val e)
  have hmap :
      ((weightedPhaseFiniteMeasure d n phaseJ a hJ q beta hq hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
          Measure (ConfigSpace (Sym2 (Site d)))).real A =
        ((weightedWiredActivePMF d n J hJbox q beta hq hbeta).toMeasure
          (liftCfg (boxActiveEdge d n) ⁻¹' A)).toReal := by
    unfold weightedPhaseFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply Measurable.of_discrete hA]
  rw [hmap, weightedWiredActivePMF_toMeasure_toReal]




theorem boxRestrict_liftActive_eq_on_inner_edges
    (d : Nat) {k R : Nat} (hkR : k <= R)
    (rho : ConfigSpace (Sym2 (boxVerts d R)))
    (e : Sym2 (boxVerts d k)) (he : e ∈ (boxGraph d k).edgeFinset) :
    boxRestrict d k
        (liftCfg (boxActiveEdge d R)
          (restrictActive (boxGraph d R) rho)) e =
      boxRestrictLE d hkR rho e := by
  have heSet : e ∈ (boxGraph d k).edgeSet := by
    rwa [SimpleGraph.mem_edgeFinset] at he
  let ek : (boxGraph d k).edgeSet := ⟨e, heSet⟩
  let eR := boxActiveEdgeLE d hkR ek
  have hlift := liftCfg_apply_edge (boxActiveEdge_injective d R)
    (restrictActive (boxGraph d R) rho) eR
  have hedge : boxActiveEdge d R eR = edgeIncl d k e := by
    calc
      boxActiveEdge d R eR = boxActiveEdge d k ek :=
        boxActiveEdgeLE_ambient d hkR ek
      _ = edgeIncl d k e := rfl
  change liftCfg (boxActiveEdge d R)
      (restrictActive (boxGraph d R) rho) (edgeIncl d k e) =
    rho (innerEdgeLE d hkR e)
  rw [← hedge, hlift]
  rfl



theorem openSub_boxRestrict_liftActive_eq_inner
    (d : Nat) {k R : Nat} (hkR : k <= R)
    (rho : ConfigSpace (Sym2 (boxVerts d R))) :
    openSub (boxGraph d k)
        (boxRestrict d k
          (liftCfg (boxActiveEdge d R)
            (restrictActive (boxGraph d R) rho))) =
      openSub (boxGraph d k) (boxRestrictLE d hkR rho) := by
  apply ecz_openSub_eq_of_edges
  intro e he
  exact boxRestrict_liftActive_eq_on_inner_edges d hkR rho e he



theorem liftActive_mem_boxBdryConnEvent_iff
    (d : Nat) {k R : Nat} (hkR : k <= R)
    (rho : ConfigSpace (Sym2 (boxVerts d R))) :
    liftCfg (boxActiveEdge d R) (restrictActive (boxGraph d R) rho) ∈
        boxBdryConnEvent d k ↔
      rho ∈ connToBdryEventLE d hkR := by
  simp only [boxBdryConnEvent, connToBdryEventLE, Set.mem_preimage,
    Set.mem_setOf_eq]
  unfold IsingFK.ConnToBdry FK.Connected
  rw [openSub_boxRestrict_liftActive_eq_inner d hkR rho]


theorem weightedPhaseFiniteMeasure_shell_eq
    (d : Nat) {k R : Nat} (hkR : k <= R) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta hq hbeta :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k) =
      ∑ rho : ConfigSpace (Sym2 (boxVerts d R)),
        (connToBdryEventLE d hkR).indicator (fun _ => (1 : Real)) rho *
          bcProbW (boxGraph d R) (wiredBoxBoundaryGraph d R)
            (betaParams (phaseBoxCoupling phaseJ a R) beta) q rho := by
  rw [weightedPhaseFiniteMeasure_real_eq d R phaseJ a hJ q beta hq hbeta
    (boxBdryConnEvent d k) (measurableSet_boxBdryConnEvent d k)]
  change activeBCMean (boxGraph d R) (wiredBoxBoundaryGraph d R)
      (betaParams (phaseBoxCoupling phaseJ a R) beta) q
      (fun omega => (liftCfg (boxActiveEdge d R) ⁻¹'
        boxBdryConnEvent d k).indicator (fun _ => (1 : Real)) omega) = _
  rw [activeBCMean_eq_bcProbW_lift]
  · apply Finset.sum_congr rfl
    intro rho _
    congr 1
    by_cases hmem : rho ∈ connToBdryEventLE d hkR
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem]
      exact (liftActive_mem_boxBdryConnEvent_iff d hkR rho).mpr hmem
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem]
      intro hlift
      exact hmem ((liftActive_mem_boxBdryConnEvent_iff d hkR rho).mp hlift)
  · exact betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  · exact betaParams_lt_one _ beta
  · exact hq



theorem weighted_boxEvent_domain_dominated
    (d r R : Nat) (hr : 1 <= r) (hrR : r < R)
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (beta q : Real) (hbeta : 0 < beta) (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d r)))}
    (hA : IsIncreasing A) :
    (∑ rho : ConfigSpace (Sym2 (boxVerts d R)),
      (ocd_innerRestrict
        (flc_incl (box_mono d (Nat.le_of_lt hrR))) ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        bcProbW (boxGraph d R) (wiredBoxBoundaryGraph d R)
          (betaParams (boxCoupling J R) beta) q rho) <=
      ∑ eta : ConfigSpace (Sym2 (boxVerts d r)),
        A.indicator (fun _ => (1 : Real)) eta *
          bcProbW (boxGraph d r) (wiredBoxBoundaryGraph d r)
            (betaParams (boxCoupling J r) beta) q eta := by
  let hsub : box d r ⊆ box d R := box_mono d (Nat.le_of_lt hrR)
  let iota := flc_incl hsub
  let pfIn := betaParams (boxCoupling J r) beta
  let pfOut := betaParams (boxCoupling J R) beta
  have hmargin : forall x : boxVerts d r,
      ¬ boxBoundary d R (iota x) := by
    intro x hbd
    apply hbd.2
    exact box_mono d (show r <= R - 1 by omega) x.2
  have hparam : ocd_ParamCompatible iota pfIn pfOut := by
    intro e
    unfold pfIn pfOut betaParams boxCoupling iota hsub
    congr 3
    simp [ocd_innerEdge, Sym2.map_map, flc_incl_val]
  have hdom := ocd_latticeWired_inner_dominatedW
    (Sin := box d r) (Sout := box d R)
    iota (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d R) (boxBoundary d r)
    hmargin (flc_hbdryIn_box hr)
    hparam
    (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
    (betaParams_lt_one _ beta)
    (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
    (betaParams_lt_one _ beta) hq hA
  simpa [iota, hsub, pfIn, pfOut] using hdom


theorem ocd_innerRestrict_box_comp
    (d : Nat) {k r R : Nat} (hkr : k <= r) (hrR : r <= R)
    (rho : ConfigSpace (Sym2 (boxVerts d R))) :
    boxRestrictLE d hkr
        (ocd_innerRestrict (flc_incl (box_mono d hrR)) rho) =
      boxRestrictLE d (hkr.trans hrR) rho := by
  funext e
  simp [boxRestrictLE, ocd_innerRestrict, ocd_innerEdge, flc_incl,
    innerEdgeLE, boxVertInclLE, Sym2.map_map]



theorem connToBdryEventLE_outer_eq_preimage
    (d : Nat) {k r R : Nat} (hkr : k <= r) (hrR : r <= R) :
    connToBdryEventLE d (hkr.trans hrR) =
      ocd_innerRestrict (flc_incl (box_mono d hrR)) ⁻¹'
        connToBdryEventLE d hkr := by
  ext rho
  simp only [connToBdryEventLE, Set.mem_preimage, Set.mem_setOf_eq]
  rw [ocd_innerRestrict_box_comp d hkr hrR rho]


theorem weightedPhaseFiniteMeasure_shell_mono
    (d : Nat) {k r R : Nat} (hk : 1 <= k) (hkr : k <= r) (hrR : r < R)
    {P : Type*} (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) <=
      ((weightedPhaseFiniteMeasure d r phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
          Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxBdryConnEvent d k) := by
  rw [weightedPhaseFiniteMeasure_shell_eq d (hkr.trans (Nat.le_of_lt hrR))
      phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta,
    weightedPhaseFiniteMeasure_shell_eq d hkr phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta,
    connToBdryEventLE_outer_eq_preimage d hkr (Nat.le_of_lt hrR)]
  exact weighted_boxEvent_domain_dominated d r R
    (hk.trans hkr) hrR (phaseJ a) hJ beta q hbeta hq
    (isIncreasing_connToBdryEventLE d hkr)



theorem weightedPhaseWiredTheta_eq_finiteMeasure_double
    (d k : Nat) (hk : 1 <= k) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedPhaseWiredTheta d phaseJ a q beta k =
      ((weightedPhaseFiniteMeasure d (2 * k) phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
          Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxBdryConnEvent d k) := by
  rw [weightedPhaseWiredTheta_eq_centeredShellMass d k hk phaseJ a hJ
      q beta hq hbeta,
    weightedPhaseFiniteMeasure_shell_eq d (n_le_two_mul k) phaseJ a hJ
      q beta (zero_lt_one.trans_le hq) hbeta,
    centeredShellEvent_eq_connToBdryEventLE d k hk]
  rfl




theorem weightedPhaseFiniteMeasure_fixedShell_tendsto
    (d k : Nat) (hk : 1 <= k) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto
      (fun j => ((weightedPhaseFiniteMeasure d (k + j) phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
          Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxBdryConnEvent d k))
      atTop
      (nhds (weightedPhaseInfiniteShell d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta k)) := by
  let mass := fun R =>
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k)
  have hanti : Antitone (fun j => mass (k + j)) := by
    apply antitone_nat_of_succ_le
    intro j
    simpa [mass, Nat.add_assoc] using
      weightedPhaseFiniteMeasure_shell_mono d hk
        (Nat.le_add_right k j) (show k + j < k + (j + 1) by omega)
        phaseJ a hJ q beta hq hbeta
  have hbdd : BddBelow (Set.range (fun j => mass (k + j))) :=
    ⟨0, by rintro x ⟨j, rfl⟩; exact measureReal_nonneg⟩
  obtain ⟨phi, hphi, hfixed⟩ := weightedPhaseFiniteShell_tendsto_infinite
    d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
  have hphitop : Tendsto phi atTop atTop := hphi.tendsto_atTop
  obtain ⟨m0, hm0⟩ := (hphitop.eventually_ge_atTop k).exists_forall_of_atTop
  refine tendsto_of_antitone_of_subseq
    (φ := fun m => phi (m + m0) - k) ?_ hanti hbdd ?_
  · intro i j hij
    have hi : k <= phi (i + m0) := hm0 (i + m0) (by omega)
    have hj : k <= phi (j + m0) := hm0 (j + m0) (by omega)
    have hlt : phi (i + m0) < phi (j + m0) := hphi (by omega)
    change phi (i + m0) - k < phi (j + m0) - k
    omega
  · have hsub := (hfixed k).comp (tendsto_add_atTop_nat m0)
    refine hsub.congr (fun m => ?_)
    have hge : k <= phi (m + m0) := hm0 (m + m0) (by omega)
    change
      ((weightedPhaseFiniteMeasure d (phi (m + m0)) phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
          (boxBdryConnEvent d k) = mass (k + (phi (m + m0) - k))
    rw [show k + (phi (m + m0) - k) = phi (m + m0) by omega]


theorem weightedPhaseWiredTheta_succ_le
    (d n : Nat) (hn : 1 <= n) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedPhaseWiredTheta d phaseJ a q beta (n + 1) <=
      weightedPhaseWiredTheta d phaseJ a q beta n := by
  rw [weightedPhaseWiredTheta_eq_finiteMeasure_double d (n + 1)
      (by omega) phaseJ a hJ q beta hq hbeta,
    weightedPhaseWiredTheta_eq_finiteMeasure_double d n hn
      phaseJ a hJ q beta hq hbeta]
  calc
    ((weightedPhaseFiniteMeasure d (2 * (n + 1)) phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
          (boxBdryConnEvent d (n + 1))
      <= ((weightedPhaseFiniteMeasure d (2 * (n + 1)) phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
            (boxBdryConnEvent d n) :=
        measureReal_mono (boxBdryConnEvent_subset_le n (n + 1) hn (by omega))
    _ <= ((weightedPhaseFiniteMeasure d (2 * n) phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
            (boxBdryConnEvent d n) := by
      exact weightedPhaseFiniteMeasure_shell_mono d hn (n_le_two_mul n)
        (show 2 * n < 2 * (n + 1) by omega)
        phaseJ a hJ q beta hq hbeta




theorem weightedPhaseWiredTheta_tendsto_infiniteTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto (weightedPhaseWiredTheta d phaseJ a q beta) atTop
      (nhds (weightedPhaseInfiniteTheta d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta)) := by
  let theta := weightedPhaseWiredTheta d phaseJ a q beta
  let shell := weightedPhaseInfiniteShell d phaseJ a hJ q beta
    (zero_lt_one.trans_le hq) hbeta
  let tail := weightedPhaseInfiniteTheta d phaseJ a hJ q beta
    (zero_lt_one.trans_le hq) hbeta
  have hfixed : forall k, 1 <= k ->
      Tendsto
        (fun j => ((weightedPhaseFiniteMeasure d (k + j) phaseJ a hJ q beta
            (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
              (boxBdryConnEvent d k))
        atTop (nhds (shell k)) := by
    intro k hk
    exact weightedPhaseFiniteMeasure_fixedShell_tendsto
      d k hk phaseJ a hJ q beta hq hbeta
  let theta1 := fun j => theta (j + 1)
  have htheta1anti : Antitone theta1 := by
    apply antitone_nat_of_succ_le
    intro j
    exact weightedPhaseWiredTheta_succ_le d (j + 1) (by omega)
      phaseJ a hJ q beta hq hbeta
  have htheta1bdd : BddBelow (Set.range theta1) :=
    ⟨0, by
      rintro x ⟨j, rfl⟩
      change 0 <= theta (j + 1)
      unfold theta
      rw [weightedPhaseWiredTheta_eq_finiteMeasure_double d (j + 1)
        (by omega) phaseJ a hJ q beta hq hbeta]
      exact measureReal_nonneg⟩
  have htheta : Tendsto theta atTop (nhds (⨅ j, theta1 j)) :=
    (tendsto_add_atTop_iff_nat (f := theta) 1).mp
      (tendsto_atTop_ciInf htheta1anti htheta1bdd)
  let L := ⨅ j, theta1 j
  have hshell : Tendsto shell atTop (nhds tail) :=
    weightedPhaseInfiniteShell_tendsto_theta d phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta
  suffices hL : L = tail by
    have hEq : (⨅ j, theta1 j) = tail := by simpa [L] using hL
    rw [hEq] at htheta
    simpa [theta, tail] using htheta
  apply le_antisymm
  · have hLle : forall k, 1 <= k -> L <= shell k := by
      intro k hk
      let outerMass := fun j =>
        ((weightedPhaseFiniteMeasure d (k + (k + 2 * j)) phaseJ a hJ q beta
            (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
              (boxBdryConnEvent d k)
      have hindex : Tendsto (fun j => k + 2 * j) atTop atTop := by
        have hle : forall j : Nat, j <= k + 2 * j := by intro j; omega
        exact tendsto_atTop_mono hle tendsto_id
      have houter : Tendsto outerMass atTop (nhds (shell k)) := by
        have hc := (hfixed k hk).comp hindex
        simpa [outerMass, Function.comp_apply] using hc
      have hbound : forall j, theta (k + j) <= outerMass j := by
        intro j
        unfold theta outerMass
        rw [weightedPhaseWiredTheta_eq_finiteMeasure_double d (k + j)
          (by omega) phaseJ a hJ q beta hq hbeta]
        rw [show k + (k + 2 * j) = 2 * (k + j) by omega]
        exact measureReal_mono
          (boxBdryConnEvent_subset_le k (k + j) hk (Nat.le_add_right k j))
      have hkTop : Tendsto (fun j => k + j) atTop atTop :=
        tendsto_atTop_mono (fun j => Nat.le_add_left j k) tendsto_id
      have hthetaShift : Tendsto (fun j => theta (k + j)) atTop (nhds L) :=
        htheta.comp hkTop
      exact le_of_tendsto_of_tendsto' hthetaShift houter hbound
    refine ge_of_tendsto hshell ?_
    filter_upwards [eventually_ge_atTop 1] with k hk using hLle k hk
  · have hshell_le : forall k, 1 <= k -> shell k <= theta k := by
      intro k hk
      have hle : shell k <=
          ((weightedPhaseFiniteMeasure d (2 * k) phaseJ a hJ q beta
              (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) : Measure _).real
                (boxBdryConnEvent d k) := by
        refine le_of_tendsto (hfixed k hk) ?_
        filter_upwards [eventually_ge_atTop (k + 1)] with j hj
        exact weightedPhaseFiniteMeasure_shell_mono d hk
          (show k <= 2 * k by omega) (show 2 * k < k + j by omega)
          phaseJ a hJ q beta hq hbeta
      rwa [← weightedPhaseWiredTheta_eq_finiteMeasure_double d k hk
        phaseJ a hJ q beta hq hbeta] at hle
    exact le_of_tendsto_of_tendsto hshell htheta <| by
      filter_upwards [eventually_ge_atTop 1] with k hk using hshell_le k hk



theorem weightedPhaseDiagonalTailConvergence_of_one_le
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 1 <= q) :
    WeightedPhaseDiagonalTailConvergence d phaseJ hJ q := by
  intro a beta hbeta _
  exact weightedPhaseWiredTheta_tendsto_infiniteTheta
    d phaseJ a (hJ a) q beta hq hbeta

end FKSharpnessWeightedCoherentLimit
end OSSS
end StatMech
