/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumWiredWeakLimitIdentification
import Code.FK.PottsClusterSumWiredComparison








open Filter MeasureTheory Set Topology

namespace StatMech.FK

open Lattice Percolation

noncomputable section

set_option maxHeartbeats 3000000 in


theorem pottsClusterSumJointProbabilityMeasure_wiredOpenExterior_map_boxRestrict
    {d q : Nat} [NeZero q] (hd : 2 ≤ d) (n : Nat) (hn : 1 ≤ n)
    (boundaryColor : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (hq : 0 < (q : Real)) :
    (pottsClusterSumJointProbabilityMeasure boundaryColor
        (wiredOpenExteriorFiniteMeasure d n hp hp1 hq)).map
        (measurable_pottsBoxJointRestrict d n q).aemeasurable =
      ⟨(Wired.clusterColorJointPMF
        (boxGraph d n) (boxBoundary d n) boundaryColor
        beta J hp hp1).toMeasure,
        inferInstance⟩ := by
  obtain ⟨v0, hv0⟩ := IsingFK.boxBoundary_nonempty d n (by omega) hn
  let source :=
    (wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure
  let localFactor :
      ConfigSpace (Sym2 (boxVerts d n)) × (Site d → Fin q) →
        (boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n)) :=
    fun input =>
      ((fun x => pottsClusterSumSpin boundaryColor
        (extendWiredEdge d n input.1) input.2 (x : Site d)), input.1)
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pottsBoxJointRestrict d n q)
      (Measure.map (pottsClusterSumJointFactor boundaryColor)
        ((Measure.map (extendWiredEdge d n) source).prod
          (pottsIIDLabelMeasure d q))) = _
  rw [Measure.map_map (measurable_pottsBoxJointRestrict d n q)
    (measurable_pottsClusterSumJointFactor boundaryColor)]
  have hprod :
      (Measure.map (extendWiredEdge d n) source).prod
          (pottsIIDLabelMeasure d q) =
        Measure.map (Prod.map (extendWiredEdge d n) id)
          (source.prod (pottsIIDLabelMeasure d q)) := by
    have hid : Measure.map id (pottsIIDLabelMeasure d q) =
        pottsIIDLabelMeasure d q := Measure.map_id
    calc
      (Measure.map (extendWiredEdge d n) source).prod
          (pottsIIDLabelMeasure d q) =
        (Measure.map (extendWiredEdge d n) source).prod
          (Measure.map id (pottsIIDLabelMeasure d q)) := by rw [hid]
      _ = _ := Measure.map_prod_map source (pottsIIDLabelMeasure d q)
        (measurable_extendWiredEdge d n) measurable_id
  rw [hprod, Measure.map_map]
  · have hcomp :
        (pottsBoxJointRestrict d n q ∘
            pottsClusterSumJointFactor boundaryColor) ∘
            Prod.map (extendWiredEdge d n) id = localFactor := by
      funext input
      apply Prod.ext
      · funext x
        rfl
      · exact boxRestrict_extendWiredEdge d n input.1
    have hlocalMeas : Measurable localFactor := by
      rw [← hcomp]
      exact ((measurable_pottsBoxJointRestrict d n q).comp
        (measurable_pottsClusterSumJointFactor boundaryColor)).comp
          (((measurable_extendWiredEdge d n).comp measurable_fst).prodMk
            measurable_snd)
    rw [hcomp]
    apply Measure.ext_of_singleton
    rintro ⟨sigma, omegaTarget⟩
    have hsingle : MeasurableSet
        ({(sigma, omegaTarget)} : Set
          ((boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n)))) :=
      MeasurableSet.of_discrete
    rw [Measure.map_apply hlocalMeas hsingle]
    rw [Measure.prod_apply (hsingle.preimage hlocalMeas)]
    rw [lintegral_fintype]
    change (∑ omega,
        (pottsIIDLabelMeasure d q)
          (Prod.mk omega ⁻¹' localFactor ⁻¹' {(sigma, omegaTarget)}) *
          source {omega}) =
      (Wired.clusterColorJointPMF
        (boxGraph d n) (boxBoundary d n) boundaryColor
        beta J hp hp1).toMeasure
          {(sigma, omegaTarget)}
    rw [PMF.toMeasure_apply_singleton _ _ hsingle]
    unfold Wired.clusterColorJointPMF
    rw [PMF.bind_apply, tsum_fintype]
    have hspinMeas : Measurable (fun label : Site d → Fin q =>
        fun x : boxVerts d n => pottsClusterSumSpin boundaryColor
          (extendWiredEdge d n omegaTarget) label (x : Site d)) := by
      exact measurable_pi_lambda _ fun x =>
        (measurable_pottsClusterSumSpin_apply boundaryColor (x : Site d)).comp
          (measurable_const.prodMk measurable_id)
    have hsigma : MeasurableSet ({sigma} : Set (boxVerts d n → Fin q)) :=
      MeasurableSet.of_discrete
    have hcond :
        (pottsIIDLabelMeasure d q)
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor
                (extendWiredEdge d n omegaTarget) label (x : Site d)) = sigma} =
          (Wired.conditionalClusterColorPMF
            (boxGraph d n) (boxBoundary d n) boundaryColor omegaTarget) sigma := by
      calc
        (pottsIIDLabelMeasure d q)
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor
                (extendWiredEdge d n omegaTarget) label (x : Site d)) = sigma} =
            Measure.map (fun label (x : boxVerts d n) =>
              pottsClusterSumSpin boundaryColor
                (extendWiredEdge d n omegaTarget) label (x : Site d))
              (pottsIIDLabelMeasure d q) {sigma} := by
                rw [Measure.map_apply hspinMeas hsigma]
                rfl
        _ = (Wired.conditionalClusterColorPMF
              (boxGraph d n) (boxBoundary d n) boundaryColor omegaTarget).toMeasure
                {sigma} := by
              rw [Wired.extendWiredClusterSumSpin_law hd hn boundaryColor
                omegaTarget v0 hv0]
        _ = _ := PMF.toMeasure_apply_singleton _ _ hsigma
    have hsourcePoint : source {omegaTarget} =
        wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq omegaTarget :=
      PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete
    rw [Finset.sum_eq_single omegaTarget]
    · rw [hsourcePoint]
      have hsets : Prod.mk omegaTarget ⁻¹'
          (localFactor ⁻¹' {(sigma, omegaTarget)}) =
          {label | (fun x : boxVerts d n =>
            pottsClusterSumSpin boundaryColor
              (extendWiredEdge d n omegaTarget) label (x : Site d)) = sigma} := by
        ext label
        simp only [Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_setOf_eq, localFactor, Prod.mk.injEq, and_true]
      rw [hsets, hcond]
      rw [Finset.sum_eq_single omegaTarget]
      · simp only [PMF.map_apply]
        rw [mul_comm]
        congr 1
        rw [tsum_eq_single sigma]
        · simp
        · intro tau hne
          simp [Ne.symm hne]
      · intro omega _ hne
        have hmap0 :
            ((Wired.conditionalClusterColorPMF
              (boxGraph d n) (boxBoundary d n) boundaryColor omega).map
                (fun tau => (tau, omega))) (sigma, omegaTarget) = 0 := by
          rw [PMF.map_apply, tsum_fintype]
          apply Finset.sum_eq_zero
          intro tau _
          simp [hne, Ne.symm hne]
        simp only [hmap0, mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    · intro omega _ hne
      have hempty : Prod.mk omega ⁻¹'
          (localFactor ⁻¹' {(sigma, omegaTarget)}) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro label hlabel
        exact hne (congrArg Prod.snd hlabel)
      rw [hempty, measure_empty, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · exact (measurable_pottsBoxJointRestrict d n q).comp
      (measurable_pottsClusterSumJointFactor boundaryColor)
  · exact ((measurable_extendWiredEdge d n).comp measurable_fst).prodMk
      measurable_snd

private theorem wired_pottsJointCylinder_eq_boxRestrict_preimage
    {d q n : Nat} (spinSites : Finset (Site d))
    (spinSet : Set (∀ _x : spinSites, Fin q))
    (edgeSites : Finset (Sym2 (Site d)))
    (edgeSet : Set (∀ _e : edgeSites, Bool))
    (hspin : ∀ x ∈ spinSites, x ∈ box d n)
    (hedge : ∀ e ∈ edgeSites, e ∈ Set.range (edgeIncl d n)) :
    pottsJointCylinder spinSites spinSet edgeSites edgeSet =
      pottsBoxJointRestrict d n q ⁻¹'
        (pottsBoxJointRestrict d n q ''
          pottsJointCylinder spinSites spinSet edgeSites edgeSet) := by
  ext joint
  constructor
  · intro hjoint
    exact ⟨joint, hjoint, rfl⟩
  · rintro ⟨other, hother, heq⟩
    rcases hother with ⟨hotherSpin, hotherEdge⟩
    constructor
    · rw [mem_cylinder] at hotherSpin ⊢
      have hrestr := congrArg Prod.fst heq
      have heqSpin : spinSites.restrict joint.1 =
          spinSites.restrict other.1 := by
        funext x
        exact (congrFun hrestr ⟨x, hspin x x.2⟩).symm
      rw [heqSpin]
      exact hotherSpin
    · rw [mem_cylinder] at hotherEdge ⊢
      have hrestr := congrArg Prod.snd heq
      have heqEdge : edgeSites.restrict joint.2 =
          edgeSites.restrict other.2 := by
        funext e
        obtain ⟨eb, heb⟩ := hedge e e.2
        simpa only [pottsBoxJointRestrict, heb] using
          (congrFun hrestr eb).symm
      rw [heqEdge]
      exact hotherEdge

private theorem wired_exists_box_containing_jointCylinder
    {d q : Nat} (spinSites : Finset (Site d))
    (edgeSites : Finset (Sym2 (Site d))) :
    ∃ n : Nat,
      (∀ x ∈ spinSites, x ∈ box d n) ∧
      (∀ e ∈ edgeSites, e ∈ Set.range (edgeIncl d n)) := by
  classical
  let vertices : Finset (Site d) :=
    spinSites ∪ edgeSites.biUnion Sym2.toFinset
  obtain ⟨n, hn⟩ := Percolation.finite_subset_box
    (vertices : Set (Site d)) vertices.finite_toSet
  refine ⟨n, ?_, ?_⟩
  · intro x hx
    exact hn (by simp [vertices, hx])
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxv : x ∈ vertices := by
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨s(x, y), he, by simp⟩
        have hyv : y ∈ vertices := by
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨s(x, y), he, by simp⟩
        let xb : boxVerts d n := ⟨x, hn hxv⟩
        let yb : boxVerts d n := ⟨y, hn hyv⟩
        refine ⟨s(xb, yb), ?_⟩
        simp [edgeIncl, xb, yb]




theorem eventually_wiredPottsJoint_eq_openExteriorClusterSum_on_pottsJointCylinder
    {d q : Nat} [NeZero q] (hd : 2 ≤ d)
    (boundaryColor : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (hq : 0 < (q : Real))
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hphiPos : ∀ k, 1 ≤ phi k)
    (spinSites : Finset (Site d))
    (spinSet : Set (∀ _x : spinSites, Fin q))
    (edgeSites : Finset (Sym2 (Site d)))
    (edgeSet : Set (∀ _e : edgeSites, Bool)) :
    Filter.EventuallyEq atTop
      (fun k => pottsClusterSumJointProbabilityMeasure boundaryColor
        (wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq)
          (pottsJointCylinder spinSites spinSet edgeSites edgeSet))
      (fun k => wiredPottsJointFiniteMeasure d (phi k) q boundaryColor
        beta J hp.le
          (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) := by
  obtain ⟨N, hspinN, hedgeN⟩ :=
    wired_exists_box_containing_jointCylinder (q := q) spinSites edgeSites
  filter_upwards [eventually_ge_atTop N] with k hk
  have hNphi : N ≤ phi k := hk.trans (hphi.id_le k)
  let C := pottsJointCylinder spinSites spinSet edgeSites edgeSet
  let R := pottsBoxJointRestrict d (phi k) q
  let T := R '' C
  have hspin : ∀ x ∈ spinSites, x ∈ box d (phi k) := by
    intro x hx
    exact box_mono d hNphi (hspinN x hx)
  have hedge : ∀ e ∈ edgeSites,
      e ∈ Set.range (edgeIncl d (phi k)) := by
    intro e he
    obtain ⟨eb, heb⟩ := hedgeN e he
    refine ⟨innerEdgeLE d hNphi eb, ?_⟩
    rw [edgeIncl_innerEdgeLE, heb]
  have hC : C = R ⁻¹' T :=
    wired_pottsJointCylinder_eq_boxRestrict_preimage
      spinSites spinSet edgeSites edgeSet hspin hedge
  have hcluster :=
    pottsClusterSumJointProbabilityMeasure_wiredOpenExterior_map_boxRestrict
      hd (phi k) (hphiPos k) boundaryColor beta J hp hp1 hq
  obtain ⟨v0, hv0⟩ := IsingFK.boxBoundary_nonempty d (phi k) (by omega) (hphiPos k)
  have hcolor := Wired.clusterColorJointPMF_eq_ivp_wiredJointPMF
    (boxGraph d (phi k)) (boxBoundary d (phi k)) boundaryColor
      beta J hp hp1 v0 hv0
  have hwired := Wired.wiredPottsJointFiniteMeasure_map_boxRestrict
    d (phi k) q boundaryColor beta J hp.le
  have hrestricted :
      (pottsClusterSumJointProbabilityMeasure boundaryColor
        (wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq)).map
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable =
      (wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le).map
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable := by
    rw [hcluster, hcolor]
    exact hwired.symm
  calc
    pottsClusterSumJointProbabilityMeasure boundaryColor
        (wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq) C =
      ((pottsClusterSumJointProbabilityMeasure boundaryColor
        (wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq)).map
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable) T := by
        rw [ProbabilityMeasure.map_apply _
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable
          MeasurableSet.of_discrete, ← hC]
    _ = ((wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le).map
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable) T := by
        rw [hrestricted]
    _ = wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le C := by
        rw [ProbabilityMeasure.map_apply _
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable
          MeasurableSet.of_discrete, ← hC]

set_option maxHeartbeats 5000000 in



theorem wiredPottsJointWeakLimit_spinMarginal_eq_clusterSum
    {d q : Nat} [NeZero q] (hd : 2 ≤ d)
    (boundaryColor : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (hq : 1 ≤ (q : Real))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (hphiPos : ∀ k, 1 ≤ phi k)
    (Xi : ProbabilityMeasure (PottsJointConfig d q))
    (hjoint : Tendsto (fun k =>
        wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le)
      atTop (nhds Xi))
    (hedge : Tendsto (fun k =>
        wiredFiniteMeasure d (phi k) hp hp1 (zero_lt_one.trans_le hq))
      atTop (nhds (wiredInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq)))) :
    Xi.map continuous_fst.measurable.aemeasurable =
      (pottsClusterSumJointProbabilityMeasure boundaryColor
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq))).map
          continuous_fst.measurable.aemeasurable := by
  let edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  let edgeSeq : Nat -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
    fun k => wiredOpenExteriorFiniteMeasure d (phi k) hp hp1
      (zero_lt_one.trans_le hq)
  let xiSpin := Xi.map continuous_fst.measurable.aemeasurable
  let targetSpin := pottsClusterSumSpinProbabilityMeasure boundaryColor edgeLimit
  have hopen : Tendsto edgeSeq atTop (nhds edgeLimit) := by
    exact tendsto_wiredOpenExteriorFiniteMeasure hp hp1
      (zero_lt_one.trans_le hq) phi hphi edgeLimit hedge
  have hxiSpin : Tendsto (fun k =>
      (wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le).map
        continuous_fst.measurable.aemeasurable) atTop (nhds xiSpin) := by
    exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k => wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le)
      Xi hjoint continuous_fst
  have htarget : targetSpin =
      (pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit).map
        continuous_fst.measurable.aemeasurable :=
    pottsClusterSumSpinProbabilityMeasure_eq_joint_map_fst
      boundaryColor edgeLimit
  have hmeasure : xiSpin = targetSpin := by
    apply ProbabilityMeasure.ext_of_pottsSpinCylinder
    intro sites colors
    let C := cylinder (α := fun _ : Site d => Fin q) sites colors
    have hC : IsClopen C := isClopen_pottsSpinCylinder sites colors
    have hpre : Prod.fst ⁻¹' C =
        pottsJointCylinder sites colors ∅ Set.univ := by
      ext joint
      simp [C, pottsJointCylinder, cylinder]
    have hfiniteMass : Tendsto (fun k =>
        (((wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le).map
          continuous_fst.measurable.aemeasurable :
            ProbabilityMeasure (PottsConfig d q)) : Measure _).real C)
        atTop (nhds ((xiSpin : Measure _).real C)) := by
      have hNN := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
        hxiSpin hC
      simpa [Measure.real] using
        NNReal.continuous_coe.continuousAt.tendsto.comp hNN
    have heqActual : ∀ᶠ k in atTop,
        (pottsClusterSumSpinProbabilityMeasure boundaryColor (edgeSeq k) :
          Measure _).real C =
        (((wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le).map
          continuous_fst.measurable.aemeasurable :
            ProbabilityMeasure (PottsConfig d q)) : Measure _).real C := by
      have heqJoint :=
        eventually_wiredPottsJoint_eq_openExteriorClusterSum_on_pottsJointCylinder
          hd boundaryColor beta J hp hp1 (zero_lt_one.trans_le hq)
          phi hphi hphiPos sites colors ∅ Set.univ
      filter_upwards [heqJoint] with k hk
      rw [pottsClusterSumSpinProbabilityMeasure_eq_joint_map_fst]
      rw [Measure.real, Measure.real]
      rw [ProbabilityMeasure.map_apply' _
          continuous_fst.measurable.aemeasurable hC.isOpen.measurableSet,
        ProbabilityMeasure.map_apply' _
          continuous_fst.measurable.aemeasurable hC.isOpen.measurableSet,
        hpre]
      exact congrArg (fun z : NNReal => ((z : ENNReal).toReal)) hk
    have hactualMass : Tendsto (fun k =>
        (pottsClusterSumSpinProbabilityMeasure boundaryColor (edgeSeq k) :
          Measure _).real C) atTop (nhds ((xiSpin : Measure _).real C)) :=
      hfiniteMass.congr' (heqActual.mono fun _ hk => hk.symm)
    have hbound (R : Nat) (hR : 1 ≤ R)
        (hsites : ∀ x ∈ sites, x ∈ box d R) :
        abs ((xiSpin : Measure _).real C -
          (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
            boundaryColor edgeLimit R : Measure _).real C) ≤
          ∑ x ∈ sites, (edgeLimit : Measure _).real
            (wiredTruncationErrorEvent d R x) := by
      have htruncMeasure :=
        tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure_of_tendsto
          boundaryColor edgeSeq edgeLimit R hopen
      have htruncMass : Tendsto (fun k =>
          (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
            boundaryColor (edgeSeq k) R : Measure _).real C) atTop
          (nhds ((wiredTruncatedPottsClusterSumSpinProbabilityMeasure
            boundaryColor edgeLimit R : Measure _).real C)) := by
        have hNN := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
          htruncMeasure hC
        simpa [Measure.real] using
          NNReal.continuous_coe.continuousAt.tendsto.comp hNN
      have hleft := (hactualMass.sub htruncMass).abs
      have herror (x : Site d) (hx : x ∈ sites) : Tendsto (fun k =>
          (edgeSeq k : Measure _).real (wiredTruncationErrorEvent d R x))
          atTop (nhds ((edgeLimit : Measure _).real
            (wiredTruncationErrorEvent d R x))) := by
        have hinfinite : Tendsto (fun k => (edgeSeq k : Measure _).real
            (clusterInfiniteEvent d x)) atTop
            (nhds ((edgeLimit : Measure _).real
              (clusterInfiniteEvent d x))) := by
          simpa only [edgeSeq, edgeLimit] using
            ((wiredOpenExterior_clusterInfiniteEvent_real_tendsto
              hd x hp hp1 hq).comp hphi.tendsto_atTop)
        exact tendsto_wiredTruncationErrorEvent_real_of_tendsto
          hd hR x (hsites x hx)
          edgeSeq edgeLimit hopen hinfinite
      have hright : Tendsto (fun k =>
          ∑ x ∈ sites, (edgeSeq k : Measure _).real
            (wiredTruncationErrorEvent d R x)) atTop
          (nhds (∑ x ∈ sites, (edgeLimit : Measure _).real
            (wiredTruncationErrorEvent d R x))) := by
        exact tendsto_finset_sum sites fun x hx => herror x hx
      exact le_of_tendsto_of_tendsto hleft hright
        (Filter.Eventually.of_forall fun k =>
          abs_clusterSumSpin_sub_truncated_real_le
            hd boundaryColor R hR sites colors hsites (edgeSeq k))
    obtain ⟨N, hN⟩ := Percolation.finite_subset_box
      (sites : Set (Site d)) sites.finite_toSet
    have htruncTargetMeasure : Tendsto
        (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
          boundaryColor edgeLimit) atTop (nhds targetSpin) := by
      have h := tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure
        hd boundaryColor edgeLimit
      rwa [← htarget] at h
    have htruncTargetMass : Tendsto (fun R =>
        (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
          boundaryColor edgeLimit R : Measure _).real C) atTop
        (nhds ((targetSpin : Measure _).real C)) := by
      have hNN := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
        htruncTargetMeasure hC
      simpa [Measure.real] using
        NNReal.continuous_coe.continuousAt.tendsto.comp hNN
    have hleftR := ((tendsto_const_nhds : Tendsto
        (fun _ : Nat => (xiSpin : Measure _).real C) atTop
          (nhds ((xiSpin : Measure _).real C))).sub htruncTargetMass).abs
    have hrightR : Tendsto (fun R =>
        ∑ x ∈ sites, (edgeLimit : Measure _).real
          (wiredTruncationErrorEvent d R x)) atTop (nhds 0) := by
      simpa using tendsto_finset_sum sites fun x _ =>
        tendsto_wiredTruncationErrorEvent_real_zero x edgeLimit
    have heventualBound : ∀ᶠ R in atTop,
        abs ((xiSpin : Measure _).real C -
          (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
            boundaryColor edgeLimit R : Measure _).real C) ≤
          ∑ x ∈ sites, (edgeLimit : Measure _).real
            (wiredTruncationErrorEvent d R x) := by
      filter_upwards [eventually_ge_atTop (max N 1)] with R hR
      have hNR : N ≤ R := le_max_left N 1 |>.trans hR
      have hR1 : 1 ≤ R := le_max_right N 1 |>.trans hR
      exact hbound R hR1 fun x hx => box_mono d hNR (hN hx)
    have habs0 : abs ((xiSpin : Measure _).real C -
        (targetSpin : Measure _).real C) ≤ 0 :=
      le_of_tendsto_of_tendsto hleftR hrightR heventualBound
    have hreal : (xiSpin : Measure _).real C =
        (targetSpin : Measure _).real C := by
      exact sub_eq_zero.mp (abs_eq_zero.mp
        (le_antisymm habs0 (abs_nonneg _)))
    apply NNReal.eq
    have hleft : ((xiSpin C : NNReal) : Real) =
        (xiSpin : Measure _).real C := by
      rw [Measure.real,
        ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact (ENNReal.coe_toReal _).symm
    have hright : ((targetSpin C : NNReal) : Real) =
        (targetSpin : Measure _).real C := by
      rw [Measure.real,
        ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact (ENNReal.coe_toReal _).symm
    rw [hleft, hright]
    exact hreal
  change xiSpin =
    (pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit).map
      continuous_fst.measurable.aemeasurable
  exact hmeasure.trans htarget



theorem wiredPottsJointWeakLimit_eq_clusterSum_of_allClustersFinite
    {d q : Nat} [NeZero q] (hd : 2 ≤ d)
    (boundaryColor : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (hq : 0 < (q : Real))
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hphiPos : ∀ k, 1 ≤ phi k)
    (Xi : ProbabilityMeasure (PottsJointConfig d q))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hjoint : Tendsto (fun k =>
        wiredPottsJointFiniteMeasure d (phi k) q boundaryColor beta J hp.le)
      atTop (nhds Xi))
    (hedge : Tendsto (fun k =>
        wiredFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit))
    (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d) :
    Xi = pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit := by
  have hopen : Tendsto (fun k =>
      wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit) :=
    tendsto_wiredOpenExteriorFiniteMeasure hp hp1 hq phi hphi edgeLimit hedge
  have hfactor := tendsto_pottsClusterSumJointProbabilityMeasure boundaryColor
    (fun k => wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq)
    edgeLimit hopen hfinite
  apply ProbabilityMeasure.ext_of_pottsJointCylinder
  intro spinSites spinSet edgeSites edgeSet
  let C := pottsJointCylinder spinSites spinSet edgeSites edgeSet
  have hC := isClopen_pottsJointCylinder spinSites spinSet edgeSites edgeSet
  have hXi := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    hjoint hC
  have hfactorMass := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    hfactor hC
  have heq :=
    eventually_wiredPottsJoint_eq_openExteriorClusterSum_on_pottsJointCylinder
      hd boundaryColor beta J hp hp1 hq phi hphi hphiPos
      spinSites spinSet edgeSites edgeSet
  have htoXi : Tendsto (fun k =>
      pottsClusterSumJointProbabilityMeasure boundaryColor
        (wiredOpenExteriorFiniteMeasure d (phi k) hp hp1 hq) C)
      atTop (nhds (Xi C)) := hXi.congr' heq.symm
  simpa only [C] using tendsto_nhds_unique htoXi hfactorMass




theorem exists_wiredPottsFiniteMeasure_tendsto_clusterSumSpinMarginal_of_allClustersFinite
    (d q : Nat) [NeZero q] (hd : 2 ≤ d) (hq : 2 ≤ q)
    (boundaryColor : Fin q) (beta J : Real)
    (hbeta : 0 < beta) (hJ : 0 < J)
    (hfinite : ∀ᵐ omega ∂((wiredInfiniteVolume d
        (by
          apply sub_pos.mpr
          rw [Real.exp_lt_one_iff]
          exact neg_neg_of_pos (mul_pos hbeta hJ))
        (by linarith [Real.exp_pos (-(beta * J))])
        (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      Tendsto
        (fun n => wiredPottsFiniteMeasure d (phi n) q boundaryColor beta J)
        atTop
        (nhds ((pottsClusterSumJointProbabilityMeasure boundaryColor
          (wiredInfiniteVolume d
            (by
              apply sub_pos.mpr
              rw [Real.exp_lt_one_iff]
              exact neg_neg_of_pos (mul_pos hbeta hJ))
            (by linarith [Real.exp_pos (-(beta * J))])
            (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q))).map
              continuous_fst.measurable.aemeasurable)) := by
  let p : Real := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-(beta * J))]
  have hqR : (0 : Real) < q := by exact_mod_cast (show 0 < q by omega)
  let edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 hqR
  obtain ⟨Xi, mu, phi, hphi, hjoint, hspin, hfst, hsnd⟩ :=
    wiredPottsInfiniteVolume_exists d q (by omega) hq boundaryColor
      beta J hbeta hJ
  let rho : Nat → Nat := fun n => phi (n + 1)
  have hrho : StrictMono rho :=
    hphi.comp (strictMono_nat_of_lt_succ fun n => by omega)
  have hrhoPos : ∀ n, 1 ≤ rho n := by
    intro n
    exact (show n + 1 ≤ phi (n + 1) from hphi.id_le (n + 1)).trans' (by omega)
  have hjointR : Tendsto
      (fun n => wiredPottsJointFiniteMeasure d (rho n) q boundaryColor
        beta J hp.le) atTop (nhds Xi) := by
    simpa [rho, p] using hjoint.comp (tendsto_add_atTop_nat 1)
  have hspinR : Tendsto
      (fun n => wiredPottsFiniteMeasure d (rho n) q boundaryColor beta J)
      atTop (nhds mu) := by
    simpa [rho] using hspin.comp (tendsto_add_atTop_nat 1)
  have hedge0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => wiredPottsJointFiniteMeasure d (rho n) q boundaryColor
      beta J hp.le) Xi hjointR continuous_snd
  have hmapEdge : ∀ n,
      (wiredPottsJointFiniteMeasure d (rho n) q boundaryColor beta J hp.le).map
          continuous_snd.measurable.aemeasurable =
        wiredFiniteMeasure d (rho n) hp hp1 hqR := by
    intro n
    exact wiredPottsJointFiniteMeasure_map_snd d (rho n) q (by omega)
      (hrhoPos n) boundaryColor beta J hp hp1
  have hedge : Tendsto
      (fun n => wiredFiniteMeasure d (rho n) hp hp1 hqR)
      atTop (nhds edgeLimit) := by
    have hsnd' : Xi.map continuous_snd.measurable.aemeasurable = edgeLimit := by
      simpa [edgeLimit, p] using hsnd
    rw [← hsnd']
    simpa only [hmapEdge] using hedge0
  have hfinite' : ∀ᵐ omega ∂(edgeLimit : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d := by
    simpa [edgeLimit, p] using hfinite
  have hident : Xi =
      pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit :=
    wiredPottsJointWeakLimit_eq_clusterSum_of_allClustersFinite
      hd boundaryColor beta J hp hp1 hqR rho hrho hrhoPos
        Xi edgeLimit hjointR hedge hfinite'
  have hmu : mu =
      (pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit).map
        continuous_fst.measurable.aemeasurable := by
    rw [← hfst, hident]
  refine ⟨rho, hrho, ?_⟩
  rw [hmu] at hspinR
  simpa [edgeLimit, p] using hspinR




theorem exists_wiredPottsFiniteMeasure_tendsto_clusterSumSpinMarginal
    (d q : Nat) [NeZero q] (hd : 2 ≤ d) (hq : 2 ≤ q)
    (boundaryColor : Fin q) (beta J : Real)
    (hbeta : 0 < beta) (hJ : 0 < J) :
    ∃ phi : Nat → Nat, StrictMono phi ∧
      Tendsto
        (fun n => wiredPottsFiniteMeasure d (phi n) q boundaryColor beta J)
        atTop
        (nhds ((pottsClusterSumJointProbabilityMeasure boundaryColor
          (wiredInfiniteVolume d
            (by
              apply sub_pos.mpr
              rw [Real.exp_lt_one_iff]
              exact neg_neg_of_pos (mul_pos hbeta hJ))
            (by linarith [Real.exp_pos (-(beta * J))])
            (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q))).map
              continuous_fst.measurable.aemeasurable)) := by
  let p : Real := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-(beta * J))]
  have hqR : (0 : Real) < q := by
    exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : Real) ≤ q := by
    exact_mod_cast (show 1 ≤ q by omega)
  let edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 hqR
  obtain ⟨Xi, mu, phi, hphi, hjoint, hspin, hfst, hsnd⟩ :=
    wiredPottsInfiniteVolume_exists d q (by omega) hq boundaryColor
      beta J hbeta hJ
  let rho : Nat → Nat := fun n => phi (n + 1)
  have hrho : StrictMono rho :=
    hphi.comp (strictMono_nat_of_lt_succ fun n => by omega)
  have hrhoPos : ∀ n, 1 ≤ rho n := by
    intro n
    exact (show n + 1 ≤ phi (n + 1) from hphi.id_le (n + 1)).trans' (by omega)
  have hjointR : Tendsto
      (fun n => wiredPottsJointFiniteMeasure d (rho n) q boundaryColor
        beta J hp.le) atTop (nhds Xi) := by
    simpa [rho, p] using hjoint.comp (tendsto_add_atTop_nat 1)
  have hspinR : Tendsto
      (fun n => wiredPottsFiniteMeasure d (rho n) q boundaryColor beta J)
      atTop (nhds mu) := by
    simpa [rho] using hspin.comp (tendsto_add_atTop_nat 1)
  have hedge0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => wiredPottsJointFiniteMeasure d (rho n) q boundaryColor
      beta J hp.le) Xi hjointR continuous_snd
  have hmapEdge : ∀ n,
      (wiredPottsJointFiniteMeasure d (rho n) q boundaryColor beta J hp.le).map
          continuous_snd.measurable.aemeasurable =
        wiredFiniteMeasure d (rho n) hp hp1 hqR := by
    intro n
    exact wiredPottsJointFiniteMeasure_map_snd d (rho n) q (by omega)
      (hrhoPos n) boundaryColor beta J hp hp1
  have hedge : Tendsto
      (fun n => wiredFiniteMeasure d (rho n) hp hp1 hqR)
      atTop (nhds edgeLimit) := by
    have hsnd' : Xi.map continuous_snd.measurable.aemeasurable = edgeLimit := by
      simpa [edgeLimit, p] using hsnd
    rw [← hsnd']
    simpa only [hmapEdge] using hedge0
  have hidentSpin : Xi.map continuous_fst.measurable.aemeasurable =
      (pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit).map
        continuous_fst.measurable.aemeasurable :=
    wiredPottsJointWeakLimit_spinMarginal_eq_clusterSum
      hd boundaryColor beta J hp hp1 hq1 rho hrho hrhoPos
        Xi hjointR hedge
  have hmu : mu =
      (pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit).map
        continuous_fst.measurable.aemeasurable := by
    rw [← hfst, hidentSpin]
  refine ⟨rho, hrho, ?_⟩
  rw [hmu] at hspinR
  simpa [edgeLimit, p] using hspinR

end

end StatMech.FK
