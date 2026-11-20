/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumContinuity
import Code.FK.PottsInfiniteVolume
import Code.FrontierB.FreeInfiniteMultipointES





open Filter MeasureTheory Set Topology

namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



noncomputable def freeClusterColorJointPMF
    (q : Nat) [NeZero q] {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    PMF ((V -> Fin q) × ConfigSpace (Sym2 V)) :=
  (fkPMF G hp hp1 hq).bind fun omega =>
    (PMF.uniformOfFintype
      ((openSub G omega).ConnectedComponent -> Fin q)).map fun tau =>
        (IsingFK.coloring G omega tau, omega)

private theorem uniformClusterColor_map_apply
    (q : Nat) [NeZero q] (omega : ConfigSpace (Sym2 V))
    (sigma : V -> Fin q) :
    ((PMF.uniformOfFintype
      ((openSub G omega).ConnectedComponent -> Fin q)).map
        (IsingFK.coloring G omega)) sigma =
      if ConstOnOpen G omega sigma then
        ((q : ENNReal) ^ numClusters G omega)⁻¹
      else 0 := by
  classical
  by_cases hconst : ConstOnOpen G omega sigma
  · rw [if_pos hconst, PMF.map_apply]
    let tau : (openSub G omega).ConnectedComponent -> Fin q :=
      (constOnOpenEquiv G omega).symm ⟨sigma, hconst⟩
    rw [tsum_eq_single tau]
    · have htau : IsingFK.coloring G omega tau = sigma := by
        change ((constOnOpenEquiv G omega) tau).1 = sigma
        simpa [tau] using congrArg Subtype.val
          ((constOnOpenEquiv G omega).apply_symm_apply ⟨sigma, hconst⟩)
      rw [if_pos htau.symm]
      simp [Fintype.card_fun, Fintype.card_fin, numClusters]
    · intro tau' hne
      rw [if_neg]
      intro heq
      apply hne
      apply (constOnOpenEquiv G omega).injective
      apply Subtype.ext
      have htau : IsingFK.coloring G omega tau = sigma := by
        change ((constOnOpenEquiv G omega) tau).1 = sigma
        simpa [tau] using congrArg Subtype.val
          ((constOnOpenEquiv G omega).apply_symm_apply ⟨sigma, hconst⟩)
      exact heq.symm.trans htau.symm
  · rw [if_neg hconst, PMF.map_apply]
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro tau _
    rw [if_neg]
    intro heq
    apply hconst
    rw [heq]
    exact (IsingFK.compatible_iff_constOnOpen G _ _).mp
      (IsingFK.coloring_compatible G omega tau)



theorem freeClusterColorJointPMF_eq_ivp_freeJointPMF
    (q : Nat) [NeZero q] {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    freeClusterColorJointPMF G q hp hp1 hq =
      ivp_freeJointPMF G q hp hp1 hq := by
  classical
  ext z
  rcases z with ⟨sigma, omega⟩
  rw [freeClusterColorJointPMF, PMF.bind_apply, tsum_fintype]
  rw [Finset.sum_eq_single omega]
  · simp only [PMF.map_apply]
    have hpair : (∑' tau : (openSub G omega).ConnectedComponent -> Fin q,
        if sigma = IsingFK.coloring G omega tau then
          PMF.uniformOfFintype
            ((openSub G omega).ConnectedComponent -> Fin q) tau
        else 0) =
        ((PMF.uniformOfFintype
          ((openSub G omega).ConnectedComponent -> Fin q)).map
            (IsingFK.coloring G omega)) sigma := by
      rw [PMF.map_apply]
      apply tsum_congr
      intro tau
      rw [eq_comm]
      by_cases h : sigma = IsingFK.coloring G omega tau
      · simp only [if_pos h]
      · simp only [if_neg h]
    simp only [Prod.mk.injEq, and_true]
    rw [hpair, uniformClusterColor_map_apply G q omega sigma]
    simp only [ivp_freeJointPMF, PMF.ofFintype_apply, fkPMF_apply]
    rw [ivp_freeJointProb_eq_fkProb_div_pow G hq]
    by_cases hconst : ConstOnOpen G omega sigma
    · simp only [if_pos hconst]
      rw [ENNReal.ofReal_div_of_pos]
      · simp [div_eq_mul_inv]
      · positivity
    · simp [hconst]
  · intro omega' _ hne
    simp [hne, Ne.symm hne]
  · simp




noncomputable def finiteOpenComponentVertices
    (omega : ConfigSpace (Sym2 V))
    (C : (openSub G omega).ConnectedComponent) : Finset V :=
  Finset.univ.filter fun x => (openSub G omega).connectedComponentMk x = C


noncomputable def finiteOpenComponentSums
    {q : Nat} [NeZero q] (omega : ConfigSpace (Sym2 V))
    (label : V -> Fin q) :
    (openSub G omega).ConnectedComponent -> Fin q :=
  pottsBlockSums (finiteOpenComponentVertices G omega) label

private theorem finiteOpenComponentVertices_nonempty
    (omega : ConfigSpace (Sym2 V))
    (C : (openSub G omega).ConnectedComponent) :
    (finiteOpenComponentVertices G omega C).Nonempty := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | _ x =>
      exact ⟨x, by simp [finiteOpenComponentVertices]⟩

private theorem finiteOpenComponentVertices_disjoint
    (omega : ConfigSpace (Sym2 V))
    (C D : (openSub G omega).ConnectedComponent) (hCD : C ≠ D) :
    Disjoint (finiteOpenComponentVertices G omega C)
      (finiteOpenComponentVertices G omega D) := by
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  simp only [finiteOpenComponentVertices, Finset.mem_filter, Finset.mem_univ,
    true_and] at hxC hxD
  exact hCD (hxC.symm.trans hxD)



theorem finiteOpenComponentSums_law
    (q : Nat) [NeZero q] (omega : ConfigSpace (Sym2 V)) :
    Measure.map (finiteOpenComponentSums G omega)
        (PMF.uniformOfFintype (V -> Fin q)).toMeasure =
      (PMF.uniformOfFintype
        ((openSub G omega).ConnectedComponent -> Fin q)).toMeasure := by
  have h := pottsIID_blockSums_law (q := q)
    (finiteOpenComponentVertices G omega)
    (finiteOpenComponentVertices_nonempty G omega)
    (finiteOpenComponentVertices_disjoint G omega)
  rw [Measure.infinitePi_eq_pi, pottsUniformPi_eq_uniform,
    Measure.infinitePi_eq_pi, pottsUniformPi_eq_uniform] at h
  exact h


theorem finiteOpenComponentSums_pmf
    (q : Nat) [NeZero q] (omega : ConfigSpace (Sym2 V)) :
    (PMF.uniformOfFintype (V -> Fin q)).map
        (finiteOpenComponentSums G omega) =
      PMF.uniformOfFintype
        ((openSub G omega).ConnectedComponent -> Fin q) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (finiteOpenComponentSums G omega)
    (PMF.uniformOfFintype (V -> Fin q)) Measurable.of_discrete]
  exact finiteOpenComponentSums_law G q omega



theorem freeSiteClusterSumJointPMF_eq_ivp_freeJointPMF
    (q : Nat) [NeZero q] {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    (fkPMF G hp hp1 hq).bind (fun omega =>
      (PMF.uniformOfFintype (V -> Fin q)).map fun label =>
        (IsingFK.coloring G omega
          (finiteOpenComponentSums G omega label), omega)) =
      ivp_freeJointPMF G q hp hp1 hq := by
  rw [← freeClusterColorJointPMF_eq_ivp_freeJointPMF G q hp hp1 hq]
  unfold freeClusterColorJointPMF
  apply congrArg (PMF.bind (fkPMF G hp hp1 hq))
  funext omega
  change (PMF.uniformOfFintype (V -> Fin q)).map
      ((fun tau => (IsingFK.coloring G omega tau, omega)) ∘
        finiteOpenComponentSums G omega) = _
  rw [← PMF.map_comp]
  rw [finiteOpenComponentSums_pmf G q omega]




noncomputable def finiteOpenComponentRepresentative
    (omega : ConfigSpace (Sym2 V))
    (C : (openSub G omega).ConnectedComponent) : V :=
  C.out

@[simp]
theorem finiteOpenComponentRepresentative_component
    (omega : ConfigSpace (Sym2 V))
    (C : (openSub G omega).ConnectedComponent) :
    (openSub G omega).connectedComponentMk
        (finiteOpenComponentRepresentative G omega C) = C := by
  exact Quot.out_eq C


def pottsBoxJointRestrict (d n q : Nat) :
    PottsJointConfig d q ->
      ((boxVerts d n -> Fin q) × ConfigSpace (Sym2 (boxVerts d n))) :=
  fun joint =>
    (fun x => joint.1 x, fun e => joint.2 (edgeIncl d n e))

theorem measurable_pottsBoxJointRestrict (d n q : Nat) :
    Measurable (pottsBoxJointRestrict d n q) := by
  have hspin : Measurable (fun joint : PottsJointConfig d q =>
      fun x : boxVerts d n => joint.1 x) :=
    measurable_pi_lambda _ fun x =>
      (measurable_pi_apply (x : Site d)).comp measurable_fst
  have hedge : Measurable (fun joint : PottsJointConfig d q =>
      fun e : Sym2 (boxVerts d n) => joint.2 (edgeIncl d n e)) :=
    measurable_pi_lambda _ fun e =>
      (measurable_pi_apply (edgeIncl d n e)).comp measurable_snd
  exact hspin.prodMk hedge

theorem continuous_pottsBoxJointRestrict (d n q : Nat) :
    Continuous (pottsBoxJointRestrict d n q) := by
  have hspin : Continuous (fun joint : PottsJointConfig d q =>
      fun x : boxVerts d n => joint.1 x) :=
    continuous_pi fun x =>
      (continuous_apply (x : Site d)).comp continuous_fst
  have hedge : Continuous (fun joint : PottsJointConfig d q =>
      fun e : Sym2 (boxVerts d n) => joint.2 (edgeIncl d n e)) :=
    continuous_pi fun e =>
      (continuous_apply (edgeIncl d n e)).comp continuous_snd
  exact hspin.prodMk hedge

private theorem reachable_extendEdge_endpoint_mem_box
    {d : Nat} (n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) {x y : Site d}
    (hreach : (openSubgraph d (extendEdge d n omega)).Reachable x y)
    (hx : x ∈ box d n) : y ∈ box d n := by
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact hx
  | @cons u v z huv walk ih =>
      exact ih
        (StatMech.FrontierB.openSubgraph_extendEdge_adj_endpoints_mem_box
          n omega huv).2

private theorem cluster_extendEdge_finite
    {d : Nat} (n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n) :
    (cluster d (extendEdge d n omega) (x : Site d)).Finite := by
  apply (box_finite d n).subset
  intro y hy
  exact reachable_extendEdge_endpoint_mem_box n omega
    (mem_cluster.mp hy) x.2

private theorem boxComponentRepresentatives_distinct
    {d : Nat} (n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (C D : (openSub (boxGraph d n) omega).ConnectedComponent)
    (hCD : C ≠ D) :
    ¬Lattice.Connected d (extendEdge d n omega)
      ((finiteOpenComponentRepresentative (boxGraph d n) omega C : boxVerts d n) : Site d)
      ((finiteOpenComponentRepresentative (boxGraph d n) omega D : boxVerts d n) : Site d) := by
  intro hconn
  apply hCD
  rw [← finiteOpenComponentRepresentative_component (boxGraph d n) omega C,
    ← finiteOpenComponentRepresentative_component (boxGraph d n) omega D]
  apply SimpleGraph.ConnectedComponent.sound
  exact (StatMech.FrontierB.openSub_extendEdge_reachable_iff n omega
    (finiteOpenComponentRepresentative (boxGraph d n) omega C)
    (finiteOpenComponentRepresentative (boxGraph d n) omega D)).mpr hconn

set_option maxHeartbeats 3000000 in




theorem boxClusterSumSpin_law
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    Measure.map (fun label (x : boxVerts d n) =>
        pottsClusterSumSpin boundaryColor (extendEdge d n omega) label (x : Site d))
        (pottsIIDLabelMeasure d q) =
      ((PMF.uniformOfFintype
        ((openSub (boxGraph d n) omega).ConnectedComponent -> Fin q)).map
          (IsingFK.coloring (boxGraph d n) omega)).toMeasure := by
  let rep : (openSub (boxGraph d n) omega).ConnectedComponent -> Site d :=
    fun C => ((finiteOpenComponentRepresentative (boxGraph d n) omega C :
      boxVerts d n) : Site d)
  have hfinite : ∀ C, (cluster d (extendEdge d n omega) (rep C)).Finite := by
    intro C
    change (cluster d (extendEdge d n omega)
      ((finiteOpenComponentRepresentative (boxGraph d n) omega C :
        boxVerts d n) : Site d)).Finite
    exact cluster_extendEdge_finite n omega
      (finiteOpenComponentRepresentative (boxGraph d n) omega C)
  have hrep := pottsClusterSumSpin_representatives_law boundaryColor
    (extendEdge d n omega) rep hfinite
      (boxComponentRepresentatives_distinct n omega)
  have hfactor : (fun label (x : boxVerts d n) =>
      pottsClusterSumSpin boundaryColor (extendEdge d n omega) label (x : Site d)) =
      IsingFK.coloring (boxGraph d n) omega ∘
        (fun label C =>
          pottsClusterSumSpin boundaryColor (extendEdge d n omega) label (rep C)) := by
    funext label x
    rw [Function.comp_apply, IsingFK.coloring_apply]
    apply Eq.symm
    apply pottsClusterSumSpin_eq_of_connected boundaryColor
    change Lattice.Connected d (extendEdge d n omega)
      ((finiteOpenComponentRepresentative (boxGraph d n) omega
        ((openSub (boxGraph d n) omega).connectedComponentMk x) :
          boxVerts d n) : Site d) (x : Site d)
    apply (StatMech.FrontierB.openSub_extendEdge_reachable_iff n omega
      (finiteOpenComponentRepresentative (boxGraph d n) omega
        ((openSub (boxGraph d n) omega).connectedComponentMk x)) x).mp
    apply SimpleGraph.ConnectedComponent.exact
    exact finiteOpenComponentRepresentative_component (boxGraph d n) omega _
  have hinner : Measurable (fun label : Site d -> Fin q => fun C =>
      pottsClusterSumSpin boundaryColor (extendEdge d n omega) label (rep C)) :=
    measurable_pi_lambda _ fun C =>
      (measurable_pottsClusterSumSpin_apply boundaryColor (rep C)).comp
        (measurable_const.prodMk measurable_id)
  rw [hfactor, ← Measure.map_map Measurable.of_discrete hinner, hrep]
  rw [Measure.infinitePi_eq_pi, pottsUniformPi_eq_uniform]
  exact PMF.toMeasure_map (IsingFK.coloring (boxGraph d n) omega)
    (PMF.uniformOfFintype
      ((openSub (boxGraph d n) omega).ConnectedComponent -> Fin q))
      Measurable.of_discrete





noncomputable def freeESJointFiniteMeasure
    (d n q : Nat) [NeZero q] {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    ProbabilityMeasure (PottsJointConfig d q) :=
  ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure.map
      (ivp_extendJoint d n q),
    Measure.isProbabilityMeasure_map
      (ivp_measurable_extendJoint d n q).aemeasurable⟩



noncomputable def boxClusterSumJointFactor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat)
    (input : ConfigSpace (Sym2 (boxVerts d n)) × (Site d -> Fin q)) :
    (boxVerts d n -> Fin q) × ConfigSpace (Sym2 (boxVerts d n)) :=
  ((fun x => pottsClusterSumSpin boundaryColor
      (extendEdge d n input.1) input.2 (x : Site d)), input.1)

theorem measurable_boxClusterSumJointFactor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat) :
    Measurable (boxClusterSumJointFactor (d := d) boundaryColor n) := by
  have hembed : Measurable (fun input :
      ConfigSpace (Sym2 (boxVerts d n)) × (Site d -> Fin q) =>
      (extendEdge d n input.1, input.2)) :=
    ((measurable_extendEdge d n).comp measurable_fst).prodMk measurable_snd
  have hfactor := (measurable_pottsClusterSumJointFactor boundaryColor).comp hembed
  have heq : boxClusterSumJointFactor (d := d) boundaryColor n =
      pottsBoxJointRestrict d n q ∘
        pottsClusterSumJointFactor boundaryColor ∘
          (fun input => (extendEdge d n input.1, input.2)) := by
    funext input
    apply Prod.ext
    · rfl
    · funext e
      exact (extendEdge_eq_of_range n e input.1).symm
  rw [heq]
  exact (measurable_pottsBoxJointRestrict d n q).comp hfactor

theorem pottsBoxJointRestrict_clusterFactor_extendEdge
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat)
    (input : ConfigSpace (Sym2 (boxVerts d n)) × (Site d -> Fin q)) :
    pottsBoxJointRestrict d n q
        (pottsClusterSumJointFactor boundaryColor
          (extendEdge d n input.1, input.2)) =
      boxClusterSumJointFactor boundaryColor n input := by
  apply Prod.ext
  · rfl
  · funext e
    exact extendEdge_eq_of_range n e input.1



theorem freePottsJointFiniteMeasure_map_boxRestrict
    (d n q : Nat) [NeZero q] (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (freePottsJointFiniteMeasure d n q beta J hp hp1).map
        (measurable_pottsBoxJointRestrict d n q).aemeasurable =
      ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : Real) < q)).toMeasure,
        inferInstance⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pottsBoxJointRestrict d n q)
      (Measure.map (ivp_extendJoint d n q)
        (ivp_freeJointPMF (boxGraph d n) q hp hp1
          (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : Real) < q)).toMeasure) = _
  rw [Measure.map_map (measurable_pottsBoxJointRestrict d n q)
    (ivp_measurable_extendJoint d n q)]
  have hleft : pottsBoxJointRestrict d n q ∘ ivp_extendJoint d n q = id := by
    funext z
    apply Prod.ext
    · funext x
      simp [pottsBoxJointRestrict, ivp_extendJoint, ivp_extendSpin, x.2]
    · funext e
      exact extendEdge_eq_of_range n e z.2
  rw [hleft, Measure.map_id]
  change (ivp_freeJointPMF (boxGraph d n) q hp hp1 _).toMeasure =
    (ivp_freeJointPMF (boxGraph d n) q hp hp1 _).toMeasure
  rfl



theorem freeESJointFiniteMeasure_map_boxRestrict
    (d n q : Nat) [NeZero q] {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    (freeESJointFiniteMeasure d n q hp hp1 hq).map
        (measurable_pottsBoxJointRestrict d n q).aemeasurable =
      ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure,
        inferInstance⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pottsBoxJointRestrict d n q)
      (Measure.map (ivp_extendJoint d n q)
        (ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure) = _
  rw [Measure.map_map (measurable_pottsBoxJointRestrict d n q)
    (ivp_measurable_extendJoint d n q)]
  have hleft : pottsBoxJointRestrict d n q ∘ ivp_extendJoint d n q = id := by
    funext z
    apply Prod.ext
    · funext x
      simp [pottsBoxJointRestrict, ivp_extendJoint, ivp_extendSpin, x.2]
    · funext e
      exact extendEdge_eq_of_range n e z.2
  rw [hleft, Measure.map_id]
  change (ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure =
    (ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure
  rfl

set_option maxHeartbeats 3000000 in




theorem pottsClusterSumJointProbabilityMeasure_freeFinite_map_boxRestrict
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    (pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d n hp hp1 hq)).map
        (measurable_pottsBoxJointRestrict d n q).aemeasurable =
      ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure,
        inferInstance⟩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pottsBoxJointRestrict d n q)
      (Measure.map (pottsClusterSumJointFactor boundaryColor)
        ((Measure.map (extendEdge d n)
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure).prod
            (pottsIIDLabelMeasure d q))) = _
  rw [Measure.map_map (measurable_pottsBoxJointRestrict d n q)
    (measurable_pottsClusterSumJointFactor boundaryColor)]
  have hprod :
      (Measure.map (extendEdge d n)
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure).prod
          (pottsIIDLabelMeasure d q) =
        Measure.map (Prod.map (extendEdge d n) id)
          ((fkPMF (boxGraph d n) hp hp1 hq).toMeasure.prod
            (pottsIIDLabelMeasure d q)) := by
    have hid : Measure.map id (pottsIIDLabelMeasure d q) =
        pottsIIDLabelMeasure d q := Measure.map_id
    calc
      (Measure.map (extendEdge d n)
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure).prod
          (pottsIIDLabelMeasure d q) =
        (Measure.map (extendEdge d n)
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure).prod
          (Measure.map id (pottsIIDLabelMeasure d q)) := by rw [hid]
      _ = _ := Measure.map_prod_map
        (fkPMF (boxGraph d n) hp hp1 hq).toMeasure
        (pottsIIDLabelMeasure d q)
        (measurable_extendEdge d n) measurable_id
  rw [hprod, Measure.map_map]
  · have hcomp :
        (pottsBoxJointRestrict d n q ∘
            pottsClusterSumJointFactor boundaryColor) ∘
            Prod.map (extendEdge d n) id =
          boxClusterSumJointFactor (d := d) boundaryColor n := by
      funext input
      exact pottsBoxJointRestrict_clusterFactor_extendEdge
        boundaryColor n input
    rw [hcomp, ← freeClusterColorJointPMF_eq_ivp_freeJointPMF
      (boxGraph d n) q hp hp1 hq]
    apply Measure.ext_of_singleton
    rintro ⟨sigma, omegaTarget⟩
    have hsingle : MeasurableSet
        ({(sigma, omegaTarget)} : Set
          ((boxVerts d n -> Fin q) × ConfigSpace (Sym2 (boxVerts d n)))) :=
      MeasurableSet.of_discrete
    rw [Measure.map_apply (measurable_boxClusterSumJointFactor (d := d) boundaryColor n)
      hsingle]
    rw [Measure.prod_apply
      ((hsingle.preimage
        (measurable_boxClusterSumJointFactor (d := d) boundaryColor n)))]
    rw [lintegral_fintype]
    change (∑ x,
        (pottsIIDLabelMeasure d q)
          (Prod.mk x ⁻¹' boxClusterSumJointFactor (d := d) boundaryColor n ⁻¹'
            {(sigma, omegaTarget)}) *
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure {x}) =
      (freeClusterColorJointPMF (boxGraph d n) q hp hp1 hq).toMeasure
        {(sigma, omegaTarget)}
    rw [PMF.toMeasure_apply_singleton _ _ hsingle]
    unfold freeClusterColorJointPMF
    rw [PMF.bind_apply, tsum_fintype]
    have hspinMeas : Measurable (fun label : Site d -> Fin q =>
        fun x : boxVerts d n => pottsClusterSumSpin boundaryColor
          (extendEdge d n omegaTarget) label (x : Site d)) := by
      exact measurable_pi_lambda _ fun x =>
        (measurable_pottsClusterSumSpin_apply boundaryColor (x : Site d)).comp
          (measurable_const.prodMk measurable_id)
    have hsigma : MeasurableSet ({sigma} : Set (boxVerts d n -> Fin q)) :=
      MeasurableSet.of_discrete
    have hcond :
        (pottsIIDLabelMeasure d q)
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) = sigma} =
          ((PMF.uniformOfFintype
            ((openSub (boxGraph d n) omegaTarget).ConnectedComponent -> Fin q)).map
              (IsingFK.coloring (boxGraph d n) omegaTarget)) sigma := by
      calc
        (pottsIIDLabelMeasure d q)
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) = sigma} =
            Measure.map (fun label (x : boxVerts d n) =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) (pottsIIDLabelMeasure d q) {sigma} := by
              rw [Measure.map_apply hspinMeas hsigma]
              rfl
        _ = ((PMF.uniformOfFintype
              ((openSub (boxGraph d n) omegaTarget).ConnectedComponent -> Fin q)).map
                (IsingFK.coloring (boxGraph d n) omegaTarget)).toMeasure
                  {sigma} := by
              rw [boxClusterSumSpin_law boundaryColor n omegaTarget]
        _ = ((PMF.uniformOfFintype
              ((openSub (boxGraph d n) omegaTarget).ConnectedComponent -> Fin q)).map
                (IsingFK.coloring (boxGraph d n) omegaTarget)) sigma := by
              rw [PMF.toMeasure_apply_singleton _ _ hsigma]
    have hsourcePoint :
        (fkPMF (boxGraph d n) hp hp1 hq).toMeasure {omegaTarget} =
          fkPMF (boxGraph d n) hp hp1 hq omegaTarget :=
      PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete
    have hsum : (∑ omega : ConfigSpace (Sym2 (boxVerts d n)),
        (pottsIIDLabelMeasure d q)
            (Prod.mk omega ⁻¹'
              (boxClusterSumJointFactor boundaryColor n ⁻¹'
                {(sigma, omegaTarget)})) *
          (fkPMF (boxGraph d n) hp hp1 hq).toMeasure {omega}) =
        (pottsIIDLabelMeasure d q)
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) = sigma} *
          fkPMF (boxGraph d n) hp hp1 hq omegaTarget := by
      rw [Finset.sum_eq_single omegaTarget]
      · rw [hsourcePoint]
        have hsets : Prod.mk omegaTarget ⁻¹'
            (boxClusterSumJointFactor boundaryColor n ⁻¹'
              {(sigma, omegaTarget)}) =
            {label | (fun x : boxVerts d n =>
              pottsClusterSumSpin boundaryColor (extendEdge d n omegaTarget)
                label (x : Site d)) = sigma} := by
          apply Set.ext
          intro label
          simp [boxClusterSumJointFactor]
        rw [hsets]
      · intro omega _ hne
        have hempty : Prod.mk omega ⁻¹'
            (boxClusterSumJointFactor boundaryColor n ⁻¹'
              {(sigma, omegaTarget)}) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro label hlabel
          have heq : boxClusterSumJointFactor boundaryColor n (omega, label) =
              (sigma, omegaTarget) := hlabel
          exact hne (congrArg Prod.snd heq)
        rw [hempty, measure_empty, zero_mul]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    rw [hsum, hcond]
    rw [Finset.sum_eq_single omegaTarget]
    · simp only [PMF.map_apply]
      rw [mul_comm]
      congr 1
      apply tsum_congr
      intro labels
      by_cases heq : sigma = IsingFK.coloring (boxGraph d n) omegaTarget labels
      · simp [heq]
      · simp [heq]
    · intro omega _ hne
      have hmap0 :
          ((PMF.uniformOfFintype
            ((openSub (boxGraph d n) omega).ConnectedComponent -> Fin q)).map
              (fun tau => (IsingFK.coloring (boxGraph d n) omega tau, omega)))
              (sigma, omegaTarget) = 0 := by
        rw [PMF.map_apply, tsum_fintype]
        apply Finset.sum_eq_zero
        intro tau _
        simp only [ite_eq_right_iff]
        intro heq
        exact (hne (congrArg Prod.snd heq).symm).elim
      simp only [hmap0, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · exact (measurable_pottsBoxJointRestrict d n q).comp
      (measurable_pottsClusterSumJointFactor boundaryColor)
  · exact ((measurable_extendEdge d n).comp measurable_fst).prodMk
      measurable_snd




theorem isClopen_pottsSpinCylinder
    {d q : Nat} (s : Finset (Site d))
    (S : Set (∀ _x : s, Fin q)) :
    IsClopen (cylinder (α := fun _ : Site d => Fin q) s S) := by
  apply IsClopen.preimage
  · exact isClopen_discrete S
  · exact continuous_pi fun x => continuous_apply x.1


def pottsJointCylinder
    {d q : Nat} (spinSites : Finset (Site d))
    (spinSet : Set (∀ _x : spinSites, Fin q))
    (edgeSites : Finset (Sym2 (Site d)))
    (edgeSet : Set (∀ _e : edgeSites, Bool)) :
    Set (PottsJointConfig d q) :=
  cylinder (α := fun _ : Site d => Fin q) spinSites spinSet ×ˢ
    cylinder (α := fun _ : Sym2 (Site d) => Bool) edgeSites edgeSet

theorem isClopen_pottsJointCylinder
    {d q : Nat} (spinSites : Finset (Site d))
    (spinSet : Set (∀ _x : spinSites, Fin q))
    (edgeSites : Finset (Sym2 (Site d)))
    (edgeSet : Set (∀ _e : edgeSites, Bool)) :
    IsClopen (pottsJointCylinder spinSites spinSet edgeSites edgeSet) :=
  (isClopen_pottsSpinCylinder spinSites spinSet).prod
    (isClopen_cylinderEvent edgeSites edgeSet)

private theorem pottsJointCylinder_eq_boxRestrict_preimage
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

private theorem exists_box_containing_jointCylinder
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




theorem eventually_freeESJoint_eq_clusterSum_on_pottsJointCylinder
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (spinSites : Finset (Site d))
    (spinSet : Set (∀ _x : spinSites, Fin q))
    (edgeSites : Finset (Sym2 (Site d)))
    (edgeSet : Set (∀ _e : edgeSites, Bool)) :
    Filter.EventuallyEq atTop
      (fun k => pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq)
          (pottsJointCylinder spinSites spinSet edgeSites edgeSet))
      (fun k => freeESJointFiniteMeasure d (phi k) q hp hp1 hq
        (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) := by
  obtain ⟨N, hspinN, hedgeN⟩ :=
    exists_box_containing_jointCylinder (q := q) spinSites edgeSites
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
  have hC : C = R ⁻¹' T := by
    exact pottsJointCylinder_eq_boxRestrict_preimage
      spinSites spinSet edgeSites edgeSet hspin hedge
  have hrestricted :=
    (pottsClusterSumJointProbabilityMeasure_freeFinite_map_boxRestrict
      boundaryColor (phi k) hp hp1 hq).trans
      (freeESJointFiniteMeasure_map_boxRestrict
        d (phi k) q hp hp1 hq).symm
  calc
    pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq) C =
      ((pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq)).map
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable) T := by
        rw [ProbabilityMeasure.map_apply
          (pottsClusterSumJointProbabilityMeasure boundaryColor
            (freeFiniteMeasure d (phi k) hp hp1 hq))
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable
          MeasurableSet.of_discrete, ← hC]
    _ = ((freeESJointFiniteMeasure d (phi k) q hp hp1 hq).map
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable) T := by
        rw [hrestricted]
    _ = freeESJointFiniteMeasure d (phi k) q hp hp1 hq C := by
        rw [ProbabilityMeasure.map_apply
          (freeESJointFiniteMeasure d (phi k) q hp hp1 hq)
          (measurable_pottsBoxJointRestrict d (phi k) q).aemeasurable
          MeasurableSet.of_discrete, ← hC]

private theorem map_snd_restrict_fst_preimage_apply
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (mu : Measure (alpha × beta)) {A : Set alpha} {B : Set beta}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.map Prod.snd (mu.restrict (Prod.fst ⁻¹' A)) B =
      mu (A ×ˢ B) := by
  rw [Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (hB.preimage measurable_snd)]
  simp only [Set.prod_eq]
  rw [inter_comm]

private theorem map_fst_restrict_snd_preimage_apply
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (mu : Measure (alpha × beta)) {A : Set alpha} {B : Set beta}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.map Prod.fst (mu.restrict (Prod.snd ⁻¹' B)) A =
      mu (A ×ˢ B) := by
  rw [Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (hA.preimage measurable_fst)]
  rfl



theorem ProbabilityMeasure.ext_of_pottsJointCylinder
    {d q : Nat} (mu nu : ProbabilityMeasure (PottsJointConfig d q))
    (h : ∀ (spinSites : Finset (Site d))
      (spinSet : Set (∀ _x : spinSites, Fin q))
      (edgeSites : Finset (Sym2 (Site d)))
      (edgeSet : Set (∀ _e : edgeSites, Bool)),
      mu (pottsJointCylinder spinSites spinSet edgeSites edgeSet) =
        nu (pottsJointCylinder spinSites spinSet edgeSites edgeSet)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_prod
  intro A B hA hB
  have hedge (spinSites : Finset (Site d))
      (spinSet : Set (∀ _x : spinSites, Fin q)) :
      (mu : Measure _)
          (cylinder (α := fun _ : Site d => Fin q) spinSites spinSet ×ˢ B) =
        (nu : Measure _)
          (cylinder (α := fun _ : Site d => Fin q) spinSites spinSet ×ˢ B) := by
    let spinCylinder : Set (PottsConfig d q) :=
      cylinder (α := fun _ : Site d => Fin q) spinSites spinSet
    let muEdge : Measure (ConfigSpace (Sym2 (Site d))) :=
      Measure.map Prod.snd ((mu : Measure _).restrict (Prod.fst ⁻¹' spinCylinder))
    let nuEdge : Measure (ConfigSpace (Sym2 (Site d))) :=
      Measure.map Prod.snd ((nu : Measure _).restrict (Prod.fst ⁻¹' spinCylinder))
    have hspinCylinder : MeasurableSet spinCylinder := by
      exact MeasurableSet.cylinder spinSites MeasurableSet.of_discrete
    have hedgeMeasure : muEdge = nuEdge := by
      apply ext_of_generate_finite
        (measurableCylinders (fun _ : Sym2 (Site d) => Bool))
        generateFrom_measurableCylinders.symm
        isPiSystem_measurableCylinders
      · intro edgeCylinder hedgeCylinder
        rw [mem_measurableCylinders] at hedgeCylinder
        obtain ⟨edgeSites, edgeSet, hedgeSet, rfl⟩ := hedgeCylinder
        dsimp only [muEdge, nuEdge]
        rw [map_snd_restrict_fst_preimage_apply _
              hspinCylinder
              (MeasurableSet.cylinder edgeSites hedgeSet),
            map_snd_restrict_fst_preimage_apply _
              hspinCylinder
              (MeasurableSet.cylinder edgeSites hedgeSet)]
        have hh := congrArg (fun x : NNReal => (x : ENNReal))
          (h spinSites spinSet edgeSites edgeSet)
        simpa only [pottsJointCylinder,
          ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hh
      · change muEdge Set.univ = nuEdge Set.univ
        dsimp only [muEdge, nuEdge]
        rw [map_snd_restrict_fst_preimage_apply _
              hspinCylinder MeasurableSet.univ,
            map_snd_restrict_fst_preimage_apply _
              hspinCylinder MeasurableSet.univ]
        have huniv := congrArg (fun x : NNReal => (x : ENNReal))
          (h spinSites spinSet ∅ Set.univ)
        simpa [pottsJointCylinder,
          ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using huniv
    have hBmap := congrArg (fun rho : Measure (ConfigSpace (Sym2 (Site d))) => rho B)
      hedgeMeasure
    change (Measure.map Prod.snd
        ((mu : Measure _).restrict (Prod.fst ⁻¹' spinCylinder))) B =
      (Measure.map Prod.snd
        ((nu : Measure _).restrict (Prod.fst ⁻¹' spinCylinder))) B at hBmap
    rw [map_snd_restrict_fst_preimage_apply _ hspinCylinder hB,
      map_snd_restrict_fst_preimage_apply _ hspinCylinder hB] at hBmap
    exact hBmap
  let muSpin : Measure (PottsConfig d q) :=
    Measure.map Prod.fst ((mu : Measure _).restrict (Prod.snd ⁻¹' B))
  let nuSpin : Measure (PottsConfig d q) :=
    Measure.map Prod.fst ((nu : Measure _).restrict (Prod.snd ⁻¹' B))
  have hspinMeasure : muSpin = nuSpin := by
    apply ext_of_generate_finite
      (measurableCylinders (fun _ : Site d => Fin q))
      generateFrom_measurableCylinders.symm
      isPiSystem_measurableCylinders
    · intro spinCylinder hspinCylinder
      rw [mem_measurableCylinders] at hspinCylinder
      obtain ⟨spinSites, spinSet, hspinSet, rfl⟩ := hspinCylinder
      dsimp only [muSpin, nuSpin]
      rw [map_fst_restrict_snd_preimage_apply _
            (MeasurableSet.cylinder (α := fun _ : Site d => Fin q)
              spinSites hspinSet) hB,
          map_fst_restrict_snd_preimage_apply _
            (MeasurableSet.cylinder (α := fun _ : Site d => Fin q)
              spinSites hspinSet) hB]
      exact hedge spinSites spinSet
    · change muSpin Set.univ = nuSpin Set.univ
      dsimp only [muSpin, nuSpin]
      rw [map_fst_restrict_snd_preimage_apply _ MeasurableSet.univ hB,
        map_fst_restrict_snd_preimage_apply _ MeasurableSet.univ hB]
      have hfull := hedge ∅ Set.univ
      simpa using hfull
  have hAmap := congrArg (fun rho : Measure (PottsConfig d q) => rho A) hspinMeasure
  change (Measure.map Prod.fst
      ((mu : Measure _).restrict (Prod.snd ⁻¹' B))) A =
    (Measure.map Prod.fst
      ((nu : Measure _).restrict (Prod.snd ⁻¹' B))) A at hAmap
  rw [map_fst_restrict_snd_preimage_apply _ hA hB,
    map_fst_restrict_snd_preimage_apply _ hA hB] at hAmap
  exact hAmap

set_option maxHeartbeats 800000 in



theorem freeESJointWeakLimit_eq_clusterSum
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (Xi : ProbabilityMeasure (PottsJointConfig d q))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hjoint : Tendsto (fun k =>
        freeESJointFiniteMeasure d (phi k) q hp hp1 hq)
      atTop (nhds Xi))
    (hedge : Tendsto (fun k =>
        freeFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit))
    (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d) :
    Xi = pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit := by
  let factorLimit :=
    pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit
  have hfactor : Tendsto (fun k =>
      pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq))
      atTop (nhds factorLimit) := by
    exact tendsto_pottsClusterSumJointProbabilityMeasure boundaryColor
      (fun k => freeFiniteMeasure d (phi k) hp hp1 hq)
      edgeLimit hedge hfinite
  apply ProbabilityMeasure.ext_of_pottsJointCylinder
  intro spinSites spinSet edgeSites edgeSet
  let C := pottsJointCylinder spinSites spinSet edgeSites edgeSet
  have hC : IsClopen C :=
    isClopen_pottsJointCylinder spinSites spinSet edgeSites edgeSet
  have hXi := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    hjoint hC
  have hfactorMass := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    hfactor hC
  have heq := eventually_freeESJoint_eq_clusterSum_on_pottsJointCylinder
    boundaryColor hp hp1 hq phi hphi spinSites spinSet edgeSites edgeSet
  have hfactorToXi : Tendsto (fun k =>
      pottsClusterSumJointProbabilityMeasure boundaryColor
        (freeFiniteMeasure d (phi k) hp hp1 hq) C)
      atTop (nhds (Xi C)) :=
    hXi.congr' heq.symm
  simpa only [factorLimit, C] using
    tendsto_nhds_unique hfactorToXi hfactorMass



theorem freePottsJointWeakLimit_eq_clusterSum
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (hq : 0 < (q : Real))
    (phi : Nat -> Nat) (hphi : StrictMono phi)
    (Xi : ProbabilityMeasure (PottsJointConfig d q))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hjoint : Tendsto (fun k =>
        freePottsJointFiniteMeasure d (phi k) q beta J hp hp1)
      atTop (nhds Xi))
    (hedge : Tendsto (fun k =>
        freeFiniteMeasure d (phi k) hp hp1 hq)
      atTop (nhds edgeLimit))
    (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d) :
    Xi = pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit := by
  apply freeESJointWeakLimit_eq_clusterSum boundaryColor hp hp1 hq
    phi hphi Xi edgeLimit
  · simpa [freeESJointFiniteMeasure, freePottsJointFiniteMeasure] using hjoint
  · exact hedge
  · exact hfinite

end StatMech.FK
