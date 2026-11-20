/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumWiredTranslatedBoundary
import Code.FK.PottsClusterSumWiredTruncationLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence









open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace StatMech.FK

open Lattice Percolation

noncomputable section



theorem abs_map_real_sub_map_real_le_disagreement
    {Omega Xi : Type*} [MeasurableSpace Omega] [MeasurableSpace Xi]
    [MeasurableEq Xi]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f g : Omega -> Xi) (hf : Measurable f) (hg : Measurable g)
    (A : Set Xi) (hA : MeasurableSet A) :
    abs ((Measure.map f mu).real A - (Measure.map g mu).real A) ≤
      mu.real {z | f z ≠ g z} := by
  let F := f ⁻¹' A
  let G := g ⁻¹' A
  let D := {z | f z ≠ g z}
  have hF : MeasurableSet F := hA.preimage hf
  have hG : MeasurableSet G := hA.preimage hg
  have hD : MeasurableSet D := (measurableSet_eq_fun hf hg).compl
  have hFG : F ⊆ G ∪ D := by
    intro z hz
    by_cases heq : f z = g z
    · left
      simpa [F, G, heq] using hz
    · exact Or.inr heq
  have hGF : G ⊆ F ∪ D := by
    intro z hz
    by_cases heq : f z = g z
    · left
      simpa [F, G, heq] using hz
    · exact Or.inr heq
  have hleFG : mu.real F ≤ mu.real G + mu.real D :=
    (measureReal_mono hFG).trans (measureReal_union_le G D)
  have hleGF : mu.real G ≤ mu.real F + mu.real D :=
    (measureReal_mono hGF).trans (measureReal_union_le F D)
  rw [Measure.real, Measure.real,
    Measure.map_apply hf hA, Measure.map_apply hg hA]
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    simpa only [F, G, D, Measure.real, add_comm] using hleFG
  · rw [sub_le_iff_le_add]
    simpa only [F, G, D, Measure.real, add_comm] using hleGF



theorem abs_map_real_sub_map_real_le_error
    {Omega Xi : Type*} [MeasurableSpace Omega] [MeasurableSpace Xi]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f g : Omega -> Xi) (hf : Measurable f) (hg : Measurable g)
    (A : Set Xi) (hA : MeasurableSet A) (D : Set Omega)
    (hagree : ∀ z, z ∉ D -> (f z ∈ A ↔ g z ∈ A)) :
    abs ((Measure.map f mu).real A - (Measure.map g mu).real A) ≤
      mu.real D := by
  let F := f ⁻¹' A
  let G := g ⁻¹' A
  have hFG : F ⊆ G ∪ D := by
    intro z hz
    by_cases hzD : z ∈ D
    · exact Or.inr hzD
    · exact Or.inl ((hagree z hzD).mp hz)
  have hGF : G ⊆ F ∪ D := by
    intro z hz
    by_cases hzD : z ∈ D
    · exact Or.inr hzD
    · exact Or.inl ((hagree z hzD).mpr hz)
  have hleFG : mu.real F ≤ mu.real G + mu.real D :=
    (measureReal_mono hFG).trans (measureReal_union_le G D)
  have hleGF : mu.real G ≤ mu.real F + mu.real D :=
    (measureReal_mono hGF).trans (measureReal_union_le F D)
  rw [Measure.real, Measure.real,
    Measure.map_apply hf hA, Measure.map_apply hg hA]
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    simpa only [F, G, Measure.real, add_comm] using hleFG
  · rw [sub_le_iff_le_add]
    simpa only [F, G, Measure.real, add_comm] using hleGF



theorem ProbabilityMeasure.ext_of_pottsSpinCylinder
    {d q : Nat} (mu nu : ProbabilityMeasure (PottsConfig d q))
    (h : ∀ (sites : Finset (Site d))
      (colors : Set (∀ _x : sites, Fin q)),
      mu (cylinder (α := fun _ : Site d => Fin q) sites colors) =
        nu (cylinder (α := fun _ : Site d => Fin q) sites colors)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (measurableCylinders (fun _ : Site d => Fin q))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    rw [mem_measurableCylinders] at hC
    obtain ⟨sites, colors, _, rfl⟩ := hC
    simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      congrArg (fun z : NNReal => (z : ENNReal)) (h sites colors)
  · simp



def wiredTruncationErrorEvent (d R : Nat) (x : Site d) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  wiredTruncatedInfiniteEvent d R x \ clusterInfiniteEvent d x

theorem measurableSet_wiredTruncationErrorEvent
    (d R : Nat) (x : Site d) :
    MeasurableSet (wiredTruncationErrorEvent d R x) := by
  apply MeasurableSet.diff
  · exact (measurableSet_clusterInfiniteEvent x).preimage
      (continuous_wiredTruncationEdge d R).measurable
  · exact measurableSet_clusterInfiniteEvent x



theorem tendsto_wiredTruncationErrorEvent_real_zero
    {d : Nat} (x : Site d)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    Tendsto (fun R => (edgeMeasure : Measure _).real
        (wiredTruncationErrorEvent d R x)) atTop (nhds 0) := by
  let F : Nat -> ConfigSpace (Sym2 (Site d)) -> Real := fun R omega =>
    (wiredTruncationErrorEvent d R x).indicator (fun _ => 1) omega
  have hmeas : ∀ R, Measurable (F R) := by
    intro R
    exact measurable_const.indicator
      (measurableSet_wiredTruncationErrorEvent d R x)
  have hpoint : ∀ omega, Tendsto (fun R => F R omega) atTop (nhds 0) := by
    intro omega
    rcases (cluster d omega x).finite_or_infinite with hfinite | hinfinite
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_cluster_wiredTruncationEdge_eq_of_finite
        omega x hfinite] with R hR
      simp [F, wiredTruncationErrorEvent, wiredTruncatedInfiniteEvent,
        clusterInfiniteEvent, hR, hfinite]
    · apply tendsto_const_nhds.congr'
      filter_upwards with R
      simp [F, wiredTruncationErrorEvent, clusterInfiniteEvent, hinfinite]
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (edgeMeasure : Measure _))
    (F := F) (f := fun _ => (0 : Real))
    (fun _ => (1 : Real))
    (fun R => (hmeas R).aestronglyMeasurable)
    (integrable_const 1)
    (by
      intro R
      filter_upwards with omega
      by_cases h : omega ∈ wiredTruncationErrorEvent d R x
      · simp [F, Set.indicator_of_mem h]
      · simp [F, Set.indicator_of_notMem h])
    (Filter.Eventually.of_forall hpoint)
  have hdct' : Tendsto (fun R => ∫ omega, F R omega
      ∂(edgeMeasure : Measure _)) atTop (nhds 0) := by
    simpa using hdct
  apply hdct'.congr'
  filter_upwards with R
  rw [integral_indicator_const (1 : Real)
    (measurableSet_wiredTruncationErrorEvent d R x)]
  simp [F]



theorem tendsto_wiredTruncationErrorEvent_real_of_tendsto
    {d R : Nat} {I : Type*} {L : Filter I}
    (hd : 2 ≤ d) (hR : 1 ≤ R) (x : Site d) (hx : x ∈ box d R)
    (edgeSeq : I -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hedge : Tendsto edgeSeq L (nhds edgeLimit))
    (hinfinite : Tendsto (fun i => (edgeSeq i : Measure _).real
        (clusterInfiniteEvent d x)) L
      (nhds ((edgeLimit : Measure _).real (clusterInfiniteEvent d x)))) :
    Tendsto (fun i => (edgeSeq i : Measure _).real
        (wiredTruncationErrorEvent d R x)) L
      (nhds ((edgeLimit : Measure _).real
        (wiredTruncationErrorEvent d R x))) := by
  have hsub : clusterInfiniteEvent d x ⊆ wiredTruncatedInfiniteEvent d R x := by
    intro omega hinfiniteOmega
    exact cluster_wiredTruncationEdge_infinite_of_infinite
      hd hR omega x hx hinfiniteOmega
  have htruncated : Tendsto (fun i => (edgeSeq i : Measure _).real
      (wiredTruncatedInfiniteEvent d R x)) L
      (nhds ((edgeLimit : Measure _).real
        (wiredTruncatedInfiniteEvent d R x))) := by
    have hNN := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
      hedge (isClopen_wiredTruncatedInfiniteEvent hd hR x hx)
    simpa [Measure.real] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hNN
  have hdiffSeq (i : I) :
      (edgeSeq i : Measure _).real (wiredTruncationErrorEvent d R x) =
        (edgeSeq i : Measure _).real (wiredTruncatedInfiniteEvent d R x) -
          (edgeSeq i : Measure _).real (clusterInfiniteEvent d x) := by
    exact measureReal_diff hsub (measurableSet_clusterInfiniteEvent x)
  have hdiffLimit :
      (edgeLimit : Measure _).real (wiredTruncationErrorEvent d R x) =
        (edgeLimit : Measure _).real (wiredTruncatedInfiniteEvent d R x) -
          (edgeLimit : Measure _).real (clusterInfiniteEvent d x) := by
    exact measureReal_diff hsub (measurableSet_clusterInfiniteEvent x)
  have ht := htruncated.sub hinfinite
  rw [← hdiffLimit] at ht
  exact ht.congr' (Filter.Eventually.of_forall fun i => (hdiffSeq i).symm)



def pottsSpinTruncationDisagreement
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (R : Nat)
    (sites : Finset (Site d)) :
    Set (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
  ⋃ x ∈ (sites : Set (Site d)),
    {input | pottsClusterSumSpin boundaryColor
        (wiredTruncationEdge d R input.1) input.2 x ≠
      pottsClusterSumSpin boundaryColor input.1 input.2 x}

theorem measurableSet_pottsSpinTruncationDisagreement
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (R : Nat)
    (sites : Finset (Site d)) :
    MeasurableSet (pottsSpinTruncationDisagreement boundaryColor R sites) := by
  apply MeasurableSet.biUnion sites.countable_toSet
  intro x hx
  apply MeasurableSet.compl
  apply measurableSet_eq_fun
  · exact (measurable_pi_apply x).comp
      (measurable_pottsClusterSumSpin_wiredTruncationEdge boundaryColor R)
  · exact measurable_pottsClusterSumSpin_apply boundaryColor x



theorem pottsSpinCylinder_membership_iff_of_not_disagreement
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (R : Nat)
    (sites : Finset (Site d)) (colors : Set (∀ _x : sites, Fin q))
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
    (hinput : input ∉ pottsSpinTruncationDisagreement boundaryColor R sites) :
    pottsClusterSumSpin boundaryColor input.1 input.2 ∈
        cylinder (α := fun _ : Site d => Fin q) sites colors ↔
      pottsClusterSumSpin boundaryColor
          (wiredTruncationEdge d R input.1) input.2 ∈
        cylinder (α := fun _ : Site d => Fin q) sites colors := by
  rw [mem_cylinder, mem_cylinder]
  have heq : sites.restrict
      (pottsClusterSumSpin boundaryColor input.1 input.2) =
      sites.restrict (pottsClusterSumSpin boundaryColor
        (wiredTruncationEdge d R input.1) input.2) := by
    funext x
    apply not_ne_iff.mp
    intro hne
    apply hinput
    rw [pottsSpinTruncationDisagreement]
    exact Set.mem_iUnion_of_mem x.1
      (Set.mem_iUnion_of_mem x.2 hne.symm)
  rw [heq]



theorem pottsSpinTruncationDisagreement_real_le
    {d q : Nat} [NeZero q] (hd : 2 ≤ d)
    (boundaryColor : Fin q) (R : Nat) (hR : 1 ≤ R)
    (sites : Finset (Site d))
    (hsites : ∀ x ∈ sites, x ∈ box d R)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    ((edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)).real
        (pottsSpinTruncationDisagreement boundaryColor R sites) ≤
      ∑ x ∈ sites, (edgeMeasure : Measure _).real
        (wiredTruncationErrorEvent d R x) := by
  let E := fun x : Site d =>
    {input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) |
      pottsClusterSumSpin boundaryColor
          (wiredTruncationEdge d R input.1) input.2 x ≠
        pottsClusterSumSpin boundaryColor input.1 input.2 x}
  calc
    ((edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)).real
        (pottsSpinTruncationDisagreement boundaryColor R sites) ≤
      ∑ x ∈ sites,
        ((edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)).real
          (E x) := by
            exact measureReal_biUnion_finset_le sites E
    _ ≤ ∑ x ∈ sites, (edgeMeasure : Measure _).real
        (wiredTruncationErrorEvent d R x) := by
      apply Finset.sum_le_sum
      intro x hx
      have hsub : E x ⊆ Prod.fst ⁻¹' wiredTruncationErrorEvent d R x := by
        intro input hinput
        simpa [wiredTruncationErrorEvent, wiredTruncatedInfiniteEvent,
          clusterInfiniteEvent] using
            (cluster_status_of_pottsClusterSumSpin_wiredTruncationEdge_ne
              hd hR boundaryColor input.1 input.2 x (hsites x hx) hinput)
      have hmono := measureReal_mono (μ :=
        (edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)) hsub
      have hpres := (measurePreserving_fst
        (μ := (edgeMeasure : Measure _))
        (ν := pottsIIDLabelMeasure d q)).measureReal_preimage
          (measurableSet_wiredTruncationErrorEvent d R x).nullMeasurableSet
      exact hmono.trans_eq hpres



noncomputable def pottsClusterSumSpinProbabilityMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    ProbabilityMeasure (PottsConfig d q) :=
  (pottsClusterFactorInputProbabilityMeasure edgeMeasure).map
    (measurable_pottsClusterSumSpin boundaryColor).aemeasurable

theorem pottsClusterSumSpinProbabilityMeasure_eq_joint_map_fst
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    pottsClusterSumSpinProbabilityMeasure boundaryColor edgeMeasure =
      (pottsClusterSumJointProbabilityMeasure boundaryColor edgeMeasure).map
        continuous_fst.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  let source : Measure
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
    pottsClusterFactorInputProbabilityMeasure (q := q) edgeMeasure
  calc
    Measure.map (fun input =>
        pottsClusterSumSpin boundaryColor input.1 input.2) source =
      Measure.map (Prod.fst ∘ pottsClusterSumJointFactor boundaryColor)
        source := rfl
    _ = Measure.map Prod.fst
        (Measure.map (pottsClusterSumJointFactor boundaryColor) source) :=
      (Measure.map_map measurable_fst
        (measurable_pottsClusterSumJointFactor boundaryColor)).symm



theorem abs_clusterSumSpin_sub_truncated_real_le
    {d q : Nat} [NeZero q] (hd : 2 ≤ d)
    (boundaryColor : Fin q) (R : Nat) (hR : 1 ≤ R)
    (sites : Finset (Site d)) (colors : Set (∀ _x : sites, Fin q))
    (hsites : ∀ x ∈ sites, x ∈ box d R)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    abs ((pottsClusterSumSpinProbabilityMeasure boundaryColor edgeMeasure : Measure _).real
          (cylinder (α := fun _ : Site d => Fin q) sites colors) -
        (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
          boundaryColor edgeMeasure R : Measure _).real
          (cylinder (α := fun _ : Site d => Fin q) sites colors)) ≤
      ∑ x ∈ sites, (edgeMeasure : Measure _).real
        (wiredTruncationErrorEvent d R x) := by
  let source : Measure
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
    (edgeMeasure : Measure _).prod (pottsIIDLabelMeasure d q)
  let f : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ->
      PottsConfig d q := fun input =>
    pottsClusterSumSpin boundaryColor input.1 input.2
  let g : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ->
      PottsConfig d q := fun input =>
    pottsClusterSumSpin boundaryColor
      (wiredTruncationEdge d R input.1) input.2
  let C := cylinder (α := fun _ : Site d => Fin q) sites colors
  let D := pottsSpinTruncationDisagreement boundaryColor R sites
  have hbase := abs_map_real_sub_map_real_le_error source f g
    (measurable_pottsClusterSumSpin boundaryColor)
    (measurable_pottsClusterSumSpin_wiredTruncationEdge boundaryColor R)
    C (isClopen_pottsSpinCylinder sites colors).isOpen.measurableSet D
    (fun input hinput =>
      pottsSpinCylinder_membership_iff_of_not_disagreement
        boundaryColor R sites colors input hinput)
  refine hbase.trans ?_
  exact pottsSpinTruncationDisagreement_real_le
    hd boundaryColor R hR sites hsites edgeMeasure

end

end StatMech.FK
