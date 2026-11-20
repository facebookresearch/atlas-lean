/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumWiredTruncation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter MeasureTheory Set Topology

namespace StatMech.FK

open Lattice Percolation

noncomputable section

set_option maxHeartbeats 5000000 in





theorem continuous_pottsClusterSumSpin_wiredTruncationEdge
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat) :
    Continuous (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor
          (wiredTruncationEdge d n input.1) input.2) := by
  rw [continuous_iff_continuousAt]
  intro input
  rw [continuousAt_pi]
  intro x
  let f : (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) ->
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) := fun z =>
    (wiredTruncationEdge d n z.1, z.2)
  let g : (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) -> Fin q :=
    fun z => pottsClusterSumSpin boundaryColor z.1 z.2 x
  change ContinuousAt (g ∘ f) input
  have hf : ContinuousAt f input := by
    dsimp only [f]
    exact ((continuous_wiredTruncationEdge d n).continuousAt.comp'
      continuousAt_fst).prodMk continuousAt_snd
  rcases (cluster d (f input).1 x).finite_or_infinite with
      hfinite | hinfinite
  · exact ContinuousAt.comp (f := f)
      (continuousAt_pottsClusterSumSpin_apply_of_finite
        boundaryColor (f input) x hfinite) hf
  · have hbox : ContinuousAt (fun z :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
          boxRestrict d n z.1) input :=
      (continuous_boxRestrict d n).continuousAt.comp' continuousAt_fst
    have hsingleton : ({boxRestrict d n input.1} :
        Set (ConfigSpace (Sym2 (boxVerts d n)))) ∈
          nhds (boxRestrict d n input.1) :=
      (isOpen_discrete _).mem_nhds rfl
    have hboxMem := hbox hsingleton
    have hboxEq : ∀ᶠ z in nhds input,
        boxRestrict d n z.1 = boxRestrict d n input.1 := by
      filter_upwards [hboxMem] with z hz
      simpa only [Set.mem_singleton_iff] using hz
    apply (continuousAt_const : ContinuousAt
      (fun _ : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        boundaryColor) input).congr_of_eventuallyEq
    filter_upwards [hboxEq] with z hz
    have hedge : (f z).1 = (f input).1 := by
      dsimp only [f]
      simp only [wiredTruncationEdge, hz]
    have hzInfinite : (cluster d (f z).1 x).Infinite := by
      simpa only [hedge] using hinfinite
    change g (f z) = boundaryColor
    exact pottsClusterSumSpin_of_infinite
      boundaryColor (f z).1 (f z).2 x hzInfinite



theorem tendsto_pottsClusterSumSpin_wiredTruncationEdge
    {d q : Nat} [NeZero q] (hd : 2 <= d) (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (Site d))) (label : Site d -> Fin q) :
    Tendsto
      (fun n => pottsClusterSumSpin boundaryColor
        (wiredTruncationEdge d n omega) label)
      atTop (nhds (pottsClusterSumSpin boundaryColor omega label)) := by
  apply tendsto_pi_nhds.2
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_pottsClusterSumSpin_wiredTruncationEdge_eq
    hd boundaryColor omega label x] with n hn
  exact hn.symm

set_option maxHeartbeats 5000000 in

theorem measurable_pottsClusterSumSpin_wiredTruncationEdge
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat) :
    Measurable (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor
          (wiredTruncationEdge d n input.1) input.2) := by
  let T : (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) ->
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) := fun input =>
    (wiredTruncationEdge d n input.1, input.2)
  have hT : Measurable T :=
    ((continuous_wiredTruncationEdge d n).measurable.comp
      measurable_fst).prodMk measurable_snd
  exact (measurable_pottsClusterSumSpin boundaryColor).comp hT



noncomputable def wiredTruncatedPottsClusterSumSpinProbabilityMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (n : Nat) : ProbabilityMeasure (PottsConfig d q) :=
  (pottsClusterFactorInputProbabilityMeasure edgeMeasure).map
    (measurable_pottsClusterSumSpin_wiredTruncationEdge
      boundaryColor n).aemeasurable



theorem tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure_of_tendsto
    {d q : Nat} [NeZero q] {I : Type*} {L : Filter I}
    (boundaryColor : Fin q)
    (edgeSeq : I -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (n : Nat) (hedge : Tendsto edgeSeq L (nhds edgeLimit)) :
    Tendsto (fun i => wiredTruncatedPottsClusterSumSpinProbabilityMeasure
      boundaryColor (edgeSeq i) n) L
      (nhds (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
        boundaryColor edgeLimit n)) := by
  let labelMeasure := pottsIIDLabelProbabilityMeasure d q
  have hpairs : Tendsto (fun i => (edgeSeq i, labelMeasure)) L
      (nhds (edgeLimit, labelMeasure)) := by
    rw [nhds_prod_eq]
    exact hedge.prodMk tendsto_const_nhds
  have hsource : Tendsto (fun i =>
      pottsClusterFactorInputProbabilityMeasure (q := q) (edgeSeq i)) L
      (nhds (pottsClusterFactorInputProbabilityMeasure
        (q := q) edgeLimit)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpairs
  simpa only [wiredTruncatedPottsClusterSumSpinProbabilityMeasure] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun i => pottsClusterFactorInputProbabilityMeasure (q := q) (edgeSeq i))
      (pottsClusterFactorInputProbabilityMeasure (q := q) edgeLimit)
      hsource
      (continuous_pottsClusterSumSpin_wiredTruncationEdge boundaryColor n)



theorem tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure
    {d q : Nat} [NeZero q] (hd : 2 <= d) (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    Tendsto (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
      boundaryColor edgeMeasure) atTop
      (nhds ((pottsClusterSumJointProbabilityMeasure
        boundaryColor edgeMeasure).map
          continuous_fst.measurable.aemeasurable)) := by
  let source : ProbabilityMeasure
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
    pottsClusterFactorInputProbabilityMeasure edgeMeasure
  let f : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ->
      PottsConfig d q := fun input =>
    pottsClusterSumSpin boundaryColor input.1 input.2
  let fn : Nat -> ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ->
      PottsConfig d q := fun n input =>
    pottsClusterSumSpin boundaryColor
      (wiredTruncationEdge d n input.1) input.2
  have hf : Measurable f := measurable_pottsClusterSumSpin boundaryColor
  have hfn : forall n, Measurable (fn n) := fun n =>
    measurable_pottsClusterSumSpin_wiredTruncationEdge boundaryColor n
  let limitSpin : ProbabilityMeasure (PottsConfig d q) :=
    source.map hf.aemeasurable
  have hlimit : Tendsto
      (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
        boundaryColor edgeMeasure) atTop (nhds limitSpin) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro g
    have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := (source : Measure _))
      (F := fun n input => g (fn n input))
      (f := fun input => g (f input))
      (fun _ => norm g)
      (fun n => (g.continuous.measurable.comp (hfn n)).aestronglyMeasurable)
      (integrable_const (norm g))
      (by
        intro n
        filter_upwards with input
        exact g.norm_coe_le_norm (fn n input))
      (by
        filter_upwards with input
        exact g.continuous.continuousAt.tendsto.comp
          (tendsto_pottsClusterSumSpin_wiredTruncationEdge
            hd boundaryColor input.1 input.2))
    have hmapn (n : Nat) :
        (∫ z, g z
            ∂(wiredTruncatedPottsClusterSumSpinProbabilityMeasure
              boundaryColor edgeMeasure n : Measure _)) =
          ∫ input, g (fn n input) ∂(source : Measure _) := by
      unfold wiredTruncatedPottsClusterSumSpinProbabilityMeasure
      change (∫ z, g z ∂Measure.map (fn n) (source : Measure _)) = _
      rw [MeasureTheory.integral_map (hfn n).aemeasurable
        g.continuous.aestronglyMeasurable]
    have hmaplim :
        (∫ z, g z ∂(limitSpin : Measure _)) =
          ∫ input, g (f input) ∂(source : Measure _) := by
      dsimp only [limitSpin]
      change (∫ z, g z ∂Measure.map f (source : Measure _)) = _
      rw [MeasureTheory.integral_map hf.aemeasurable
        g.continuous.aestronglyMeasurable]
    simpa only [hmapn, hmaplim] using hdct
  have htarget : limitSpin =
      (pottsClusterSumJointProbabilityMeasure boundaryColor edgeMeasure).map
        continuous_fst.measurable.aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    calc
      Measure.map f (source : Measure _) =
          Measure.map (Prod.fst ∘ pottsClusterSumJointFactor boundaryColor)
            (source : Measure _) := rfl
      _ = Measure.map Prod.fst
          (Measure.map (pottsClusterSumJointFactor boundaryColor)
            (source : Measure _)) :=
        (Measure.map_map measurable_fst
          (measurable_pottsClusterSumJointFactor boundaryColor)).symm
  rwa [← htarget]

end

end StatMech.FK
