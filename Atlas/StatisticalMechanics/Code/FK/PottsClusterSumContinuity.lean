/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PottsClusterSumProductErgodicity
import Code.FrontierB.FreeInfiniteParityTopology









open Filter MeasureTheory Set Topology

namespace StatMech.FK

open Lattice Percolation



theorem tendsto_probabilityMeasure_map_of_ae_continuousAt
    {Omega Xi I : Type*}
    [MeasurableSpace Omega] [TopologicalSpace Omega]
    [OpensMeasurableSpace Omega] [HasOuterApproxClosed Omega]
    [MeasurableSpace Xi] [TopologicalSpace Xi]
    [OpensMeasurableSpace Xi]
    {L : Filter I} [L.IsCountablyGenerated]
    (muSeq : I -> ProbabilityMeasure Omega) (mu : ProbabilityMeasure Omega)
    (hmu : Tendsto muSeq L (nhds mu))
    (f : Omega -> Xi) (hf : Measurable f)
    (hcontinuous : ∀ᵐ x ∂(mu : Measure Omega), ContinuousAt f x) :
    Tendsto (fun i => (muSeq i).map hf.aemeasurable)
      L (nhds (mu.map hf.aemeasurable)) := by
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  have hGmeas : MeasurableSet G := hG.measurableSet
  have hpreInterior : interior (f ⁻¹' G) ⊆ f ⁻¹' G := interior_subset
  have hae : f ⁻¹' G =ᵐ[(mu : Measure Omega)] interior (f ⁻¹' G) := by
    apply EventuallyLE.antisymm
    · filter_upwards [hcontinuous] with x hx hxin
      exact mem_interior_iff_mem_nhds.mpr (hx (hG.mem_nhds hxin))
    · exact hpreInterior.eventuallyLE
  rw [ProbabilityMeasure.map_apply' _ hf.aemeasurable hGmeas]
  have hopen := mu.le_liminf_measure_open_of_tendsto hmu
    (G := interior (f ⁻¹' G)) isOpen_interior
  calc
    (mu : Measure Omega) (f ⁻¹' G) =
        (mu : Measure Omega) (interior (f ⁻¹' G)) := measure_congr hae
    _ ≤ L.liminf (fun i => (muSeq i : Measure Omega)
        (interior (f ⁻¹' G))) := hopen
    _ ≤ L.liminf (fun i => (muSeq i : Measure Omega) (f ⁻¹' G)) :=
      liminf_le_liminf (Eventually.of_forall fun i => measure_mono hpreInterior)
    _ = L.liminf (fun i =>
        (((muSeq i).map hf.aemeasurable : ProbabilityMeasure Xi) : Measure Xi) G) := by
      congr 1
      funext i
      rw [ProbabilityMeasure.map_apply' _ _ hGmeas]

theorem cluster_eq_of_mem_finiteClusterEvent
    {d : Nat} (omega eta : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite)
    (heta : eta ∈ clusterEvent d
      (StatMech.FrontierB.finiteClusterNeighborhood omega x hfin :
        Set (Site d)) x (cluster d omega x)) :
    cluster d eta x = cluster d omega x := by
  ext y
  constructor
  · intro hy
    exact StatMech.FrontierB.connected_clusterEvent_imp_mem
      omega eta x y hfin heta (mem_cluster.mp hy)
  · intro hy
    have hwithin : y ∈ clusterWithin d eta
        (StatMech.FrontierB.finiteClusterNeighborhood omega x hfin :
          Set (Site d)) x := by
      rw [show clusterWithin d eta
          (StatMech.FrontierB.finiteClusterNeighborhood omega x hfin :
            Set (Site d)) x = cluster d omega x from heta]
      exact hy
    exact mem_cluster.mpr hwithin.2.2.connected



theorem continuousAt_pottsClusterSumSpin_apply_of_finite
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
    (x : Site d) (hfin : (cluster d input.1 x).Finite) :
    ContinuousAt (fun z =>
      pottsClusterSumSpin boundaryColor z.1 z.2 x) input := by
  let Uedge := clusterEvent d
    (StatMech.FrontierB.finiteClusterNeighborhood input.1 x hfin :
      Set (Site d)) x (cluster d input.1 x)
  let F : Finset (Site d) := hfin.toFinset
  let Ulabel : Set (Site d -> Fin q) :=
    cylinder (α := fun _ : Site d => Fin q) F
      {F.restrict input.2}
  let U : Set (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
    Prod.fst ⁻¹' Uedge ∩ Prod.snd ⁻¹' Ulabel
  have hUopen : IsOpen U := by
    apply IsOpen.inter
    · exact (StatMech.FrontierB.isClopen_finiteClusterEvent
        input.1 x hfin).isOpen.preimage continuous_fst
    · have hlabelClopen : IsClopen Ulabel := by
        unfold Ulabel cylinder
        apply IsClopen.preimage
        · exact isClopen_discrete _
        · exact continuous_pi fun i => continuous_apply i.1
      exact hlabelClopen.isOpen.preimage continuous_snd
  have hinputU : input ∈ U := by
    constructor
    · exact StatMech.FrontierB.clusterWithin_finiteClusterNeighborhood_eq_cluster
        input.1 x hfin
    · simp [Ulabel]
  apply (continuousAt_const : ContinuousAt (fun _ =>
      pottsClusterSumSpin boundaryColor input.1 input.2 x) input).congr
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨U, hUopen.mem_nhds hinputU, ?_⟩
  intro z hz
  have hcluster : cluster d z.1 x = cluster d input.1 x :=
    cluster_eq_of_mem_finiteClusterEvent input.1 z.1 x hfin hz.1
  have hlabels : ∀ y ∈ F, z.2 y = input.2 y := by
    intro y hy
    have hrestrict : F.restrict z.2 = F.restrict input.2 := by
      simpa [Ulabel] using hz.2
    exact congrFun hrestrict ⟨y, hy⟩
  change pottsClusterSumSpin boundaryColor input.1 input.2 x =
    pottsClusterSumSpin boundaryColor z.1 z.2 x
  unfold pottsClusterSumSpin
  rw [hcluster, dif_pos hfin, dif_pos hfin]
  exact (Finset.sum_congr rfl fun y hy =>
    hlabels y (by simpa [F] using hy)).symm



theorem continuousAt_pottsClusterSumSpin_of_allClustersFinite
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
    (hfinite : input.1 ∈ pottsAllClustersFiniteEvent d) :
    ContinuousAt (fun z =>
      pottsClusterSumSpin boundaryColor z.1 z.2) input := by
  rw [continuousAt_pi]
  intro x
  exact continuousAt_pottsClusterSumSpin_apply_of_finite
    boundaryColor input x
      ((mem_pottsAllClustersFiniteEvent_iff input.1).mp hfinite x)



theorem continuousAt_pottsClusterSumJointFactor_of_allClustersFinite
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q))
    (hfinite : input.1 ∈ pottsAllClustersFiniteEvent d) :
    ContinuousAt (pottsClusterSumJointFactor boundaryColor) input := by
  exact (continuousAt_pottsClusterSumSpin_of_allClustersFinite
    boundaryColor input hfinite).prodMk continuousAt_fst




noncomputable def pottsIIDLabelProbabilityMeasure
    (d q : Nat) [NeZero q] : ProbabilityMeasure (Site d -> Fin q) :=
  ⟨pottsIIDLabelMeasure d q, inferInstance⟩


noncomputable def pottsClusterFactorInputProbabilityMeasure
    {d q : Nat} [NeZero q]
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    ProbabilityMeasure
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
  edgeMeasure.prod (pottsIIDLabelProbabilityMeasure d q)


noncomputable def pottsClusterSumJointProbabilityMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    ProbabilityMeasure ((Site d -> Fin q) × ConfigSpace (Sym2 (Site d))) :=
  (pottsClusterFactorInputProbabilityMeasure edgeMeasure).map
    (measurable_pottsClusterSumJointFactor boundaryColor).aemeasurable





theorem tendsto_pottsClusterSumJointProbabilityMeasure
    {d q : Nat} [NeZero q] {I : Type*} {L : Filter I}
    [L.IsCountablyGenerated]
    (boundaryColor : Fin q)
    (edgeSeq : I -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hedge : Tendsto edgeSeq L (nhds edgeLimit))
    (hfinite : ∀ᵐ omega ∂(edgeLimit : Measure _),
      omega ∈ pottsAllClustersFiniteEvent d) :
    Tendsto (fun i =>
        pottsClusterSumJointProbabilityMeasure boundaryColor (edgeSeq i))
      L (nhds (pottsClusterSumJointProbabilityMeasure boundaryColor edgeLimit)) := by
  let labelMeasure := pottsIIDLabelProbabilityMeasure d q
  have hpairs : Tendsto (fun i => (edgeSeq i, labelMeasure)) L
      (nhds (edgeLimit, labelMeasure)) :=
    by
      rw [nhds_prod_eq]
      exact hedge.prodMk tendsto_const_nhds
  have hsource : Tendsto (fun i =>
      pottsClusterFactorInputProbabilityMeasure (q := q) (edgeSeq i)) L
      (nhds (pottsClusterFactorInputProbabilityMeasure (q := q) edgeLimit)) := by
    exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpairs
  have hprodFinite : ∀ᵐ input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ∂
      ((pottsClusterFactorInputProbabilityMeasure (q := q) edgeLimit :
        ProbabilityMeasure _) : Measure _),
      input.1 ∈ pottsAllClustersFiniteEvent d := by
    change ∀ᵐ input ∂(edgeLimit : Measure _).prod
      (pottsIIDLabelMeasure d q),
      input.1 ∈ pottsAllClustersFiniteEvent d
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards [hfinite] with omega homega
      exact Filter.Eventually.of_forall fun _ => homega
    · exact (measurableSet_pottsAllClustersFiniteEvent d).preimage measurable_fst
  apply tendsto_probabilityMeasure_map_of_ae_continuousAt
    (fun i => pottsClusterFactorInputProbabilityMeasure (q := q) (edgeSeq i))
    (pottsClusterFactorInputProbabilityMeasure (q := q) edgeLimit)
    hsource (pottsClusterSumJointFactor boundaryColor)
    (measurable_pottsClusterSumJointFactor boundaryColor)
  filter_upwards [hprodFinite] with input hinput
  exact continuousAt_pottsClusterSumJointFactor_of_allClustersFinite
    boundaryColor input hinput

end StatMech.FK
