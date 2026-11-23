/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.Finsupp
public import MathlibExt.AlgebraicTopology.SimplicialComplex.Realization
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.CompactOpen
import MathlibExt.AlgebraicTopology.SimplicialComplex.FiniteRelativeApproximation

/-!
# Weak and metric realizations at literal vertices

The metric model consists of the original supported finite barycentric
vectors in the existing arbitrary-index L1 metric space. The forward map
keeps those coordinates. A subordinate partition constructs a continuous
return into the weak finite-face realization. Both actual inverse homotopies
are affine and fix every literal vertex. The default weak topology receives
no metric instance.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology Filter Function Set
open scoped unitInterval NNReal

universe u z

namespace PreAbstractSimplicialComplex

/-- The original normalized supported vectors in the existing arbitrary-index L1 space. -/
abbrev MetricRealization {V : Type u} (P : PreAbstractSimplicialComplex V) : Type u :=
  {a : WithLp (1 : ℝ≥0) (V →₀ ℝ) //
    ∃ x : P.Realization, WithLp.toLp (1 : ℝ≥0) x.point.weights = a}

/-- Only the separate metric realization inherits this existing subtype metric. -/
instance instMetricSpaceMetricRealization {V : Type u}
    (P : PreAbstractSimplicialComplex V) : MetricSpace (MetricRealization P) := by
  letI : Fact ((1 : ℝ≥0) ≤ 1) := ⟨le_rfl⟩
  infer_instance

end PreAbstractSimplicialComplex

namespace PreAbstractSimplicialComplex.WeakMetricConstruction

local instance : Fact ((1 : ℝ≥0) ≤ 1) := ⟨le_rfl⟩

private abbrev L1 (V : Type u) := WithLp (1 : ℝ≥0) (V →₀ ℝ)

private theorem l1_dist_on_support {V : Type u} (a b : L1 V) (s : Finset V)
    (ha : a.ofLp.support ⊆ s) (hb : b.ofLp.support ⊆ s) :
    dist a b = ∑ v ∈ s, dist (a.ofLp v) (b.ofLp v) := by
  classical
  rw [Finsupp.dist_def]
  simp only [NNReal.coe_one, inv_one, Real.rpow_one]
  rw [Finsupp.sum_of_support_subset (s := s) _
    ((Finsupp.support_zipWith).trans (Finset.union_subset ha hb)) _ (by simp)]
  simp only [Finsupp.zipWith_apply]

private theorem l1_coordinate_dist_le {V : Type u} (a b : L1 V) (v : V) :
    dist (a.ofLp v) (b.ofLp v) ≤ dist a b := by
  classical
  let s := a.ofLp.support ∪ b.ofLp.support
  rw [l1_dist_on_support a b s Finset.subset_union_left Finset.subset_union_right]
  by_cases hv : v ∈ s
  · exact Finset.single_le_sum (fun i _ => dist_nonneg) hv
  · have ha : a.ofLp v = 0 := Finsupp.notMem_support_iff.mp
      (fun h => hv (Finset.mem_union.mpr (Or.inl h)))
    have hb : b.ofLp v = 0 := Finsupp.notMem_support_iff.mp
      (fun h => hv (Finset.mem_union.mpr (Or.inr h)))
    simp only [ha, hb, dist_self]
    exact Finset.sum_nonneg (fun i _ => dist_nonneg)

private theorem l1_coordinate_continuous {V : Type u} (v : V) :
    Continuous (fun x : L1 V => x.ofLp v) := by
  have h : LipschitzWith 1 (fun x : L1 V => x.ofLp v) :=
    LipschitzWith.of_dist_le_mul (fun a b => by
      simpa only [NNReal.coe_one, one_mul] using l1_coordinate_dist_le a b v)
  exact h.continuous

/-- Only the finite carrier is assumed in this auxiliary continuity result,
not finiteness of the ambient vertex type or of the polyhedron. -/
private theorem continuous_toL1_of_finite_support {V : Type u} {X : Type z}
    [TopologicalSpace X] (f : X → V →₀ ℝ) (s : Finset V)
    (hf : ∀ x, (f x).support ⊆ s)
    (hc : ∀ v, Continuous (fun x => f x v)) :
    Continuous (fun x => WithLp.toLp (1 : ℝ≥0) (f x)) := by
  rw [continuous_iff_continuous_dist]
  have hdist : ∀ x : X × X,
      dist (WithLp.toLp (1 : ℝ≥0) (f x.1)) (WithLp.toLp (1 : ℝ≥0) (f x.2)) =
        ∑ v ∈ s, dist (f x.1 v) (f x.2 v) := by
    intro x
    exact l1_dist_on_support _ _ s (hf x.1) (hf x.2)
  simp_rw [hdist]
  exact continuous_finsetSum s (fun v _ =>
    ((hc v).comp continuous_fst).dist ((hc v).comp continuous_snd))

private def coordinateVector {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : P.Realization) : L1 V :=
  WithLp.toLp (1 : ℝ≥0) x.point.weights

private theorem coordinateVector_injective {V : Type u}
    (P : PreAbstractSimplicialComplex V) : Function.Injective (coordinateVector P) := by
  intro x y h
  apply PreAbstractSimplicialComplex.Realization.ext
  apply Convexity.StdSimplex.ext
  exact congrArg WithLp.ofLp h

/-- The normalized supported points as a subtype of the actual L1 ambient
metric. Membership derives all original barycentric/simplex conditions. -/
private abbrev MetricPolyhedron {V : Type u} (P : PreAbstractSimplicialComplex V) :=
  PreAbstractSimplicialComplex.MetricRealization P

/-- The identity on original barycentric points, changing only to the metric model. -/
private def toMetric {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : P.Realization) : MetricPolyhedron P :=
  ⟨coordinateVector P x, ⟨x, rfl⟩⟩

private theorem toMetric_weights {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : P.Realization) : (toMetric P x).val.ofLp = x.point.weights := (rfl)

/-- Underlying weak-point data only. This function is not asserted continuous
and is not the supported partition return. -/
private def pointData {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : P.Realization :=
  Classical.choose x.property

private theorem pointData_vector {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : coordinateVector P (pointData P x) = x.val :=
  Classical.choose_spec x.property

private theorem pointData_weights {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : (pointData P x).point.weights = x.val.ofLp :=
  congrArg WithLp.ofLp (pointData_vector P x)

private theorem pointData_toMetric {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : P.Realization) : pointData P (toMetric P x) = x :=
  coordinateVector_injective P (pointData_vector P (toMetric P x))

private theorem toMetric_pointData {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : toMetric P (pointData P x) = x :=
  Subtype.ext (pointData_vector P x)

private theorem coordinateVector_continuous {V : Type u}
    (P : PreAbstractSimplicialComplex V) : Continuous (coordinateVector P) := by
  rw [PreAbstractSimplicialComplex.Realization.continuous_iff]
  intro s
  exact continuous_toL1_of_finite_support
    (fun q => (PreAbstractSimplicialComplex.Realization.faceMap P s q).point.weights)
    s.val
    (fun q => PreAbstractSimplicialComplex.Realization.support_map_subtype_subset s.val q)
    (fun v => (PreAbstractSimplicialComplex.Realization.continuous_weight P v).comp
      (PreAbstractSimplicialComplex.Realization.continuous_faceMap P s))

private theorem toMetric_continuous {V : Type u} (P : PreAbstractSimplicialComplex V) :
    Continuous (toMetric P) :=
  (coordinateVector_continuous P).subtype_mk _

private def identityComparison {V : Type u} (P : PreAbstractSimplicialComplex V) :
    C(P.Realization, MetricPolyhedron P) := ⟨toMetric P, toMetric_continuous P⟩

private def coordinateStar {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) :
    Set (MetricPolyhedron P) := {x | 0 < x.val.ofLp v}

private theorem coordinateStar_open {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) : IsOpen (coordinateStar P v) :=
  isOpen_lt continuous_const ((l1_coordinate_continuous v).comp continuous_subtype_val)

private theorem coordinateStar_cover {V : Type u} (P : PreAbstractSimplicialComplex V) :
    (Set.univ : Set (MetricPolyhedron P)) ⊆ ⋃ v, coordinateStar P v := by
  intro x _
  obtain ⟨v, hv⟩ := (pointData P x).point.support_weights_nonempty
  have hne : (pointData P x).point.weights v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hpos : 0 < (pointData P x).point.weights v :=
    lt_of_le_of_ne ((pointData P x).point.nonneg v) hne.symm
  exact Set.mem_iUnion.mpr ⟨v, by
    change 0 < x.val.ofLp v
    exact (congrArg (fun w : V →₀ ℝ => w v) (pointData_weights P x)) ▸ hpos⟩

/-- Metric normality/paracompactness and the actual star cover derive a
locally supported partition. No partition is supplied as a premise. -/
private theorem existsStarPartition {V : Type u} (P : PreAbstractSimplicialComplex V) :
    ∃ ρ : PartitionOfUnity V (MetricPolyhedron P), ρ.IsSubordinate (coordinateStar P) :=
  PartitionOfUnity.exists_isSubordinate isClosed_univ (coordinateStar P)
    (coordinateStar_open P) (coordinateStar_cover P)

private def starPartition {V : Type u} (P : PreAbstractSimplicialComplex V) :
    PartitionOfUnity V (MetricPolyhedron P) := Classical.choose (existsStarPartition P)

private theorem starPartition_subordinate {V : Type u}
    (P : PreAbstractSimplicialComplex V) :
    (starPartition P).IsSubordinate (coordinateStar P) :=
  Classical.choose_spec (existsStarPartition P)

private def partitionWeights {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : V →₀ ℝ :=
  Finsupp.ofSupportFinite (fun v => starPartition P v x)
    ((starPartition P).locallyFinite.point_finite x)

private theorem partitionWeights_apply {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) (v : V) : partitionWeights P x v = starPartition P v x := rfl

private theorem partitionWeights_support {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : (partitionWeights P x).support = (starPartition P).finsupport x := by
  ext v
  simp only [Finsupp.mem_support_iff, partitionWeights_apply,
    PartitionOfUnity.mem_finsupport, Function.mem_support]

private def partitionSimplex {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : Convexity.StdSimplex ℝ V where
  weights := partitionWeights P x
  nonneg := fun v => (starPartition P).nonneg v x
  total := by
    change ∑ v ∈ (partitionWeights P x).support, partitionWeights P x v = 1
    rw [partitionWeights_support]
    simp_rw [partitionWeights_apply]
    exact (starPartition P).sum_finsupport (by simp)

private theorem partition_support_carried {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) :
    (partitionSimplex P x).weights.support ⊆ (pointData P x).point.weights.support := by
  intro v hv
  have hne : starPartition P v x ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hs : x ∈ Function.support (starPartition P v) := hne
  have hstar := starPartition_subordinate P v (subset_tsupport (starPartition P v) hs)
  have hpos : 0 < (pointData P x).point.weights v := by
    change 0 < x.val.ofLp v at hstar
    exact (congrArg (fun w : V →₀ ℝ => w v) (pointData_weights P x)).symm ▸ hstar
  exact Finsupp.mem_support_iff.mpr hpos.ne'

private def partitionReturn {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : P.Realization where
  point := partitionSimplex P x
  support_mem := (P.isRelLowerSet_faces (pointData P x).support_mem).2
    (partition_support_carried P x) (partitionSimplex P x).support_weights_nonempty

private theorem partitionReturn_weights {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) (v : V) :
    (partitionReturn P x).point.weights v = starPartition P v x := rfl

private theorem partitionReturn_support {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) :
    (partitionReturn P x).point.weights.support ⊆ (pointData P x).point.weights.support :=
  partition_support_carried P x

/-- The locally finite supports produce a finite actual vertex restriction
near each point; existing finite-coordinate continuity then proves the return. -/
private theorem partitionReturn_continuous {V : Type u}
    (P : PreAbstractSimplicialComplex V) : Continuous (partitionReturn P) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨s, hs⟩ := (starPartition P).exists_finset_nhds x
  obtain ⟨U, hbound, hU, hxU⟩ := eventually_nhds_iff.mp hs
  have hsupport : ∀ y : U, (partitionReturn P y.val).point.weights.support ⊆ s := by
    intro y v hv
    exact (hbound y.val y.property).2
      (by change starPartition P v y.val ≠ 0; exact Finsupp.mem_support_iff.mp hv)
  let g : U → PreAbstractSimplicialComplex.Realization
      (PreAbstractSimplicialComplex.restrictVertices P s) := fun y =>
    ⟨(partitionReturn P y.val).point, (partitionReturn P y.val).support_mem, hsupport y⟩
  have hg : Continuous g := by
    rw [PreAbstractSimplicialComplex.Realization.continuous_iff_weights]
    intro v
    exact (starPartition P v).continuous.comp continuous_subtype_val
  have hpU : Continuous (U.domRestrict (partitionReturn P)) :=
    (PreAbstractSimplicialComplex.Realization.continuous_inclusion
      (PreAbstractSimplicialComplex.restrictVertices_le P s)).comp hg
  exact (continuousOn_iff_continuous_domRestrict.mpr hpU x hxU).continuousAt
    (hU.mem_nhds hxU)

private def returnComparison {V : Type u} (P : PreAbstractSimplicialComplex V) :
    C(MetricPolyhedron P, P.Realization) :=
  ⟨partitionReturn P, partitionReturn_continuous P⟩

private def pointCarrier {V : Type u} (P : PreAbstractSimplicialComplex V)
    (a b : P.Realization) (h : b.point.weights.support ⊆ a.point.weights.support) :
    ContinuousMap.Homotopy (ContinuousMap.const PUnit.{1} a)
      (ContinuousMap.const PUnit.{1} b) :=
  PreAbstractSimplicialComplex.Realization.carrierHomotopy
    (ContinuousMap.const PUnit.{1} a) (ContinuousMap.const PUnit.{1} b) (fun _ => h)

private def weakCurve {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : P.Realization) : C(unitInterval, P.Realization) :=
  let H := pointCarrier P x (partitionReturn P (toMetric P x))
    (by simpa only [pointData_toMetric] using partitionReturn_support P (toMetric P x))
  { toFun := fun s => H (s, PUnit.unit)
    continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const) }

private theorem weakCurve_point {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : P.Realization) (s : unitInterval) :
    (weakCurve P x s).point = PreAbstractSimplicialComplex.Realization.segmentPoint s
      x.point (partitionReturn P (toMetric P x)).point :=
  PreAbstractSimplicialComplex.Realization.carrierHomotopy_point
    (ContinuousMap.const PUnit.{1} x)
    (ContinuousMap.const PUnit.{1} (partitionReturn P (toMetric P x)))
    (fun _ => by
      simpa only [ContinuousMap.const_apply, pointData_toMetric] using
        partitionReturn_support P (toMetric P x))
    (s, PUnit.unit)

private theorem weakCurve_continuous {V : Type u}
    (P : PreAbstractSimplicialComplex V) : Continuous (weakCurve P) := by
  rw [PreAbstractSimplicialComplex.Realization.continuous_iff]
  intro t
  let f : C(Convexity.StdSimplex ℝ t.val, P.Realization) :=
    ⟨PreAbstractSimplicialComplex.Realization.faceMap P t,
      PreAbstractSimplicialComplex.Realization.continuous_faceMap P t⟩
  let g : C(Convexity.StdSimplex ℝ t.val, P.Realization) :=
    (returnComparison P).comp ((identityComparison P).comp f)
  have h : ∀ a, (g a).point.weights.support ⊆ (f a).point.weights.support := by
    intro a
    change (partitionReturn P (toMetric P (f a))).point.weights.support ⊆
      (f a).point.weights.support
    simpa only [pointData_toMetric] using partitionReturn_support P (toMetric P (f a))
  let H := PreAbstractSimplicialComplex.Realization.carrierHomotopy f g h
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : Convexity.StdSimplex ℝ t.val × unitInterval =>
    weakCurve P (f z.1) z.2)
  have heq : (fun z : Convexity.StdSimplex ℝ t.val × unitInterval =>
      weakCurve P (f z.1) z.2) = (fun z => H (z.2, z.1)) := by
    funext z
    apply PreAbstractSimplicialComplex.Realization.ext
    rw [weakCurve_point, PreAbstractSimplicialComplex.Realization.carrierHomotopy_point]
    rfl
  rw [heq]
  exact H.continuous.comp (continuous_snd.prodMk continuous_fst)

private def weakHomotopy {V : Type u} (P : PreAbstractSimplicialComplex V) :
    ContinuousMap.Homotopy (ContinuousMap.id P.Realization)
      ((returnComparison P).comp (identityComparison P)) where
  toFun z := weakCurve P z.2 z.1
  continuous_toFun :=
    continuous_eval.comp
      (((weakCurve_continuous P).comp continuous_snd).prodMk continuous_fst)
  map_zero_left x := by
    apply PreAbstractSimplicialComplex.Realization.ext
    rw [weakCurve_point]
    exact PreAbstractSimplicialComplex.Realization.segmentPoint_zero _ _
  map_one_left x := by
    apply PreAbstractSimplicialComplex.Realization.ext
    rw [weakCurve_point]
    exact PreAbstractSimplicialComplex.Realization.segmentPoint_one _ _

/-- This is the actual metric-side affine value family. Its metric joint
continuity is derived below from the normalized-mass coordinate dictionary. -/
private def metricDeformationValue {V : Type u} (P : PreAbstractSimplicialComplex V)
    (s : unitInterval) (x : MetricPolyhedron P) : MetricPolyhedron P :=
  toMetric P (pointCarrier P (pointData P x) (partitionReturn P x)
    (partitionReturn_support P x) (s, PUnit.unit))

private theorem metricDeformation_zero {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : metricDeformationValue P 0 x = x := by
  exact (congrArg (toMetric P)
    ((pointCarrier P (pointData P x) (partitionReturn P x)
      (partitionReturn_support P x)).apply_zero PUnit.unit)).trans (toMetric_pointData P x)

private theorem metricDeformation_one {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) :
    metricDeformationValue P 1 x = toMetric P (partitionReturn P x) := by
  change toMetric P ((pointCarrier P _ _ _) (1, PUnit.unit)) = _
  rw [ContinuousMap.Homotopy.apply_one]
  rfl

private theorem metricDeformation_weights {V : Type u} (P : PreAbstractSimplicialComplex V)
    (s : unitInterval) (x : MetricPolyhedron P) (v : V) :
    (metricDeformationValue P s x).val.ofLp v =
      (1 - (s : ℝ)) * x.val.ofLp v + (s : ℝ) * starPartition P v x := by
  change (toMetric P
    ((pointCarrier P (pointData P x) (partitionReturn P x)
      (partitionReturn_support P x)) (s, PUnit.unit))).val.ofLp v = _
  rw [toMetric_weights]
  have hpoint :
      ((pointCarrier P (pointData P x) (partitionReturn P x)
        (partitionReturn_support P x)) (s, PUnit.unit)).point =
        PreAbstractSimplicialComplex.Realization.segmentPoint s
          (pointData P x).point (partitionReturn P x).point :=
    PreAbstractSimplicialComplex.Realization.carrierHomotopy_point
      (ContinuousMap.const PUnit.{1} (pointData P x))
      (ContinuousMap.const PUnit.{1} (partitionReturn P x))
      (fun _ => partitionReturn_support P x) (s, PUnit.unit)
  rw [hpoint, PreAbstractSimplicialComplex.Realization.segmentPoint_weights]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [pointData_weights, partitionReturn_weights]

/-- Coordinate continuity is reused by the proved normalized-mass metric
dictionary below; no generic topological-module instance is assumed. -/
private theorem metricDeformation_coordinate_continuous {V : Type u}
    (P : PreAbstractSimplicialComplex V) (v : V) :
    Continuous (fun z : unitInterval × MetricPolyhedron P =>
      (metricDeformationValue P z.1 z.2).val.ofLp v) := by
  simp_rw [metricDeformation_weights]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((l1_coordinate_continuous v).comp
      (continuous_subtype_val.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((starPartition P v).continuous.comp continuous_snd))

private theorem partitionReturn_vertex {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) :
    partitionReturn P (toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv)) =
      PreAbstractSimplicialComplex.Realization.vertex P v hv := by
  classical
  apply PreAbstractSimplicialComplex.Realization.ext
  have hsupport := partitionReturn_support P
    (toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv))
  rw [pointData_toMetric] at hsupport
  simpa [PreAbstractSimplicialComplex.Realization.vertex] using hsupport

private theorem weakHomotopy_vertex {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) (s : unitInterval) :
    weakHomotopy P (s, PreAbstractSimplicialComplex.Realization.vertex P v hv) =
      PreAbstractSimplicialComplex.Realization.vertex P v hv := by
  change weakCurve P (PreAbstractSimplicialComplex.Realization.vertex P v hv) s = _
  apply PreAbstractSimplicialComplex.Realization.ext
  rw [weakCurve_point, partitionReturn_vertex]
  exact PreAbstractSimplicialComplex.Realization.segmentPoint_self _ _

private theorem metricDeformation_vertex {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) (s : unitInterval) :
    metricDeformationValue P s
        (toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv)) =
      toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv) := by
  let a := PreAbstractSimplicialComplex.Realization.vertex P v hv
  let x := toMetric P a
  have hp : pointData P x = partitionReturn P x :=
    (pointData_toMetric P a).trans (partitionReturn_vertex P v hv).symm
  have hfix :
      ((pointCarrier P (pointData P x) (partitionReturn P x)
        (partitionReturn_support P x)) (s, PUnit.unit)) = pointData P x :=
    PreAbstractSimplicialComplex.Realization.carrierHomotopy_fixed
      (ContinuousMap.const PUnit.{1} (pointData P x))
      (ContinuousMap.const PUnit.{1} (partitionReturn P x))
      (fun _ => partitionReturn_support P x) (x := PUnit.unit) hp s
  change metricDeformationValue P s x = x
  exact (congrArg (toMetric P) hfix).trans (toMetric_pointData P x)

private theorem metricPoint_nonneg {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) (v : V) : 0 ≤ x.val.ofLp v := by
  rw [← pointData_weights]
  exact (pointData P x).point.nonneg v

private theorem metricPoint_total {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : MetricPolyhedron P) : x.val.ofLp.sum (fun _ r => r) = 1 := by
  rw [← pointData_weights]
  exact (pointData P x).point.total

/-- Finite positive mass at the reference point bounds all remaining mass.
This estimate uses its finite support, without a finite ambient index. -/
private theorem metric_dist_control {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x y : MetricPolyhedron P) :
    dist x y ≤ 2 * ∑ v ∈ y.val.ofLp.support, dist (x.val.ofLp v) (y.val.ofLp v) := by
  classical
  let s := y.val.ofLp.support
  let t := x.val.ofLp.support ∪ s
  have hst : s ⊆ t := Finset.subset_union_right
  have hxsum : ∑ v ∈ t, x.val.ofLp v = 1 := by
    have h := Finsupp.sum_of_support_subset (s := t) x.val.ofLp
      Finset.subset_union_left (fun (_ : V) (r : ℝ) => r) (by simp)
    exact h.symm.trans (metricPoint_total P x)
  have hysum : ∑ v ∈ s, y.val.ofLp v = 1 := metricPoint_total P y
  have hout : (∑ v ∈ t \ s, x.val.ofLp v) = 1 - ∑ v ∈ s, x.val.ofLp v := by
    have h := (Finset.sum_sdiff hst (f := fun v => x.val.ofLp v)).trans hxsum
    exact eq_sub_iff_add_eq.mpr h
  have houtside :
      (∑ v ∈ t \ s, dist (x.val.ofLp v) (y.val.ofLp v)) =
        ∑ v ∈ t \ s, x.val.ofLp v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hy : y.val.ofLp v = 0 :=
      Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hv).2
    rw [hy, Real.dist_eq, sub_zero]
    exact abs_of_nonneg (metricPoint_nonneg P x v)
  have hdelta :
      1 - (∑ v ∈ s, x.val.ofLp v) ≤ ∑ v ∈ s, dist (x.val.ofLp v) (y.val.ofLp v) := by
    rw [← hysum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro v _
    simpa only [Real.dist_eq, abs_sub_comm] using
      le_abs_self (y.val.ofLp v - x.val.ofLp v)
  change dist x.val y.val ≤ _
  calc
    dist x.val y.val = ∑ v ∈ t, dist (x.val.ofLp v) (y.val.ofLp v) :=
      l1_dist_on_support _ _ t Finset.subset_union_left Finset.subset_union_right
    _ = (∑ v ∈ t \ s, x.val.ofLp v) +
        ∑ v ∈ s, dist (x.val.ofLp v) (y.val.ofLp v) := by
      rw [← Finset.sum_sdiff hst, houtside]
    _ = (1 - ∑ v ∈ s, x.val.ofLp v) +
        ∑ v ∈ s, dist (x.val.ofLp v) (y.val.ofLp v) := by rw [hout]
    _ ≤ (∑ v ∈ s, dist (x.val.ofLp v) (y.val.ofLp v)) +
        ∑ v ∈ s, dist (x.val.ofLp v) (y.val.ofLp v) :=
      add_le_add hdelta le_rfl
    _ = 2 * ∑ v ∈ s, dist (x.val.ofLp v) (y.val.ofLp v) := (two_mul _).symm

/-- The actual metric topology on normalized finite-support points is the
induced coordinate topology. The positive total-one condition is essential. -/
private theorem metric_continuous_iff_coordinates {V : Type u}
    (P : PreAbstractSimplicialComplex V) {X : Type z} [TopologicalSpace X]
    (f : X → MetricPolyhedron P) :
    Continuous f ↔ ∀ v, Continuous (fun x => (f x).val.ofLp v) := by
  refine ⟨fun h v => (l1_coordinate_continuous v).comp (continuous_subtype_val.comp h), ?_⟩
  intro h
  rw [Metric.continuous_iff']
  intro a eps heps
  have hc : Continuous (fun x : X =>
      2 * ∑ v ∈ (f a).val.ofLp.support, dist ((f x).val.ofLp v) ((f a).val.ofLp v)) :=
    continuous_const.mul (continuous_finsetSum _ (fun v _ => (h v).dist continuous_const))
  have hsmall : ∀ᶠ x in 𝓝 a,
      2 * ∑ v ∈ (f a).val.ofLp.support, dist ((f x).val.ofLp v) ((f a).val.ofLp v) < eps :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa using heps))
  filter_upwards [hsmall] with x hx
  exact (metric_dist_control P (f x) (f a)).trans_lt hx

private theorem metricDeformation_continuous {V : Type u}
    (P : PreAbstractSimplicialComplex V) :
    Continuous (fun z : unitInterval × MetricPolyhedron P =>
      metricDeformationValue P z.1 z.2) :=
  (metric_continuous_iff_coordinates P _).mpr
    (metricDeformation_coordinate_continuous P)

private def metricHomotopy {V : Type u} (P : PreAbstractSimplicialComplex V) :
    ContinuousMap.Homotopy (ContinuousMap.id (MetricPolyhedron P))
      ((identityComparison P).comp (returnComparison P)) where
  toFun z := metricDeformationValue P z.1 z.2
  continuous_toFun := metricDeformation_continuous P
  map_zero_left x := metricDeformation_zero P x
  map_one_left x := metricDeformation_one P x

private theorem metricHomotopy_vertex {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) (s : unitInterval) :
    metricHomotopy P (s, toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv)) =
      toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv) :=
  metricDeformation_vertex P v hv s

/-- Actual two-sided maps and jointly continuous affine homotopies; the
homotopies are the constructed families, not selected existential inverses. -/
private def weakMetricHomotopyEquiv {V : Type u} (P : PreAbstractSimplicialComplex V) :
    ContinuousMap.HomotopyEquiv P.Realization (MetricPolyhedron P) where
  toFun := identityComparison P
  invFun := returnComparison P
  left_inv := ⟨(weakHomotopy P).symm⟩
  right_inv := ⟨(metricHomotopy P).symm⟩

private def weakInverseHomotopyRel {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) :
    ContinuousMap.HomotopyRel
      ((returnComparison P).comp (identityComparison P))
      (ContinuousMap.id P.Realization)
      {PreAbstractSimplicialComplex.Realization.vertex P v hv} where
  toHomotopy := (weakHomotopy P).symm
  prop' s x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    change weakHomotopy P
      (unitInterval.symm s, PreAbstractSimplicialComplex.Realization.vertex P v hv) = _
    rw [weakHomotopy_vertex]
    change PreAbstractSimplicialComplex.Realization.vertex P v hv =
      partitionReturn P (toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv))
    exact (partitionReturn_vertex P v hv).symm

private def metricInverseHomotopyRel {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) :
    ContinuousMap.HomotopyRel
      ((identityComparison P).comp (returnComparison P))
      (ContinuousMap.id (MetricPolyhedron P))
      {toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv)} where
  toHomotopy := (metricHomotopy P).symm
  prop' s x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    change metricHomotopy P
      (unitInterval.symm s, toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv)) = _
    rw [metricHomotopy_vertex]
    change toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv) =
      toMetric P (partitionReturn P
        (toMetric P (PreAbstractSimplicialComplex.Realization.vertex P v hv)))
    exact congrArg (toMetric P) (partitionReturn_vertex P v hv).symm

end PreAbstractSimplicialComplex.WeakMetricConstruction

namespace PreAbstractSimplicialComplex

/-- The continuous identity on barycentric points into the separate metric model. -/
def Realization.toMetric {V : Type u} (P : PreAbstractSimplicialComplex V) :
    C(P.Realization, MetricRealization P) :=
  WeakMetricConstruction.identityComparison P

/-- The forward map preserves the entire original barycentric vector. -/
theorem Realization.toMetric_weights {V : Type u} (P : PreAbstractSimplicialComplex V)
    (x : P.Realization) :
    (Realization.toMetric P x).val.ofLp = x.point.weights :=
  WeakMetricConstruction.toMetric_weights P x

/-- The actual supported partition return into the weak finite-face realization. -/
def MetricRealization.toWeak {V : Type u} (P : PreAbstractSimplicialComplex V) :
    C(MetricRealization P, P.Realization) :=
  WeakMetricConstruction.returnComparison P

/-- The partition return is carried by the original face of its metric point. -/
theorem MetricRealization.toWeak_support {V : Type u}
    (P : PreAbstractSimplicialComplex V) (x : MetricRealization P) :
    (MetricRealization.toWeak P x).point.weights.support ⊆ x.val.ofLp.support := by
  change (WeakMetricConstruction.partitionReturn P x).point.weights.support ⊆
    x.val.ofLp.support
  simpa only [WeakMetricConstruction.pointData_weights] using
    WeakMetricConstruction.partitionReturn_support P x

/-- The same actual return fixes every original belonging vertex. -/
theorem MetricRealization.toWeak_vertex {V : Type u}
    (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    MetricRealization.toWeak P (Realization.toMetric P (Realization.vertex P v hv)) =
      Realization.vertex P v hv :=
  WeakMetricConstruction.partitionReturn_vertex P v hv

/-- The weak and metric models are equivalent through the actual two comparison maps. -/
def weakMetricHomotopyEquiv {V : Type u} (P : PreAbstractSimplicialComplex V) :
    ContinuousMap.HomotopyEquiv P.Realization (MetricRealization P) :=
  WeakMetricConstruction.weakMetricHomotopyEquiv P

/-- The forward field is exactly the original coordinate identity. -/
theorem weakMetricHomotopyEquiv_toFun {V : Type u} (P : PreAbstractSimplicialComplex V) :
    (weakMetricHomotopyEquiv P).toFun = Realization.toMetric P := (rfl)

/-- The inverse field is exactly the same supported partition return. -/
theorem weakMetricHomotopyEquiv_invFun {V : Type u} (P : PreAbstractSimplicialComplex V) :
    (weakMetricHomotopyEquiv P).invFun = MetricRealization.toWeak P := (rfl)

/-- The actual weak-side inverse homotopy is fixed at the literal weak vertex. -/
def weakMetricLeftHomotopy {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) :
    ContinuousMap.HomotopyRel
      ((MetricRealization.toWeak P).comp (Realization.toMetric P))
      (ContinuousMap.id P.Realization) {Realization.vertex P v hv} :=
  WeakMetricConstruction.weakInverseHomotopyRel P v hv

/-- The actual metric-side inverse homotopy fixes the literal metric vertex image. -/
def weakMetricRightHomotopy {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) :
    ContinuousMap.HomotopyRel
      ((Realization.toMetric P).comp (MetricRealization.toWeak P))
      (ContinuousMap.id (MetricRealization P))
      {Realization.toMetric P (Realization.vertex P v hv)} :=
  WeakMetricConstruction.metricInverseHomotopyRel P v hv

/-- On normalized supported vectors, the actual metric topology is the coordinate topology. -/
theorem MetricRealization.continuous_iff_coordinates {V : Type u}
    (P : PreAbstractSimplicialComplex V) {X : Type z} [TopologicalSpace X]
    (f : X → MetricRealization P) :
    Continuous f ↔ ∀ v, Continuous (fun x => (f x).val.ofLp v) :=
  WeakMetricConstruction.metric_continuous_iff_coordinates P f

namespace Realization

variable {V : Type u} (P : PreAbstractSimplicialComplex V)

/-- The original coordinate map is injective as a map of points. -/
theorem toMetric_injective : Function.Injective (toMetric P) := by
  intro x y h
  apply Realization.ext
  apply Convexity.StdSimplex.ext
  exact (toMetric_weights P x).symm.trans
    ((congrArg (fun m : MetricRealization P => m.val.ofLp) h).trans (toMetric_weights P y))

end Realization

end PreAbstractSimplicialComplex

end
