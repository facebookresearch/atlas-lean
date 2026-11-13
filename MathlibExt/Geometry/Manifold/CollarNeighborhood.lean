/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Instances.Real

import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity

@[expose] public section

/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/

noncomputable section

open Filter Function Manifold Set WithLp
open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

private abbrev collarFace (n : ℕ) [NeZero n] :=
  {x : EuclideanHalfSpace n // x.val 0 = 0}

/-- Splitting a Euclidean half-space into its boundary face and normal coordinate. -/
private def collarHalfSpaceSplit (n : ℕ) [NeZero n] :
    EuclideanHalfSpace n ≃ₜ collarFace n × Set.Ici (0 : ℝ) where
  toFun x :=
    (⟨⟨toLp 2 (Function.update x.val 0 0), by simp⟩, by simp⟩,
      ⟨x.val 0, x.property⟩)
  invFun x :=
    ⟨toLp 2 (Function.update x.1.val.val 0 x.2.val), by
      rw [PiLp.toLp_apply, Function.update_self]
      exact x.2.property⟩
  left_inv x := by
    apply EuclideanHalfSpace.ext
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp
    · simp [hi]
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      apply EuclideanHalfSpace.ext
      apply PiLp.ext
      intro i
      by_cases hi : i = 0
      · subst i
        simp [x.1.property]
      · simp [hi]
    · apply Subtype.ext
      simp
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

private def collarIcoToIci (r : ℝ) : Set.Ico (0 : ℝ) r → Set.Ici (0 : ℝ) :=
  Set.inclusion Set.Ico_subset_Ici_self

private theorem collarIcoToIci_isOpenEmbedding (r : ℝ) :
    Topology.IsOpenEmbedding (collarIcoToIci r) := by
  refine Topology.IsOpenEmbedding.inclusion Set.Ico_subset_Ici_self ?_
  have h : (Subtype.val : Set.Ici (0 : ℝ) → ℝ) ⁻¹' Set.Ico 0 r =
      {x : Set.Ici (0 : ℝ) | x.val < r} := by
    ext x
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨x.property, hx⟩
  rw [h]
  exact isOpen_lt continuous_subtype_val continuous_const

private def collarModelMap (n : ℕ) [NeZero n] (r : ℝ) :
    collarFace n × Set.Ico (0 : ℝ) r → EuclideanHalfSpace n :=
  (collarHalfSpaceSplit n).symm ∘ Prod.map id (collarIcoToIci r)

/-- The standard half-open normal cylinder is open-embedded in the half-space. -/
private theorem collarModelMap_isOpenEmbedding (n : ℕ) [NeZero n] (r : ℝ) :
    Topology.IsOpenEmbedding (collarModelMap n r) := by
  exact (collarHalfSpaceSplit n).symm.isOpenEmbedding.comp
    (Topology.IsOpenEmbedding.id.prodMap (collarIcoToIci_isOpenEmbedding r))

private theorem collarModelMap_zero (n : ℕ) [NeZero n] {r : ℝ} (hr : 0 < r)
    (x : collarFace n) :
    collarModelMap n r (x, ⟨0, by exact ⟨le_rfl, hr⟩⟩) = x.val := by
  apply EuclideanHalfSpace.ext
  apply PiLp.ext
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [collarModelMap, collarIcoToIci, collarHalfSpaceSplit] using x.property.symm
  · simp [collarModelMap, collarIcoToIci, collarHalfSpaceSplit, hi]

private abbrev collarChartDomain {n : ℕ} {M : Type*} [TopologicalSpace M] [NeZero n]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (r : ℝ) :=
  collarModelMap n r ⁻¹' e.target

private def collarChartMap {n : ℕ} {M : Type*} [TopologicalSpace M] [NeZero n]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (r : ℝ) :
    ↥(collarChartDomain e r) → M :=
  fun x => e.symm (collarModelMap n r x.val)

/-- Restricting a chart to a standard normal cylinder gives an open embedding. -/
private theorem collarChartMap_isOpenEmbedding {n : ℕ} {M : Type*} [TopologicalSpace M] [NeZero n]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (r : ℝ) :
    Topology.IsOpenEmbedding (collarChartMap e r) := by
  let h := e.open_source.isOpenEmbedding_subtypeVal.comp
    (e.toHomeomorphSourceTarget.symm.isOpenEmbedding.comp
      ((collarModelMap_isOpenEmbedding n r).restrictPreimage e.target))
  exact h

/-- Every boundary point in an arbitrary atlas chart lies on its zero-coordinate face. -/
private theorem collarBoundaryCoordZeroOfChart
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {x : M} (hx : x ∈ e.source)
    (hxb : x ∈ ModelWithCorners.boundary (I := 𝓡∂ n) M) :
    (e x).val 0 = 0 := by
  change (𝓡∂ n).IsBoundaryPoint x at hxb
  have hfront : e.extend (𝓡∂ n) x ∈ frontier (e.extend (𝓡∂ n)).target :=
    ((𝓡∂ n).isBoundaryPoint_iff_of_mem_atlas (n := (⊤ : ℕ∞)) (by simp) he hx).mp hxb
  have htarget : e.extend (𝓡∂ n) x ∈ (e.extend (𝓡∂ n)).target :=
    (e.extend (𝓡∂ n)).map_source (by simpa [e.extend_source] using hx)
  have hnint : e.extend (𝓡∂ n) x ∉ interior (e.extend (𝓡∂ n)).target :=
    (mem_frontier_iff_notMem_interior htarget).mp hfront
  have hnint' : e.extend (𝓡∂ n) x ∉ interior (range (𝓡∂ n)) := by
    rwa [(e.extend_target_eventuallyEqSet (I := 𝓡∂ n) hx).mem_interior_iff] at hnint
  have hrange : e.extend (𝓡∂ n) x ∈ range (𝓡∂ n) :=
    e.extend_target_subset_range htarget
  have hfront' : e.extend (𝓡∂ n) x ∈ frontier (range (𝓡∂ n)) :=
    (mem_frontier_iff_notMem_interior hrange).mpr hnint'
  rw [frontier_range_modelWithCornersEuclideanHalfSpace, e.extend_coe] at hfront'
  simpa using hfront'.symm

/-- In any atlas chart, the boundary is exactly the zero-coordinate face. -/
private theorem collarMemBoundaryIffCoordZeroOfChart
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {x : M} (hx : x ∈ e.source) :
    x ∈ ModelWithCorners.boundary (I := 𝓡∂ n) M ↔ (e x).val 0 = 0 := by
  constructor
  · exact collarBoundaryCoordZeroOfChart he hx
  · intro hz
    apply ((𝓡∂ n).isBoundaryPoint_iff_of_mem_atlas
      (n := (⊤ : ℕ∞)) (by simp) he hx).mpr
    have htarget : e.extend (𝓡∂ n) x ∈ (e.extend (𝓡∂ n)).target :=
      (e.extend (𝓡∂ n)).map_source (by simpa [e.extend_source] using hx)
    have hrange : e.extend (𝓡∂ n) x ∈ range (𝓡∂ n) :=
      e.extend_target_subset_range htarget
    have hfront : e.extend (𝓡∂ n) x ∈ frontier (range (𝓡∂ n)) := by
      rw [frontier_range_modelWithCornersEuclideanHalfSpace, e.extend_coe]
      simpa using hz.symm
    have hnintRange : e.extend (𝓡∂ n) x ∉ interior (range (𝓡∂ n)) :=
      (mem_frontier_iff_notMem_interior hrange).mp hfront
    have hnintTarget :
        e.extend (𝓡∂ n) x ∉ interior (e.extend (𝓡∂ n)).target := by
      intro hint
      exact hnintRange
        ((e.extend_target_eventuallyEqSet (I := 𝓡∂ n) hx).mem_interior_iff.mp hint)
    exact (mem_frontier_iff_notMem_interior htarget).mpr hnintTarget

/-- The normal-cylinder part of a chart target is open in the model cylinder. -/
private theorem collarChartDomain_isOpen
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (r : ℝ) :
    IsOpen (collarChartDomain e r) :=
  e.open_target.preimage (collarModelMap_isOpenEmbedding n r).continuous

private abbrev collarBoundary
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] :=
  ↥(ModelWithCorners.boundary (I := 𝓡∂ n) M)

private abbrev collarBoundaryChartSource
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) :=
  {b : collarBoundary (n := n) (M := M) // b.val ∈ e.source}

private abbrev collarBoundaryChartTarget
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) :=
  {x : collarFace n // x.val ∈ e.target}

/-- A manifold chart restricts to a homeomorphism from its boundary part to the zero face. -/
private def collarBoundaryChart
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) :
    collarBoundaryChartSource e ≃ₜ collarBoundaryChartTarget e where
  toFun b := ⟨⟨e b.val.val, collarBoundaryCoordZeroOfChart he b.property b.val.property⟩,
    e.map_source b.property⟩
  invFun x := ⟨⟨e.symm x.val.val, by
    apply (collarMemBoundaryIffCoordZeroOfChart he (e.map_target x.property)).mpr
    rw [e.right_inv x.property]
    exact x.val.property⟩, e.map_target x.property⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    exact e.left_inv b.property
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact e.right_inv x.property
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact e.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) fun b ↦ b.property
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact e.symm.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) fun x ↦ x.property

private theorem collarBoundaryChartSource_isOpen
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) :
    IsOpen {b : collarBoundary (n := n) (M := M) | b.val ∈ e.source} :=
  e.open_source.preimage continuous_subtype_val

private theorem collarBoundaryChartTarget_isOpen
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) :
    IsOpen {x : collarFace n | x.val ∈ e.target} :=
  e.open_target.preimage continuous_subtype_val

private def collarBoundaryParamMap
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
    collarBoundaryChartSource e × Set.Ico (0 : ℝ) r → collarFace n × Set.Ico (0 : ℝ) r :=
  fun x ↦ (↑((collarBoundaryChart e he) x.1), x.2)

/-- Boundary chart coordinates, paired with the normal coordinate, form an open embedding. -/
private theorem collarBoundaryParamMap_isOpenEmbedding
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
    Topology.IsOpenEmbedding (collarBoundaryParamMap e he r) := by
  have hface : Topology.IsOpenEmbedding
      (fun x : collarBoundaryChartSource e ↦ (↑((collarBoundaryChart e he) x) : collarFace n)) :=
    (collarBoundaryChartTarget_isOpen e).isOpenEmbedding_subtypeVal.comp
      (collarBoundaryChart e he).isOpenEmbedding
  exact hface.prodMap Topology.IsOpenEmbedding.id

private abbrev collarLocalDomain
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :=
  collarBoundaryParamMap e he r ⁻¹' collarChartDomain e r

/-- The domain on which one chart supplies a local collar is open. -/
private theorem collarLocalDomain_isOpen
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
    IsOpen (collarLocalDomain e he r) :=
  (collarChartDomain_isOpen e r).preimage (collarBoundaryParamMap_isOpenEmbedding e he r).continuous

private def collarLocalMap
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
    ↥(collarLocalDomain e he r) → M :=
  fun x ↦ collarChartMap e r ⟨collarBoundaryParamMap e he r x.val, x.property⟩

/-- A chart supplies an open embedded local collar on its maximal product-shaped domain. -/
private theorem collarLocalMap_isOpenEmbedding
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
    Topology.IsOpenEmbedding (collarLocalMap e he r) := by
  exact (collarChartMap_isOpenEmbedding e r).comp
    ((collarBoundaryParamMap_isOpenEmbedding e he r).restrictPreimage
      (collarChartDomain e r))

private def collarLocalZeroPoint
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) (hr : 0 < r)
    (b : collarBoundaryChartSource e) : ↥(collarLocalDomain e he r) :=
  ⟨(b, ⟨0, ⟨le_rfl, hr⟩⟩), by
    change collarModelMap n r
      (↑((collarBoundaryChart e he) b), ⟨0, by exact ⟨le_rfl, hr⟩⟩) ∈ e.target
    rw [collarModelMap_zero n hr]
    exact e.map_source b.property⟩

/-- Every point of the boundary chart is fixed by the local collar at normal coordinate zero. -/
private theorem collarLocalMap_zero
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) (hr : 0 < r)
    (b : collarBoundaryChartSource e) :
    collarLocalMap e he r (collarLocalZeroPoint e he r hr b) = b.val.val := by
  change e.symm (collarModelMap n r
    (↑((collarBoundaryChart e he) b), ⟨0, by exact ⟨le_rfl, hr⟩⟩)) = b.val.val
  rw [collarModelMap_zero n hr]
  exact e.left_inv b.property

/-- Positive normal parameters in a chart collar lie off the manifold boundary. -/
private theorem collarLocalMap_not_mem_boundary
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ)
    (z : ↥(collarLocalDomain e he r)) (hz : 0 < z.val.2.val) :
    collarLocalMap e he r z ∉ ModelWithCorners.boundary (I := 𝓡∂ n) M := by
  intro hb
  have hsource : collarLocalMap e he r z ∈ e.source := by
    exact e.map_target z.property
  have hzero := (collarMemBoundaryIffCoordZeroOfChart he hsource).mp hb
  change (e (e.symm (collarModelMap n r (collarBoundaryParamMap e he r z.val)))).val 0 = 0
    at hzero
  rw [e.right_inv z.property] at hzero
  change
    ((collarHalfSpaceSplit n).symm
      (↑((collarBoundaryChart e he) z.val.1), collarIcoToIci r z.val.2)).val 0 = 0 at hzero
  simpa [collarHalfSpaceSplit, collarIcoToIci] using hz.ne' hzero

/-- The manifold boundary is a closed subset of the ambient manifold. -/
private theorem collarBoundary_isClosed
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] :
    IsClosed (ModelWithCorners.boundary (I := 𝓡∂ n) M) := by
  exact ModelWithCorners.isClosed_boundary (I := 𝓡∂ n) (n := (⊤ : ℕ∞)) (by simp)

/-- A Hausdorff second-countable finite-dimensional manifold is paracompact. -/
private theorem collarParacompactSpace
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] [T2Space M] [SecondCountableTopology M] :
    ParacompactSpace M := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡∂ n)
  let _ : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

/-- The closed boundary subtype is paracompact. -/
private theorem collarBoundaryParacompactSpace
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] [T2Space M] [SecondCountableTopology M] :
    ParacompactSpace (collarBoundary (n := n) (M := M)) := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡∂ n)
  let _ : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  let _ : ParacompactSpace M := collarParacompactSpace (n := n) (M := M)
  exact (collarBoundary_isClosed (n := n) (M := M)).isClosedEmbedding_subtypeVal.paracompactSpace

private abbrev collarExternal (X : Type*) [TopologicalSpace X] (A : Set X) :=
  ↥((Set.univ ×ˢ ({0} : Set ℝ)) ∪ (A ×ˢ Set.Icc (-2 : ℝ) 0))

private def collarExternalBase
    {X : Type*} [TopologicalSpace X] (A : Set X) : X → collarExternal X A :=
  fun x ↦ ⟨(x, 0), Or.inl ⟨Set.mem_univ x, Set.mem_singleton 0⟩⟩

private theorem collarExternal_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    IsClosed ((Set.univ ×ˢ ({0} : Set ℝ)) ∪ (A ×ˢ Set.Icc (-2 : ℝ) 0)) := by
  exact (isClosed_univ.prod isClosed_singleton).union (hA.prod isClosed_Icc)

private theorem collarExternalBase_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Continuous (collarExternalBase A) := by
  exact Continuous.subtype_mk (continuous_id.prodMk continuous_const) _

private theorem collarExternalBase_isClosedEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.IsClosedEmbedding (collarExternalBase A) := by
  have hprod : Topology.IsClosedEmbedding (fun x : X ↦ (x, (0 : ℝ))) := by
    refine ⟨isEmbedding_prodMkLeft 0, ?_⟩
    convert (isClosed_univ.prod (isClosed_singleton : IsClosed ({0} : Set ℝ))) using 1
    ext p
    rcases p with ⟨x, t⟩
    simp [eq_comm]
  apply Topology.IsClosedEmbedding.of_comp
    (collarExternal_isClosed hA).isClosedEmbedding_subtypeVal.isEmbedding
  simpa [Function.comp_def, collarExternalBase] using hprod

private abbrev collarExternalNegative
    (X : Type*) [TopologicalSpace X] (A : Set X) : Set (collarExternal X A) :=
  {y | y.val.2 < 0}

private theorem collarExternalNegative_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (collarExternalNegative X A) := by
  exact isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const

private theorem collarExternal_fst_mem_of_snd_lt
    {X : Type*} [TopologicalSpace X] {A : Set X} (y : collarExternal X A)
    (hy : y.val.2 < 0) : y.val.1 ∈ A := by
  rcases y.property with hy0 | hyA
  · exfalso
    have hz : y.val.2 = 0 := hy0.2
    rw [hz] at hy
    exact (lt_irrefl 0 hy).elim
  · exact hyA.1

private def collarExternalNegativeMap
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    A × Set.Ico (-2 : ℝ) 0 → collarExternal X A :=
  fun z ↦ ⟨(z.1.val, z.2.val), Or.inr ⟨z.1.property, z.2.property.1, z.2.property.2.le⟩⟩

private theorem collarExternalNegativeMap_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Continuous (collarExternalNegativeMap A) := by
  exact Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) _

private theorem collarExternalNegativeMap_isEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.IsEmbedding (collarExternalNegativeMap A) := by
  apply Topology.IsEmbedding.of_comp collarExternalNegativeMap_continuous continuous_subtype_val
  change Topology.IsEmbedding
    (Prod.map (Subtype.val : A → X) (Subtype.val : Set.Ico (-2 : ℝ) 0 → ℝ))
  exact Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.subtypeVal

private theorem collarExternalNegativeMap_range
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    range (collarExternalNegativeMap A) = collarExternalNegative X A := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2.property.2
  · intro hy
    have ha : y.val.1 ∈ A := collarExternal_fst_mem_of_snd_lt y hy
    have hlow : -2 ≤ y.val.2 := by
      rcases y.property with hy0 | hyA
      · have hz : y.val.2 = 0 := hy0.2
        rw [hz]
        norm_num
      · exact hyA.2.1
    refine ⟨(⟨y.val.1, ha⟩, ⟨y.val.2, hlow, hy⟩), ?_⟩
    apply Subtype.ext
    rfl

private theorem collarExternalNegativeMap_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.IsOpenEmbedding (collarExternalNegativeMap A) := by
  refine ⟨collarExternalNegativeMap_isEmbedding (X := X) (A := A), ?_⟩
  rw [collarExternalNegativeMap_range (X := X) (A := A)]
  exact collarExternalNegative_isOpen (X := X) (A := A)

private def collarExternalInteriorMap
    {X : Type*} [TopologicalSpace X] (A : Set X) : ↥(Aᶜ) → collarExternal X A :=
  fun x ↦ collarExternalBase A x.val

private theorem collarExternalInteriorMap_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Continuous (collarExternalInteriorMap A) := by
  exact collarExternalBase_continuous.comp continuous_subtype_val

private theorem collarExternalInteriorMap_isEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.IsEmbedding (collarExternalInteriorMap A) := by
  apply Topology.IsEmbedding.of_comp collarExternalInteriorMap_continuous continuous_subtype_val
  change Topology.IsEmbedding (fun x : ↥(Aᶜ) ↦ (x.val, (0 : ℝ)))
  exact (isEmbedding_prodMkLeft 0).comp Topology.IsEmbedding.subtypeVal

private abbrev collarExternalInterior
    (X : Type*) [TopologicalSpace X] (A : Set X) : Set (collarExternal X A) :=
  {y | y.val.1 ∉ A}

private theorem collarExternalInterior_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    IsOpen (collarExternalInterior X A) := by
  exact hA.isOpen_compl.preimage (continuous_fst.comp continuous_subtype_val)

private theorem collarExternalInteriorMap_range
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    range (collarExternalInteriorMap A) = collarExternalInterior X A := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact x.property
  · intro hy
    rcases y.property with hy0 | hyA
    · refine ⟨⟨y.val.1, hy⟩, ?_⟩
      apply Subtype.ext
      change (y.val.1, (0 : ℝ)) = y.val
      apply Prod.ext
      · rfl
      · exact hy0.2.symm
    · exact (hy hyA.1).elim

private theorem collarExternalInteriorMap_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.IsOpenEmbedding (collarExternalInteriorMap A) := by
  refine ⟨collarExternalInteriorMap_isEmbedding (X := X) (A := A), ?_⟩
  rw [collarExternalInteriorMap_range (X := X) (A := A)]
  exact collarExternalInterior_isOpen hA

private def collarNegativeIntervalInclusion :
    Set.Ico (-2 : ℝ) 0 → Set.Ico (-2 : ℝ) 1 :=
  Set.inclusion fun _ hx ↦ ⟨hx.1, hx.2.trans (by norm_num)⟩

private theorem collarNegativeIntervalInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding collarNegativeIntervalInclusion := by
  refine Topology.IsOpenEmbedding.inclusion
    (show Set.Ico (-2 : ℝ) 0 ⊆ Set.Ico (-2 : ℝ) 1 from
      fun _ hx ↦ ⟨hx.1, hx.2.trans (by norm_num)⟩) ?_
  have h : (Subtype.val : Set.Ico (-2 : ℝ) 1 → ℝ) ⁻¹' Set.Ico (-2 : ℝ) 0 =
      {x | x.val < 0} := by
    ext x
    exact and_iff_right x.property.1
  rw [h]
  exact isOpen_lt (continuous_subtype_val) continuous_const

private def collarPositiveIntervalInclusion :
    Set.Ioo (0 : ℝ) 1 → Set.Ico (0 : ℝ) 1 :=
  Set.inclusion fun _ hx ↦ ⟨hx.1.le, hx.2⟩

private theorem collarPositiveIntervalInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding collarPositiveIntervalInclusion := by
  refine Topology.IsOpenEmbedding.inclusion
    (show Set.Ioo (0 : ℝ) 1 ⊆ Set.Ico (0 : ℝ) 1 from fun _ hx ↦ ⟨hx.1.le, hx.2⟩) ?_
  have h : (Subtype.val : Set.Ico (0 : ℝ) 1 → ℝ) ⁻¹' Set.Ioo (0 : ℝ) 1 =
      {x | 0 < x.val} := by
    ext x
    exact and_iff_left x.property.2
  rw [h]
  exact isOpen_lt continuous_const continuous_subtype_val

private def collarPositiveExtendedIntervalInclusion :
    Set.Ioo (0 : ℝ) 1 → Set.Ico (-2 : ℝ) 1 :=
  Set.inclusion fun _ hx ↦ ⟨le_trans (by norm_num) hx.1.le, hx.2⟩

private theorem collarPositiveExtendedIntervalInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding collarPositiveExtendedIntervalInclusion := by
  refine Topology.IsOpenEmbedding.inclusion
    (show Set.Ioo (0 : ℝ) 1 ⊆ Set.Ico (-2 : ℝ) 1 from
      fun _ hx ↦ ⟨le_trans (by norm_num) hx.1.le, hx.2⟩) ?_
  have h : (Subtype.val : Set.Ico (-2 : ℝ) 1 → ℝ) ⁻¹' Set.Ioo (0 : ℝ) 1 =
      {x | 0 < x.val} := by
    ext x
    exact and_iff_left x.property.2
  rw [h]
  exact isOpen_lt continuous_const continuous_subtype_val

private structure collarLocalData
    (X : Type*) [TopologicalSpace X] (A : Set X) where
  carrier : Set A
  isOpen_carrier : IsOpen carrier
  map : carrier × Set.Ico (0 : ℝ) 1 → X
  isOpenEmbedding_map : Topology.IsOpenEmbedding map
  map_zero : ∀ u : carrier, map (u, ⟨0, by simp⟩) = u.val.val
  map_not_mem : ∀ z, 0 < z.2.val → map z ∉ A

private def collarLocalDataRestrict
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (V : Set A) (hV : IsOpen V) (hVd : V ⊆ d.carrier) : collarLocalData X A := by
  let inc : V → d.carrier := Set.inclusion hVd
  have hinc : Topology.IsOpenEmbedding inc := by
    apply Topology.IsOpenEmbedding.inclusion hVd
    exact hV.preimage continuous_subtype_val
  let param : V × Set.Ico (0 : ℝ) 1 → d.carrier × Set.Ico (0 : ℝ) 1 :=
    Prod.map inc id
  exact
    { carrier := V
      isOpen_carrier := hV
      map := d.map ∘ param
      isOpenEmbedding_map := d.isOpenEmbedding_map.comp
        (hinc.prodMap Topology.IsOpenEmbedding.id)
      map_zero := fun u ↦ by
        change d.map (inc u, ⟨0, by simp⟩) = u.val.val
        simpa [inc] using d.map_zero (inc u)
      map_not_mem := fun z hz ↦ d.map_not_mem (param z) hz }

private theorem collarLocalDataShrink
    {X : Type*} [TopologicalSpace X] {A : Set X}
    [LocallyCompactSpace A] [RegularSpace A]
    (d : collarLocalData X A) (a : A) (ha : a ∈ d.carrier) :
    ∃ e : collarLocalData X A, a ∈ e.carrier ∧ IsCompact (closure e.carrier) := by
  obtain ⟨V, hVopen, haV, hVd, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton d.isOpen_carrier
      (singleton_subset_iff.mpr ha)
  exact ⟨collarLocalDataRestrict d V hVopen (subset_closure.trans hVd),
    haV (mem_singleton a), hVcompact⟩

private def collarScaleIco (d : ℝ) (hd₀ : 0 < d) (hd₁ : d ≤ 1) :
    Set.Ico (0 : ℝ) 1 → Set.Ico (0 : ℝ) 1 :=
  fun t ↦ ⟨d * t.val, mul_nonneg hd₀.le t.property.1,
    (mul_lt_mul_of_pos_left t.property.2 hd₀).trans_le (by simpa using hd₁)⟩

private theorem collarScaleIco_isOpenEmbedding (d : ℝ) (hd₀ : 0 < d) (hd₁ : d ≤ 1) :
    Topology.IsOpenEmbedding (collarScaleIco d hd₀ hd₁) := by
  let e : Set.Ico (0 : ℝ) 1 ≃ₜ Set.Ico (0 : ℝ) d :=
    { toFun := fun x ↦ ⟨d * x.val, mul_nonneg hd₀.le x.property.1,
          by simpa using mul_lt_mul_of_pos_left x.property.2 hd₀⟩
      invFun := fun y ↦ ⟨y.val / d, div_nonneg y.property.1 hd₀.le,
          (div_lt_one hd₀).2 y.property.2⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        exact mul_div_cancel_left₀ x.val hd₀.ne'
      right_inv := fun y ↦ by
        apply Subtype.ext
        exact mul_div_cancel₀ y.val hd₀.ne'
      continuous_toFun := Continuous.subtype_mk
        (continuous_const.mul continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk
        (continuous_subtype_val.div_const d) _ }
  let inc : Set.Ico (0 : ℝ) d → Set.Ico (0 : ℝ) 1 :=
    Set.inclusion (Set.Ico_subset_Ico_right hd₁)
  have hinc : Topology.IsOpenEmbedding inc := by
    apply Topology.IsOpenEmbedding.inclusion (Set.Ico_subset_Ico_right hd₁)
    have heq : (Subtype.val : Set.Ico (0 : ℝ) 1 → ℝ) ⁻¹' Set.Ico 0 d =
        (Subtype.val : Set.Ico (0 : ℝ) 1 → ℝ) ⁻¹' Set.Iio d := by
      ext x
      simp [x.property.1]
    rw [heq]
    exact isOpen_Iio.preimage continuous_subtype_val
  have hcomp := hinc.comp e.isOpenEmbedding
  have heq : inc ∘ e = collarScaleIco d hd₀ hd₁ := by
    funext x
    apply Subtype.ext
    rfl
  rwa [heq] at hcomp

private def collarLocalDataScale
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) : collarLocalData X A := by
  let param : d.carrier × Set.Ico (0 : ℝ) 1 → d.carrier × Set.Ico (0 : ℝ) 1 :=
    Prod.map id (collarScaleIco δ hδ₀ hδ₁)
  exact
    { carrier := d.carrier
      isOpen_carrier := d.isOpen_carrier
      map := d.map ∘ param
      isOpenEmbedding_map := d.isOpenEmbedding_map.comp
        (Topology.IsOpenEmbedding.id.prodMap
          (collarScaleIco_isOpenEmbedding δ hδ₀ hδ₁))
      map_zero := fun u ↦ by
        change d.map (u, collarScaleIco δ hδ₀ hδ₁ ⟨0, by simp⟩) = u.val.val
        simpa [collarScaleIco] using d.map_zero u
      map_not_mem := fun z hz ↦ by
        apply d.map_not_mem (param z)
        change 0 < δ * z.2.val
        exact mul_pos hδ₀ hz }

private theorem collarExistsTubeHeight
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (d : collarLocalData X A) (K : Set A) (hK : IsCompact K)
    (hKd : K ⊆ d.carrier) (V : Set X) (hV : IsOpen V)
    (hbase : ∀ (a : d.carrier), a.val ∈ K → d.map (a, ⟨0, by simp⟩) ∈ V) :
    ∃ (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1),
      ∀ (a : d.carrier), a.val ∈ K → ∀ t : Set.Ico (0 : ℝ) 1,
        d.map (a, collarScaleIco δ hδ₀ hδ₁ t) ∈ V := by
  let K' : Set d.carrier := Subtype.val ⁻¹' K
  have hKrange : K ⊆ range (Subtype.val : d.carrier → A) := by
    intro a ha
    exact ⟨⟨a, hKd ha⟩, rfl⟩
  have hK' : IsCompact K' := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [image_preimage_eq_inter_range, inter_eq_left.mpr hKrange]
    exact hK
  let P : Set (d.carrier × Set.Ico (0 : ℝ) 1) := d.map ⁻¹' V
  have hPopen : IsOpen P := hV.preimage d.isOpenEmbedding_map.continuous
  have hPpoint (a : d.carrier) (ha : a ∈ K') :
      P ∈ SProd.sprod (nhds a) (nhds (⟨0, by simp⟩ : Set.Ico (0 : ℝ) 1)) := by
    rw [← nhds_prod_eq]
    apply hPopen.mem_nhds
    exact hbase a ha
  have hPprod :
      P ∈ SProd.sprod (nhdsSet K') (nhds (⟨0, by simp⟩ : Set.Ico (0 : ℝ) 1)) :=
    hK'.mem_nhdsSet_prod_of_forall hPpoint
  obtain ⟨U, hU, T, hT, hUT⟩ := Filter.mem_prod_iff.mp hPprod
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ₀ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ₁ : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  refine ⟨δ, hδ₀, hδ₁, ?_⟩
  intro a ha t
  apply hUT
  constructor
  · exact mem_of_mem_nhds ((mem_nhdsSet_iff_forall.mp hU) a ha)
  · apply hεT
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, sub_zero]
    change |δ * t.val| < ε
    rw [abs_of_nonneg (mul_nonneg hδ₀.le t.property.1)]
    exact (mul_lt_of_lt_one_right hδ₀ t.property.2).trans hδε

/-- Every boundary point has local collar data on an actual product neighborhood. -/
private theorem collarExistsLocalData
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (b : collarBoundary (n := n) (M := M)) :
    ∃ d : collarLocalData M (ModelWithCorners.boundary (I := 𝓡∂ n) M),
      b ∈ d.carrier := by
  let e := chartAt (EuclideanHalfSpace n) b.val
  have he : e ∈ atlas (EuclideanHalfSpace n) M := chart_mem_atlas _ _
  let bs : collarBoundaryChartSource e :=
    ⟨b, mem_chart_source (EuclideanHalfSpace n) b.val⟩
  let z₀ := collarLocalZeroPoint e he 1 zero_lt_one bs
  obtain ⟨U, V, hU, hV, hbsU, hzeroV, hUV⟩ :=
    (isOpen_prod_iff.mp (collarLocalDomain_isOpen e he 1)) bs
      (⟨0, by simp⟩ : Set.Ico (0 : ℝ) 1) z₀.property
  obtain ⟨ε, hε, hεV⟩ :=
    (Metric.isOpen_iff.mp hV) (⟨0, by simp⟩ : Set.Ico (0 : ℝ) 1) hzeroV
  let d : ℝ := min (ε / 2) (1 / 2)
  have hd₀ : 0 < d := lt_min (half_pos hε) (by norm_num)
  have hd₁ : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hdε : d < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  let C : Set (collarBoundary (n := n) (M := M)) :=
    Subtype.val '' U
  have hsource : Topology.IsOpenEmbedding
      (fun x : collarBoundaryChartSource e ↦
        (x.val : collarBoundary (n := n) (M := M))) :=
    (collarBoundaryChartSource_isOpen e).isOpenEmbedding_subtypeVal
  have hC : IsOpen C := hsource.isOpenMap U hU
  have hCsource (u : C) : u.val.val ∈ e.source := by
    rcases u.property with ⟨v, hvU, hv⟩
    rw [← hv]
    exact v.property
  let toSource : C → collarBoundaryChartSource e :=
    fun u ↦ ⟨u.val, hCsource u⟩
  have htoSource : Topology.IsOpenEmbedding toSource := by
    apply Topology.IsOpenEmbedding.of_comp toSource hsource
    simpa [toSource, Function.comp_def] using hC.isOpenEmbedding_subtypeVal
  have htoSourceU (u : C) : toSource u ∈ U := by
    rcases u.property with ⟨v, hvU, hv⟩
    have huv : toSource u = v := by
      apply Subtype.ext
      exact hv.symm
    rwa [huv]
  let param : C × Set.Ico (0 : ℝ) 1 →
      collarBoundaryChartSource e × Set.Ico (0 : ℝ) 1 :=
    Prod.map toSource (collarScaleIco d hd₀ hd₁)
  have hparam : Topology.IsOpenEmbedding param :=
    htoSource.prodMap (collarScaleIco_isOpenEmbedding d hd₀ hd₁)
  have hscaledV (t : Set.Ico (0 : ℝ) 1) : collarScaleIco d hd₀ hd₁ t ∈ V := by
    apply hεV
    rw [Metric.mem_ball, Subtype.dist_eq]
    have hnonneg : 0 ≤ d * t.val := mul_nonneg hd₀.le t.property.1
    rw [Real.dist_eq, sub_zero]
    change |d * t.val| < ε
    rw [abs_of_nonneg hnonneg]
    exact (mul_lt_of_lt_one_right hd₀ t.property.2).trans hdε
  have hparamDomain (z : C × Set.Ico (0 : ℝ) 1) :
      param z ∈ collarLocalDomain e he 1 := by
    exact hUV ⟨htoSourceU z.1, hscaledV z.2⟩
  let lift : C × Set.Ico (0 : ℝ) 1 → ↥(collarLocalDomain e he 1) :=
    fun z ↦ ⟨param z, hparamDomain z⟩
  have hlift : Topology.IsOpenEmbedding lift := by
    apply Topology.IsOpenEmbedding.of_comp lift
      (collarLocalDomain_isOpen e he 1).isOpenEmbedding_subtypeVal
    simpa [lift, Function.comp_def] using hparam
  let localMap : C × Set.Ico (0 : ℝ) 1 → M :=
    collarLocalMap e he 1 ∘ lift
  have hlocalMap : Topology.IsOpenEmbedding localMap :=
    (collarLocalMap_isOpenEmbedding e he 1).comp hlift
  let data : collarLocalData M (ModelWithCorners.boundary (I := 𝓡∂ n) M) :=
    { carrier := C
      isOpen_carrier := hC
      map := localMap
      isOpenEmbedding_map := hlocalMap
      map_zero := fun u ↦ by
        change collarLocalMap e he 1 (lift (u, ⟨0, by simp⟩)) = u.val.val
        have hliftZero : lift (u, ⟨0, by simp⟩) =
            collarLocalZeroPoint e he 1 zero_lt_one (toSource u) := by
          apply Subtype.ext
          change param (u, ⟨0, by simp⟩) = (toSource u, ⟨0, by simp⟩)
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            simp [param, collarScaleIco]
        rw [hliftZero, collarLocalMap_zero]
      map_not_mem := fun z hz ↦ by
        apply collarLocalMap_not_mem_boundary e he 1 (lift z)
        change 0 < d * z.2.val
        exact mul_pos hd₀ hz }
  refine ⟨data, ?_⟩
  change b ∈ C
  exact ⟨bs, hbsU, rfl⟩

private def collarExtendedChart
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 1 → collarExternal X A :=
  fun z ↦ if hz : z.2.val ≤ 0 then
    ⟨(z.1.val.val, z.2.val), Or.inr ⟨z.1.val.property, z.2.property.1, hz⟩⟩
  else
    collarExternalBase A
      (d.map (z.1, ⟨z.2.val, (le_of_lt (lt_of_not_ge hz)), z.2.property.2⟩))

private theorem collarExtendedChart_val_of_nonpos
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 1) (hz : z.2.val ≤ 0) :
    (collarExtendedChart d z).val = (z.1.val.val, z.2.val) := by
  simp [collarExtendedChart, hz]

private theorem collarExtendedChart_val_of_pos
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 1) (hz : 0 < z.2.val) :
    (collarExtendedChart d z).val =
      (d.map (z.1, ⟨z.2.val, hz.le, z.2.property.2⟩), 0) := by
  rw [collarExtendedChart, dite_eq_right (not_le_of_gt hz)]
  rfl

private theorem collarExtendedChart_val_of_nonneg
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 1) (hz : 0 ≤ z.2.val) :
    (collarExtendedChart d z).val =
      (d.map (z.1, ⟨z.2.val, hz, z.2.property.2⟩), 0) := by
  rcases hz.eq_or_lt with hz0 | hzpos
  · have hz0' : z.2.val = 0 := hz0.symm
    rw [collarExtendedChart_val_of_nonpos d z hz0'.le]
    have hcoord : (⟨z.2.val, hz, z.2.property.2⟩ : Set.Ico (0 : ℝ) 1) =
        ⟨0, by simp⟩ := by
      apply Subtype.ext
      exact hz0'
    rw [hcoord, d.map_zero z.1, hz0']
  · exact collarExtendedChart_val_of_pos d z hzpos

private def collarExtendedNegative
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 1 → collarExternal X A :=
  fun z ↦ ⟨(z.1.val.val, min z.2.val 0), Or.inr ⟨z.1.val.property,
    le_min z.2.property.1 (by norm_num), min_le_right _ _⟩⟩

private def collarExtendedPositive
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 1 → collarExternal X A :=
  fun z ↦ collarExternalBase A
    (d.map (z.1, ⟨max 0 z.2.val, le_max_left _ _, max_lt (by norm_num) z.2.property.2⟩))

private theorem collarExtendedNegative_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Continuous (collarExtendedNegative d) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
    ((continuous_subtype_val.comp continuous_snd).min continuous_const)

private theorem collarExtendedPositive_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Continuous (collarExtendedPositive d) := by
  apply collarExternalBase_continuous.comp
  apply d.isOpenEmbedding_map.continuous.comp
  exact continuous_fst.prodMk <| Continuous.subtype_mk
    (continuous_const.max (continuous_subtype_val.comp continuous_snd)) _

private theorem collarExtendedChart_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 1) :
    collarExtendedChart d z = if z.2.val ≤ 0 then
      collarExtendedNegative d z else collarExtendedPositive d z := by
  by_cases hz : z.2.val ≤ 0
  · rw [ite_eq_left hz]
    apply Subtype.ext
    rw [collarExtendedChart_val_of_nonpos d z hz]
    simp [collarExtendedNegative, min_eq_left hz]
  · rw [ite_eq_right hz]
    have hz' : 0 < z.2.val := lt_of_not_ge hz
    apply Subtype.ext
    rw [collarExtendedChart_val_of_pos d z hz']
    simp [collarExtendedPositive, collarExternalBase, max_eq_right hz'.le]

private theorem collarExtendedChart_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Continuous (collarExtendedChart d) := by
  rw [show collarExtendedChart d = fun z ↦ if z.2.val ≤ 0 then
    collarExtendedNegative d z else collarExtendedPositive d z from
      funext (collarExtendedChart_eq d)]
  exact Continuous.if_le (collarExtendedNegative_continuous d)
    (collarExtendedPositive_continuous d) (continuous_subtype_val.comp continuous_snd)
    continuous_const fun z hz ↦ by
      apply Subtype.ext
      change (z.1.val.val, min z.2.val 0) =
        (d.map (z.1, ⟨max 0 z.2.val, by simp [z.2.property.2]⟩), 0)
      have hmin : min z.2.val 0 = 0 := by simp [hz]
      have hmax : (⟨max 0 z.2.val, by simp [z.2.property.2]⟩ : Set.Ico (0 : ℝ) 1) =
          ⟨0, by simp⟩ := by
        apply Subtype.ext
        simp [hz]
      rw [hmin, hmax, d.map_zero z.1]

private theorem collarExtendedChart_injective
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Function.Injective (collarExtendedChart d) := by
  intro z w hzw
  by_cases hz : z.2.val ≤ 0 <;> by_cases hw : w.2.val ≤ 0
  · have hval := congrArg Subtype.val hzw
    rw [collarExtendedChart_val_of_nonpos d z hz,
      collarExtendedChart_val_of_nonpos d w hw] at hval
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg Prod.fst hval
    · apply Subtype.ext
      exact congrArg Prod.snd hval
  · have hw' : 0 < w.2.val := lt_of_not_ge hw
    have hval := congrArg Subtype.val hzw
    rw [collarExtendedChart_val_of_nonpos d z hz,
      collarExtendedChart_val_of_pos d w hw'] at hval
    have hfst : z.1.val.val =
        d.map (w.1, ⟨w.2.val, hw'.le, w.2.property.2⟩) := congrArg Prod.fst hval
    have hmem : d.map (w.1, ⟨w.2.val, hw'.le, w.2.property.2⟩) ∈ A := by
      exact (congrArg (fun x : X ↦ x ∈ A) hfst).mp z.1.val.property
    exact (d.map_not_mem _ hw' hmem).elim
  · have hz' : 0 < z.2.val := lt_of_not_ge hz
    have hval := congrArg Subtype.val hzw
    rw [collarExtendedChart_val_of_pos d z hz',
      collarExtendedChart_val_of_nonpos d w hw] at hval
    have hfst : d.map (z.1, ⟨z.2.val, hz'.le, z.2.property.2⟩) =
        w.1.val.val := congrArg Prod.fst hval
    have hmem : d.map (z.1, ⟨z.2.val, hz'.le, z.2.property.2⟩) ∈ A := by
      exact (congrArg (fun x : X ↦ x ∈ A) hfst).mpr w.1.val.property
    exact (d.map_not_mem _ hz' hmem).elim
  · have hz' : 0 < z.2.val := lt_of_not_ge hz
    have hw' : 0 < w.2.val := lt_of_not_ge hw
    have hval := congrArg Subtype.val hzw
    rw [collarExtendedChart_val_of_pos d z hz',
      collarExtendedChart_val_of_pos d w hw'] at hval
    have hmap := d.isOpenEmbedding_map.injective (congrArg Prod.fst hval)
    apply Prod.ext
    · exact congrArg (fun p : d.carrier × Set.Ico (0 : ℝ) 1 ↦ p.1) hmap
    · apply Subtype.ext
      exact congrArg (fun p : d.carrier × Set.Ico (0 : ℝ) 1 ↦ p.2.val) hmap

private def collarExtendedNegativeInclusion
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 0 → d.carrier × Set.Ico (-2 : ℝ) 1 :=
  Prod.map id collarNegativeIntervalInclusion

private theorem collarExtendedNegativeInclusion_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Topology.IsOpenEmbedding (collarExtendedNegativeInclusion d) := by
  exact Topology.IsOpenEmbedding.id.prodMap collarNegativeIntervalInclusion_isOpenEmbedding

private def collarExtendedPositiveInclusion
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ioo (0 : ℝ) 1 → d.carrier × Set.Ico (-2 : ℝ) 1 :=
  Prod.map id collarPositiveExtendedIntervalInclusion

private theorem collarExtendedPositiveInclusion_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Topology.IsOpenEmbedding (collarExtendedPositiveInclusion d) := by
  exact Topology.IsOpenEmbedding.id.prodMap
    collarPositiveExtendedIntervalInclusion_isOpenEmbedding

private def collarExtendedNegativePart
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 0 → collarExternal X A :=
  collarExternalNegativeMap A ∘ Prod.map Subtype.val id

private theorem collarExtendedNegativePart_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Topology.IsOpenEmbedding (collarExtendedNegativePart d) := by
  exact collarExternalNegativeMap_isOpenEmbedding.comp
    (d.isOpen_carrier.isOpenEmbedding_subtypeVal.prodMap Topology.IsOpenEmbedding.id)

private theorem collarExtendedChart_negative
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 0) :
    collarExtendedChart d (z.1, collarNegativeIntervalInclusion z.2) =
      collarExtendedNegativePart d z := by
  apply Subtype.ext
  rw [collarExtendedChart_val_of_nonpos]
  · rfl
  · exact z.2.property.2.le

private theorem collarExtendedChart_comp_negative
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    collarExtendedChart d ∘ collarExtendedNegativeInclusion d =
      collarExtendedNegativePart d := by
  funext z
  exact collarExtendedChart_negative d z

private def collarLocalPositiveMap
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ioo (0 : ℝ) 1 → ↥(Aᶜ) :=
  fun z ↦ ⟨d.map (z.1, collarPositiveIntervalInclusion z.2),
    d.map_not_mem _ z.2.property.1⟩

private theorem collarLocalPositiveMap_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) : Topology.IsOpenEmbedding (collarLocalPositiveMap d) := by
  apply Topology.IsOpenEmbedding.of_comp (collarLocalPositiveMap d)
    hA.isOpen_compl.isOpenEmbedding_subtypeVal
  change Topology.IsOpenEmbedding
    (d.map ∘ Prod.map id collarPositiveIntervalInclusion)
  exact d.isOpenEmbedding_map.comp
    (Topology.IsOpenEmbedding.id.prodMap collarPositiveIntervalInclusion_isOpenEmbedding)

private def collarExtendedPositivePart
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ioo (0 : ℝ) 1 → collarExternal X A :=
  collarExternalInteriorMap A ∘ collarLocalPositiveMap d

private theorem collarExtendedPositivePart_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) : Topology.IsOpenEmbedding (collarExtendedPositivePart d) := by
  exact (collarExternalInteriorMap_isOpenEmbedding hA).comp
    (collarLocalPositiveMap_isOpenEmbedding hA d)

private theorem collarExtendedChart_positive
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ioo (0 : ℝ) 1) :
    collarExtendedChart d
      (z.1, ⟨z.2.val, (le_trans (by norm_num) z.2.property.1.le), z.2.property.2⟩) =
      collarExtendedPositivePart d z := by
  apply Subtype.ext
  rw [collarExtendedChart_val_of_pos]
  · rfl
  · exact z.2.property.1

private theorem collarExtendedChart_comp_positive
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    collarExtendedChart d ∘ collarExtendedPositiveInclusion d =
      collarExtendedPositivePart d := by
  funext z
  exact collarExtendedChart_positive d z

private theorem collarExtendedChart_image_mem_nhds_of_neg
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    {S : Set (d.carrier × Set.Ico (-2 : ℝ) 1)} (hS : IsOpen S)
    {z : d.carrier × Set.Ico (-2 : ℝ) 1} (hzS : z ∈ S) (hz : z.2.val < 0) :
    collarExtendedChart d '' S ∈ 𝓝 (collarExtendedChart d z) := by
  let q : d.carrier × Set.Ico (-2 : ℝ) 0 :=
    (z.1, ⟨z.2.val, z.2.property.1, hz⟩)
  have hq : collarExtendedNegativeInclusion d q = z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  let T := collarExtendedNegativeInclusion d ⁻¹' S
  have hT : IsOpen T := hS.preimage (collarExtendedNegativeInclusion_isOpenEmbedding d).continuous
  have hqT : q ∈ T := by
    change collarExtendedNegativeInclusion d q ∈ S
    rwa [hq]
  have hopen : IsOpen (collarExtendedNegativePart d '' T) :=
    (collarExtendedNegativePart_isOpenEmbedding d).isOpenMap T hT
  have hnhds : collarExtendedNegativePart d '' T ∈ 𝓝 (collarExtendedNegativePart d q) :=
    hopen.mem_nhds ⟨q, hqT, rfl⟩
  have hpoint : collarExtendedNegativePart d q = collarExtendedChart d z :=
    (congrFun (collarExtendedChart_comp_negative d) q).symm.trans
      (congrArg (collarExtendedChart d) hq)
  rw [hpoint] at hnhds
  apply mem_of_superset hnhds
  rintro y ⟨w, hw, rfl⟩
  exact ⟨collarExtendedNegativeInclusion d w, hw,
    congrFun (collarExtendedChart_comp_negative d) w⟩

private theorem collarExtendedChart_image_mem_nhds_of_pos
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) {S : Set (d.carrier × Set.Ico (-2 : ℝ) 1)}
    (hS : IsOpen S) {z : d.carrier × Set.Ico (-2 : ℝ) 1} (hzS : z ∈ S)
    (hz : 0 < z.2.val) : collarExtendedChart d '' S ∈ 𝓝 (collarExtendedChart d z) := by
  let q : d.carrier × Set.Ioo (0 : ℝ) 1 :=
    (z.1, ⟨z.2.val, hz, z.2.property.2⟩)
  have hq : collarExtendedPositiveInclusion d q = z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  let T := collarExtendedPositiveInclusion d ⁻¹' S
  have hT : IsOpen T := hS.preimage (collarExtendedPositiveInclusion_isOpenEmbedding d).continuous
  have hqT : q ∈ T := by
    change collarExtendedPositiveInclusion d q ∈ S
    rwa [hq]
  have hopen : IsOpen (collarExtendedPositivePart d '' T) :=
    (collarExtendedPositivePart_isOpenEmbedding hA d).isOpenMap T hT
  have hnhds : collarExtendedPositivePart d '' T ∈ 𝓝 (collarExtendedPositivePart d q) :=
    hopen.mem_nhds ⟨q, hqT, rfl⟩
  have hpoint : collarExtendedPositivePart d q = collarExtendedChart d z :=
    (congrFun (collarExtendedChart_comp_positive d) q).symm.trans
      (congrArg (collarExtendedChart d) hq)
  rw [hpoint] at hnhds
  apply mem_of_superset hnhds
  rintro y ⟨w, hw, rfl⟩
  exact ⟨collarExtendedPositiveInclusion d w, hw,
    congrFun (collarExtendedChart_comp_positive d) w⟩

private theorem collarExtendedChart_image_mem_nhds_of_zero
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    {S : Set (d.carrier × Set.Ico (-2 : ℝ) 1)} (hS : IsOpen S)
    {z : d.carrier × Set.Ico (-2 : ℝ) 1} (hzS : z ∈ S) (hz : z.2.val = 0) :
    collarExtendedChart d '' S ∈ 𝓝 (collarExtendedChart d z) := by
  obtain ⟨U, V, hU, hV, hzU, hzV, hUV⟩ := (isOpen_prod_iff.mp hS) z.1 z.2 hzS
  obtain ⟨ε, hε, hεV⟩ := (Metric.isOpen_iff.mp hV) z.2 hzV
  let P : Set (d.carrier × Set.Ico (0 : ℝ) 1) := U ×ˢ {t | t.val < ε}
  have hP : IsOpen P := hU.prod (isOpen_lt continuous_subtype_val continuous_const)
  let W : Set X := d.map '' P
  have hW : IsOpen W := d.isOpenEmbedding_map.isOpenMap P hP
  let N : Set (collarExternal X A) :=
    (Subtype.val : collarExternal X A → X × ℝ) ⁻¹' (W ×ˢ Set.Ioi (-ε))
  have hN : IsOpen N := (hW.prod isOpen_Ioi).preimage continuous_subtype_val
  have hzW : z.1.val.val ∈ W := by
    refine ⟨(z.1, ⟨0, by simp⟩), ⟨hzU, hε⟩, ?_⟩
    exact d.map_zero z.1
  have hzN : collarExtendedChart d z ∈ N := by
    change (collarExtendedChart d z).val.1 ∈ W ∧ -ε < (collarExtendedChart d z).val.2
    rw [collarExtendedChart_val_of_nonpos d z hz.le]
    exact ⟨hzW, by simpa [hz] using hε⟩
  apply mem_of_superset (hN.mem_nhds hzN)
  intro y hyN
  change y.val.1 ∈ W ∧ -ε < y.val.2 at hyN
  rcases hyN.1 with ⟨p, hpP, hpy⟩
  rcases hpP with ⟨hpU, hpε⟩
  rcases y.property with hy0 | hyA
  · let t : Set.Ico (-2 : ℝ) 1 :=
      ⟨p.2.val, le_trans (by norm_num) p.2.property.1, p.2.property.2⟩
    have htV : t ∈ V := by
      apply hεV
      rw [Metric.mem_ball, Subtype.dist_eq]
      simpa [t, hz, abs_of_nonneg p.2.property.1] using hpε
    let w : d.carrier × Set.Ico (-2 : ℝ) 1 := (p.1, t)
    refine ⟨w, hUV ⟨hpU, htV⟩, ?_⟩
    apply Subtype.ext
    rw [collarExtendedChart_val_of_nonneg d w p.2.property.1]
    have ht : (⟨t.val, p.2.property.1, t.property.2⟩ : Set.Ico (0 : ℝ) 1) = p.2 := by
      apply Subtype.ext
      rfl
    rw [ht]
    apply Prod.ext
    · exact hpy
    · exact hy0.2.symm
  · have hp0 : p.2.val = 0 := by
      apply le_antisymm
      · by_contra hp
        have hp' : 0 < p.2.val := lt_of_not_ge hp
        apply d.map_not_mem p hp'
        exact (congrArg (fun x : X ↦ x ∈ A) hpy).mpr hyA.1
      · exact p.2.property.1
    have hpx : p.1.val.val = y.val.1 := by
      have hpcoord : p.2 = ⟨0, by simp⟩ := by
        apply Subtype.ext
        exact hp0
      calc
        p.1.val.val = d.map (p.1, ⟨0, by simp⟩) := (d.map_zero p.1).symm
        _ = d.map p := by rw [← hpcoord]
        _ = y.val.1 := hpy
    let t : Set.Ico (-2 : ℝ) 1 :=
      ⟨y.val.2, hyA.2.1, hyA.2.2.trans_lt (by norm_num)⟩
    have htV : t ∈ V := by
      apply hεV
      rw [Metric.mem_ball, Subtype.dist_eq]
      have ht0 : t.val ≤ 0 := by
        exact hyA.2.2
      have hdist : dist t.val z.2.val = -t.val := by
        simp [hz, abs_of_nonpos ht0]
      rw [hdist]
      change -y.val.2 < ε
      linarith
    let w : d.carrier × Set.Ico (-2 : ℝ) 1 := (p.1, t)
    refine ⟨w, hUV ⟨hpU, htV⟩, ?_⟩
    apply Subtype.ext
    rw [collarExtendedChart_val_of_nonpos d w hyA.2.2]
    exact Prod.ext hpx rfl

private theorem collarExtendedChart_isOpenMap
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) : IsOpenMap (collarExtendedChart d) := by
  intro S hS
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hzS, rfl⟩
  rcases lt_trichotomy z.2.val 0 with hz | hz | hz
  · exact collarExtendedChart_image_mem_nhds_of_neg d hS hzS hz
  · exact collarExtendedChart_image_mem_nhds_of_zero d hS hzS hz
  · exact collarExtendedChart_image_mem_nhds_of_pos hA d hS hzS hz

private theorem collarExtendedChart_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) : Topology.IsOpenEmbedding (collarExtendedChart d) := by
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (collarExtendedChart_continuous d) (collarExtendedChart_injective d)
    (collarExtendedChart_isOpenMap hA d)

private abbrev collarPushParameters :=
  Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1

/-- The piecewise-linear fibre map used to push one partial collar to the next. -/
private def collarFiberMap (p q s : ℝ) : ℝ :=
  if s ≤ -p then
    -2 + (s + 2) * (2 - q) / (2 - p)
  else if s ≤ (1 / 2 : ℝ) then
    -q + (s + p) * (q + 1 / 2) / (p + 1 / 2)
  else s

private theorem collarFiberDenomTwoPos (p : Set.Icc (0 : ℝ) 1) :
    0 < 2 - p.val := by
  linarith [p.property.2]

private theorem collarFiberDenomHalfPos (p : Set.Icc (0 : ℝ) 1) :
    0 < p.val + 1 / 2 := by
  linarith [p.property.1]

private theorem collarFiberMap_lower {p q s : ℝ} (h : s ≤ -p) :
    collarFiberMap p q s = -2 + (s + 2) * (2 - q) / (2 - p) := by
  simp [collarFiberMap, h]

private theorem collarFiberMap_middle {p q s : ℝ} (h₁ : ¬ s ≤ -p)
    (h₂ : s ≤ (1 / 2 : ℝ)) :
    collarFiberMap p q s = -q + (s + p) * (q + 1 / 2) / (p + 1 / 2) := by
  rw [collarFiberMap, ite_eq_right h₁, ite_eq_left h₂]

private theorem collarFiberMap_upper (p : Set.Icc (0 : ℝ) 1) {q s : ℝ}
    (h : ¬ s ≤ (1 / 2 : ℝ)) : collarFiberMap p q s = s := by
  have h' : ¬ s ≤ -p.val := by linarith [p.property.1]
  rw [collarFiberMap, ite_eq_right h', ite_eq_right h]

private theorem collarFiberMap_lower_bounds (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hs : -2 ≤ s) (hsp : s ≤ -p.val) :
    -2 ≤ collarFiberMap p.val q.val s ∧ collarFiberMap p.val q.val s ≤ -q.val := by
  rw [collarFiberMap_lower hsp]
  have hp : 0 < 2 - p.val := collarFiberDenomTwoPos p
  have hq : 0 ≤ 2 - q.val := by linarith [q.property.2]
  have hs0 : 0 ≤ s + 2 := by linarith
  have hs1 : s + 2 ≤ 2 - p.val := by linarith
  constructor
  · have : 0 ≤ (s + 2) * (2 - q.val) / (2 - p.val) :=
      div_nonneg (mul_nonneg hs0 hq) hp.le
    linarith
  · have hmul := mul_le_mul_of_nonneg_right hs1 hq
    have hdiv : (s + 2) * (2 - q.val) / (2 - p.val) ≤ 2 - q.val := by
      apply (div_le_iff₀ hp).2
      simpa [mul_comm] using hmul
    linarith

private theorem collarFiberMap_middle_bounds (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hsp : -p.val < s) (hs : s ≤ (1 / 2 : ℝ)) :
    -q.val < collarFiberMap p.val q.val s ∧
      collarFiberMap p.val q.val s ≤ (1 / 2 : ℝ) := by
  rw [collarFiberMap_middle (not_le_of_gt hsp) hs]
  have hp : 0 < p.val + 1 / 2 := collarFiberDenomHalfPos p
  have hq : 0 < q.val + 1 / 2 := by linarith [q.property.1]
  have hs0 : 0 < s + p.val := by linarith
  have hs1 : s + p.val ≤ p.val + 1 / 2 := by linarith
  constructor
  · have : 0 < (s + p.val) * (q.val + 1 / 2) / (p.val + 1 / 2) :=
      div_pos (mul_pos hs0 hq) hp
    linarith
  · have hmul := mul_le_mul_of_nonneg_right hs1 hq.le
    have hdiv :
        (s + p.val) * (q.val + 1 / 2) / (p.val + 1 / 2) ≤ q.val + 1 / 2 := by
      apply (div_le_iff₀ hp).2
      simpa [mul_comm] using hmul
    linarith

private theorem collarFiberMap_mem_Ico (p q : Set.Icc (0 : ℝ) 1)
    (s : Set.Ico (-2 : ℝ) 1) :
    collarFiberMap p.val q.val s.val ∈ Set.Ico (-2 : ℝ) 1 := by
  by_cases hsp : s.val ≤ -p.val
  · have h := collarFiberMap_lower_bounds p q s.property.1 hsp
    exact ⟨h.1, lt_of_le_of_lt h.2 (by linarith [q.property.1])⟩
  · by_cases hs : s.val ≤ (1 / 2 : ℝ)
    · have h := collarFiberMap_middle_bounds p q (lt_of_not_ge hsp) hs
      exact ⟨by linarith [q.property.2, h.1], lt_of_le_of_lt h.2 (by norm_num)⟩
    · rw [collarFiberMap_upper p hs]
      exact s.property

private theorem collarFiberMap_inverse_lower (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hs : -2 ≤ s) (hsp : s ≤ -p.val) :
    collarFiberMap q.val p.val (collarFiberMap p.val q.val s) = s := by
  have hb := (collarFiberMap_lower_bounds p q hs hsp).2
  rw [collarFiberMap_lower hb, collarFiberMap_lower hsp]
  field_simp [ne_of_gt (collarFiberDenomTwoPos p),
    ne_of_gt (collarFiberDenomTwoPos q)]
  ring

private theorem collarFiberMap_inverse_middle (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hsp : -p.val < s) (hs : s ≤ (1 / 2 : ℝ)) :
    collarFiberMap q.val p.val (collarFiberMap p.val q.val s) = s := by
  have hb := collarFiberMap_middle_bounds p q hsp hs
  rw [collarFiberMap_middle (not_le_of_gt hb.1) hb.2,
    collarFiberMap_middle (not_le_of_gt hsp) hs]
  have hp : p.val + 1 / 2 ≠ 0 := ne_of_gt (collarFiberDenomHalfPos p)
  have hq : q.val + 1 / 2 ≠ 0 := ne_of_gt (collarFiberDenomHalfPos q)
  have hc :
      -q.val + (s + p.val) * (q.val + 1 / 2) / (p.val + 1 / 2) + q.val =
        (s + p.val) * (q.val + 1 / 2) / (p.val + 1 / 2) := by ring
  rw [hc, div_mul_cancel₀ _ hp, mul_div_cancel_right₀ _ hq]
  ring

private theorem collarFiberMap_inverse_upper (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hs : (1 / 2 : ℝ) < s) :
    collarFiberMap q.val p.val (collarFiberMap p.val q.val s) = s := by
  rw [collarFiberMap_upper p (not_le_of_gt hs),
    collarFiberMap_upper q (not_le_of_gt hs)]

private theorem collarFiberMap_inverse (p q : Set.Icc (0 : ℝ) 1)
    (s : Set.Ico (-2 : ℝ) 1) :
    collarFiberMap q.val p.val (collarFiberMap p.val q.val s.val) = s.val := by
  by_cases hsp : s.val ≤ -p.val
  · exact collarFiberMap_inverse_lower p q s.property.1 hsp
  · by_cases hs : s.val ≤ (1 / 2 : ℝ)
    · exact collarFiberMap_inverse_middle p q (lt_of_not_ge hsp) hs
    · exact collarFiberMap_inverse_upper p q (lt_of_not_ge hs)

private abbrev collarFiberInput :=
  collarPushParameters × Set.Ico (-2 : ℝ) 1

private def collarFiberTransform (z : collarFiberInput) : Set.Ico (-2 : ℝ) 1 :=
  ⟨collarFiberMap z.1.1.val z.1.2.val z.2.val,
    collarFiberMap_mem_Ico z.1.1 z.1.2 z.2⟩

private theorem collarFiberTransform_continuous : Continuous collarFiberTransform := by
  apply Continuous.subtype_mk
  let p : collarFiberInput → ℝ := fun z ↦ z.1.1.val
  let q : collarFiberInput → ℝ := fun z ↦ z.1.2.val
  let s : collarFiberInput → ℝ := fun z ↦ z.2.val
  have hp : Continuous p :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hq : Continuous q :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous s := continuous_subtype_val.comp continuous_snd
  let lower : collarFiberInput → ℝ := fun z ↦
    -2 + (s z + 2) * (2 - q z) / (2 - p z)
  let middle : collarFiberInput → ℝ := fun z ↦
    -q z + (s z + p z) * (q z + 1 / 2) / (p z + 1 / 2)
  have hlower : Continuous lower := by
    exact continuous_const.add (((hs.add continuous_const).mul
      (continuous_const.sub hq)).div (continuous_const.sub hp) fun z ↦
        ne_of_gt (by dsimp [p]; linarith [z.1.1.property.2]))
  have hmiddle : Continuous middle := by
    exact hq.neg.add (((hs.add hp).mul (hq.add continuous_const)).div
      (hp.add continuous_const) fun z ↦
        ne_of_gt (by dsimp [p]; linarith [z.1.1.property.1]))
  change Continuous fun z ↦ if s z ≤ -p z then lower z
    else if s z ≤ (1 / 2 : ℝ) then middle z else s z
  apply Continuous.if_le hlower
    (Continuous.if_le hmiddle hs hs continuous_const ?_) hs hp.neg
  · intro z hz
    have hhalf : s z ≤ (1 / 2 : ℝ) := by
      dsimp [s, p] at hz ⊢
      linarith [z.1.1.property.1]
    rw [ite_eq_left hhalf]
    dsimp [lower, middle, p, q, s] at hz ⊢
    have hden₁ : 2 - z.1.1.val ≠ 0 := ne_of_gt (collarFiberDenomTwoPos z.1.1)
    have hden₂ : z.1.1.val + 1 / 2 ≠ 0 :=
      ne_of_gt (collarFiberDenomHalfPos z.1.1)
    rw [hz]
    field_simp [hden₁, hden₂]
    ring
  · intro z hz
    dsimp [middle, p, q, s]
    dsimp [s] at hz
    have hden : z.1.1.val + 1 / 2 ≠ 0 := ne_of_gt (collarFiberDenomHalfPos z.1.1)
    rw [hz]
    rw [show (1 / 2 : ℝ) + z.1.1.val = z.1.1.val + 1 / 2 by ring]
    rw [mul_div_cancel_left₀ _ hden]
    ring

private theorem collarFiberMap_anchor (p q : Set.Icc (0 : ℝ) 1) :
    collarFiberMap p.val q.val (-p.val) = -q.val := by
  rw [collarFiberMap_lower le_rfl]
  have hp : 2 - p.val ≠ 0 := ne_of_gt (collarFiberDenomTwoPos p)
  rw [show -p.val + 2 = 2 - p.val by ring, mul_div_cancel_left₀ _ hp]
  ring

private theorem collarFiberMap_self (p : Set.Icc (0 : ℝ) 1)
    (s : Set.Ico (-2 : ℝ) 1) : collarFiberMap p.val p.val s.val = s.val := by
  by_cases hsp : s.val ≤ -p.val
  · rw [collarFiberMap_lower hsp]
    have hp : 2 - p.val ≠ 0 := ne_of_gt (collarFiberDenomTwoPos p)
    rw [mul_div_cancel_right₀ _ hp]
    ring
  · by_cases hs : s.val ≤ (1 / 2 : ℝ)
    · rw [collarFiberMap_middle hsp hs]
      have hp : p.val + 1 / 2 ≠ 0 := ne_of_gt (collarFiberDenomHalfPos p)
      rw [mul_div_cancel_right₀ _ hp]
      ring
    · rw [collarFiberMap_upper p hs]

private structure collarGluingCover
    (X : Type*) [TopologicalSpace X] (A : Set X) where
  data : ℕ → collarLocalData X A
  compact_closure : ∀ k, IsCompact (closure (data k).carrier)
  cover : (Set.univ : Set A) ⊆ ⋃ k, (data k).carrier
  weight : PartitionOfUnity ℕ A Set.univ
  subordinate : weight.IsSubordinate fun k ↦ (data k).carrier

private theorem collarExistsGluingCover
    {X : Type*} [TopologicalSpace X] {A : Set X}
    [Nonempty A] [LindelofSpace A] [LocallyCompactSpace A] [RegularSpace A]
    [NormalSpace A] [ParacompactSpace A]
    (hlocal : ∀ a : A, ∃ d : collarLocalData X A, a ∈ d.carrier) :
    Nonempty (collarGluingCover X A) := by
  choose d hd using hlocal
  choose e he hcompact using fun a ↦ collarLocalDataShrink (d a) a (hd a)
  have hcover : (Set.univ : Set A) ⊆ ⋃ a, (e a).carrier := by
    intro a ha
    exact mem_iUnion.2 ⟨a, he a⟩
  obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover
    (fun a ↦ (e a).carrier) (fun a ↦ (e a).isOpen_carrier) hcover
  let data : ℕ → collarLocalData X A := fun k ↦ e (f k)
  have hdataCover : (Set.univ : Set A) ⊆ ⋃ k, (data k).carrier := by
    simpa [data] using hf
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun k ↦ (data k).carrier) (fun k ↦ (data k).isOpen_carrier) hdataCover
  exact ⟨
    { data := data
      compact_closure := fun k ↦ hcompact (f k)
      cover := hdataCover
      weight := ρ
      subordinate := hρ }⟩

private structure collarControlledCover
    (X : Type*) [TopologicalSpace X] (A : Set X) where
  data : ℕ → collarLocalData X A
  compact_closure : ∀ k, IsCompact (closure (data k).carrier)
  cover : (Set.univ : Set A) ⊆ ⋃ k, (data k).carrier
  ambient : ℕ → Set X
  ambient_open : ∀ k, IsOpen (ambient k)
  ambient_locallyFinite : LocallyFinite ambient
  carrier_to_ambient : ∀ k (a : A), a ∈ (data k).carrier → a.val ∈ ambient k
  weight : PartitionOfUnity ℕ A Set.univ
  subordinate : weight.IsSubordinate fun k ↦ (data k).carrier

private theorem collarExistsControlledCover
    {X : Type*} [TopologicalSpace X] {A : Set X}
    [ParacompactSpace X] [NormalSpace A] [ParacompactSpace A]
    (hA : IsClosed A) (g : collarGluingCover X A) :
    Nonempty (collarControlledCover X A) := by
  choose O hOopen hOpre using fun k ↦
    isOpen_induced_iff.mp (g.data k).isOpen_carrier
  have hOcover : A ⊆ ⋃ k, O k := by
    intro x hx
    let a : A := ⟨x, hx⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (g.cover (mem_univ a))
    apply mem_iUnion.2 ⟨k, ?_⟩
    have : a ∈ Subtype.val ⁻¹' O k := hOpre k ▸ hk
    exact this
  obtain ⟨V, hVopen, hVcover, hVfinite, hVO⟩ :=
    precise_refinement_set hA O hOopen hOcover
  let W : ℕ → Set A := fun k ↦ Subtype.val ⁻¹' V k
  have hWopen (k : ℕ) : IsOpen (W k) :=
    (hVopen k).preimage continuous_subtype_val
  have hWsub (k : ℕ) : W k ⊆ (g.data k).carrier := by
    intro a ha
    have : a ∈ Subtype.val ⁻¹' O k := hVO k ha
    rwa [hOpre k] at this
  let data : ℕ → collarLocalData X A := fun k ↦
    collarLocalDataRestrict (g.data k) (W k) (hWopen k) (hWsub k)
  have hdataCover : (Set.univ : Set A) ⊆ ⋃ k, (data k).carrier := by
    intro a ha
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hVcover a.property)
    exact mem_iUnion.2 ⟨k, hk⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun k ↦ (data k).carrier) (fun k ↦ (data k).isOpen_carrier) hdataCover
  exact ⟨
    { data := data
      compact_closure := fun k ↦ (g.compact_closure k).of_isClosed_subset isClosed_closure
        (closure_mono (hWsub k))
      cover := hdataCover
      ambient := V
      ambient_open := hVopen
      ambient_locallyFinite := hVfinite
      carrier_to_ambient := fun k a ha ↦ ha
      weight := ρ
      subordinate := hρ }⟩

private theorem collarControlledCover_compact_tsupport
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarControlledCover X A) (k : ℕ) : IsCompact (tsupport (g.weight k)) := by
  exact (g.compact_closure k).of_isClosed_subset isClosed_closure
    ((g.subordinate k).trans subset_closure)

private structure collarPreparedCover
    (X : Type*) [TopologicalSpace X] (A : Set X) where
  data : ℕ → collarLocalData X A
  ambient : ℕ → Set X
  ambient_open : ∀ k, IsOpen (ambient k)
  ambient_locallyFinite : LocallyFinite ambient
  carrier_to_ambient : ∀ k (a : A), a ∈ (data k).carrier → a.val ∈ ambient k
  weight : PartitionOfUnity ℕ A Set.univ
  subordinate : weight.IsSubordinate fun k ↦ (data k).carrier
  compact_tsupport : ∀ k, IsCompact (tsupport (weight k))
  tube : ∀ k (a : (data k).carrier), a.val ∈ tsupport (weight k) →
    ∀ t : Set.Ico (0 : ℝ) 1, (data k).map (a, t) ∈ ambient k

private theorem collarPrepareCover
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarControlledCover X A) : Nonempty (collarPreparedCover X A) := by
  have hbase (k : ℕ) (a : (g.data k).carrier)
      (ha : a.val ∈ tsupport (g.weight k)) :
      (g.data k).map (a, ⟨0, by simp⟩) ∈ g.ambient k := by
    rw [(g.data k).map_zero]
    exact g.carrier_to_ambient k a.val (g.subordinate k ha)
  choose δ hδ₀ hδ₁ htube using fun k ↦
    collarExistsTubeHeight (g.data k) (tsupport (g.weight k))
      (collarControlledCover_compact_tsupport g k) (g.subordinate k)
      (g.ambient k) (g.ambient_open k) (hbase k)
  let data : ℕ → collarLocalData X A := fun k ↦
    collarLocalDataScale (g.data k) (δ k) (hδ₀ k) (hδ₁ k)
  exact ⟨
    { data := data
      ambient := g.ambient
      ambient_open := g.ambient_open
      ambient_locallyFinite := g.ambient_locallyFinite
      carrier_to_ambient := g.carrier_to_ambient
      weight := g.weight
      subordinate := g.subordinate
      compact_tsupport := collarControlledCover_compact_tsupport g
      tube := fun k a ha t ↦ by
        change (g.data k).map
          (a, collarScaleIco (δ k) (hδ₀ k) (hδ₁ k) t) ∈ g.ambient k
        exact htube k a ha t }⟩

private def collarPartialWeight
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) : ℝ :=
  ∑ k ∈ Finset.range m, g.weight k a

private theorem collarPartialWeight_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) : Continuous (collarPartialWeight g m) := by
  exact continuous_finsetSum _ fun k _ ↦ (g.weight k).continuous

private theorem collarPartialWeight_nonneg
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) : 0 ≤ collarPartialWeight g m a := by
  exact Finset.sum_nonneg fun k _ ↦ g.weight.nonneg k a

private theorem collarPartialWeight_le_one
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) : collarPartialWeight g m a ≤ 1 := by
  let I := Finset.range m ∪ g.weight.finsupport a
  have htotal : ∑ k ∈ I, g.weight k a = 1 :=
    g.weight.sum_finsupport' (mem_univ a) Finset.subset_union_right
  have hle : ∑ k ∈ Finset.range m, g.weight k a ≤ ∑ k ∈ I, g.weight k a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    intro k hkI hk
    exact g.weight.nonneg k a
  rwa [htotal] at hle

private def collarPartialWeightIcc
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) : Set.Icc (0 : ℝ) 1 :=
  ⟨collarPartialWeight g m a, collarPartialWeight_nonneg g m a,
    collarPartialWeight_le_one g m a⟩

private theorem collarPartialWeight_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) : collarPartialWeight g 0 a = 0 := by
  simp [collarPartialWeight]

private theorem collarPartialWeight_succ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) :
    collarPartialWeight g (m + 1) a = collarPartialWeight g m a + g.weight m a := by
  simp [collarPartialWeight, Finset.sum_range_succ]

private theorem collarPartialWeight_eventually_eq_one
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) :
    ∃ m, collarPartialWeight g m =ᶠ[nhds a] 1 := by
  obtain ⟨I, hI⟩ := g.weight.exists_finset_nhds a
  obtain ⟨m, hIm⟩ := I.exists_nat_subset_range
  refine ⟨m, hI.mono ?_⟩
  intro b hb
  have hsupp : support (g.weight · b) ⊆ Finset.range m := hb.2.trans hIm
  calc
    collarPartialWeight g m b = ∑ᶠ k, g.weight k b :=
      (finsum_eq_sum_of_support_subset _ hsupp).symm
    _ = 1 := g.weight.sum_eq_one (mem_univ b)

private def collarChartPushParameters
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) (a : (g.data k).carrier) :
    collarPushParameters :=
  (collarPartialWeightIcc g k a.val, collarPartialWeightIcc g (k + 1) a.val)

private theorem collarChartPushParameters_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : Continuous (collarChartPushParameters g k) := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact (collarPartialWeight_continuous g k).comp continuous_subtype_val
  · apply Continuous.subtype_mk
    exact (collarPartialWeight_continuous g (k + 1)).comp continuous_subtype_val

private def collarChartPush
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    (g.data k).carrier × Set.Ico (-2 : ℝ) 1 →
      (g.data k).carrier × Set.Ico (-2 : ℝ) 1 :=
  fun z ↦ (z.1, collarFiberTransform (collarChartPushParameters g k z.1, z.2))

private def collarChartPushInv
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    (g.data k).carrier × Set.Ico (-2 : ℝ) 1 →
      (g.data k).carrier × Set.Ico (-2 : ℝ) 1 :=
  fun z ↦ (z.1, collarFiberTransform
    (((collarChartPushParameters g k z.1).2, (collarChartPushParameters g k z.1).1), z.2))

private theorem collarChartPush_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : Continuous (collarChartPush g k) := by
  apply continuous_fst.prodMk
  apply collarFiberTransform_continuous.comp
  exact ((collarChartPushParameters_continuous g k).comp continuous_fst).prodMk continuous_snd

private theorem collarChartPushInv_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : Continuous (collarChartPushInv g k) := by
  apply continuous_fst.prodMk
  apply collarFiberTransform_continuous.comp
  have hp : Continuous (fun z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1 ↦
      collarChartPushParameters g k z.1) :=
    (collarChartPushParameters_continuous g k).comp continuous_fst
  exact ((continuous_snd.comp hp).prodMk (continuous_fst.comp hp)).prodMk continuous_snd

private theorem collarChartPush_leftInverse
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    Function.LeftInverse (collarChartPushInv g k) (collarChartPush g k) := by
  intro z
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact collarFiberMap_inverse (collarChartPushParameters g k z.1).1
      (collarChartPushParameters g k z.1).2 z.2

private theorem collarChartPush_rightInverse
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    Function.RightInverse (collarChartPushInv g k) (collarChartPush g k) := by
  intro z
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact collarFiberMap_inverse (collarChartPushParameters g k z.1).2
      (collarChartPushParameters g k z.1).1 z.2

private def collarChartPushHomeomorph
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    (g.data k).carrier × Set.Ico (-2 : ℝ) 1 ≃ₜ
      (g.data k).carrier × Set.Ico (-2 : ℝ) 1 where
  toFun := collarChartPush g k
  invFun := collarChartPushInv g k
  left_inv := collarChartPush_leftInverse g k
  right_inv := collarChartPush_rightInverse g k
  continuous_toFun := collarChartPush_continuous g k
  continuous_invFun := collarChartPushInv_continuous g k

private theorem collarChartPush_eq_self_of_weight_eq_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1)
    (hz : g.weight k z.1.val = 0) : collarChartPush g k z = z := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    have hpq : (collarChartPushParameters g k z.1).1 =
        (collarChartPushParameters g k z.1).2 := by
      apply Subtype.ext
      change collarPartialWeight g k z.1.val = collarPartialWeight g (k + 1) z.1.val
      rw [collarPartialWeight_succ, hz, add_zero]
    change collarFiberMap (collarChartPushParameters g k z.1).1.val
      (collarChartPushParameters g k z.1).2.val z.2.val = z.2.val
    rw [← hpq]
    exact collarFiberMap_self (collarChartPushParameters g k z.1).1 z.2

private def collarPartialAnchor
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) : Set.Ico (-2 : ℝ) 1 :=
  ⟨-collarPartialWeight g m a, by linarith [collarPartialWeight_le_one g m a],
    by linarith [collarPartialWeight_nonneg g m a]⟩

private theorem collarChartPush_anchor
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) (a : (g.data k).carrier) :
    collarChartPush g k (a, collarPartialAnchor g k a.val) =
      (a, collarPartialAnchor g (k + 1) a.val) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact collarFiberMap_anchor (collarChartPushParameters g k a).1
      (collarChartPushParameters g k a).2

private def collarExtendByIdentityFun
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R) (y : Y) : Y := by
  classical
  exact if hy : y ∈ R then (e ⟨y, hy⟩).val else y

private def collarExtendByIdentityInv
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R) (y : Y) : Y := by
  classical
  exact if hy : y ∈ R then (e.symm ⟨y, hy⟩).val else y

private theorem collarExtendByIdentityFun_apply_mem
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R)
    {y : Y} (hy : y ∈ R) :
    collarExtendByIdentityFun R e y = (e ⟨y, hy⟩).val := by
  simp [collarExtendByIdentityFun, hy]

private theorem collarExtendByIdentityInv_apply_mem
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R)
    {y : Y} (hy : y ∈ R) :
    collarExtendByIdentityInv R e y = (e.symm ⟨y, hy⟩).val := by
  simp [collarExtendByIdentityInv, hy]

private theorem collarExtendByIdentity_leftInverse
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R) :
    Function.LeftInverse (collarExtendByIdentityInv R e)
      (collarExtendByIdentityFun R e) := by
  intro y
  by_cases hy : y ∈ R
  · rw [collarExtendByIdentityFun_apply_mem R e hy]
    rw [collarExtendByIdentityInv_apply_mem R e (e ⟨y, hy⟩).property]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩)
  · simp [collarExtendByIdentityFun, collarExtendByIdentityInv, hy]

private theorem collarExtendByIdentity_rightInverse
    {Y : Type*} [TopologicalSpace Y] (R : Set Y) (e : R ≃ₜ R) :
    Function.RightInverse (collarExtendByIdentityInv R e)
      (collarExtendByIdentityFun R e) := by
  intro y
  by_cases hy : y ∈ R
  · rw [collarExtendByIdentityInv_apply_mem R e hy]
    rw [collarExtendByIdentityFun_apply_mem R e (e.symm ⟨y, hy⟩).property]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  · simp [collarExtendByIdentityFun, collarExtendByIdentityInv, hy]

private theorem collarExtendByIdentity_continuous
    {Y : Type*} [TopologicalSpace Y] (R C : Set Y) (e : R ≃ₜ R)
    (hR : IsOpen R) (hC : IsClosed C) (hCR : C ⊆ R)
    (he : ∀ x : R, x.val ∉ C → e x = x) : Continuous (collarExtendByIdentityFun R e) := by
  have hcontR : ContinuousOn (collarExtendByIdentityFun R e) R := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : R.domRestrict (collarExtendByIdentityFun R e) =
        (Subtype.val : R → Y) ∘ e := by
      funext y
      simp [collarExtendByIdentityFun]
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  have heqC : Set.EqOn (collarExtendByIdentityFun R e) id Cᶜ := by
    intro y hy
    by_cases hyR : y ∈ R
    · rw [collarExtendByIdentityFun_apply_mem R e hyR]
      exact congrArg Subtype.val (he ⟨y, hyR⟩ hy)
    · simp [collarExtendByIdentityFun, hyR]
  have hcontC : ContinuousOn (collarExtendByIdentityFun R e) Cᶜ :=
    continuous_id.continuousOn.congr heqC
  have hunion : R ∪ Cᶜ = Set.univ := by
    apply eq_univ_iff_forall.mpr
    intro y
    by_cases hy : y ∈ C
    · exact Or.inl (hCR hy)
    · exact Or.inr hy
  rw [← continuousOn_univ, ← hunion]
  exact hcontR.union_of_isOpen hcontC hR hC.isOpen_compl

private def collarExtendByIdentity
    {Y : Type*} [TopologicalSpace Y] (R C : Set Y) (e : R ≃ₜ R)
    (hR : IsOpen R) (hC : IsClosed C) (hCR : C ⊆ R)
    (he : ∀ x : R, x.val ∉ C → e x = x)
    (he' : ∀ x : R, x.val ∉ C → e.symm x = x) : Y ≃ₜ Y where
  toFun := collarExtendByIdentityFun R e
  invFun := collarExtendByIdentityInv R e
  left_inv := collarExtendByIdentity_leftInverse R e
  right_inv := collarExtendByIdentity_rightInverse R e
  continuous_toFun := collarExtendByIdentity_continuous R C e hR hC hCR he
  continuous_invFun := collarExtendByIdentity_continuous R C e.symm hR hC hCR he'

private abbrev collarLowerHalf : Set (Set.Ico (-2 : ℝ) 1) :=
  {s | s.val ≤ (1 / 2 : ℝ)}

private theorem collarLowerHalf_isCompact : IsCompact collarLowerHalf := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have himage : (Subtype.val : Set.Ico (-2 : ℝ) 1 → ℝ) '' collarLowerHalf =
      Set.Icc (-2 : ℝ) (1 / 2) := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.property.1, ht⟩
    · intro hs
      let t : Set.Ico (-2 : ℝ) 1 := ⟨s, hs.1, hs.2.trans_lt (by norm_num)⟩
      exact ⟨t, hs.2, rfl⟩
  rw [himage]
  exact isCompact_Icc

private abbrev collarChartSupport
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : Set (g.data k).carrier :=
  Subtype.val ⁻¹' tsupport (g.weight k)

private theorem collarChartSupport_isCompact
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : IsCompact (collarChartSupport g k) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have hrange : tsupport (g.weight k) ⊆
      range (Subtype.val : (g.data k).carrier → A) := by
    intro a ha
    exact ⟨⟨a, g.subordinate k ha⟩, rfl⟩
  rw [image_preimage_eq_inter_range, inter_eq_left.mpr hrange]
  exact g.compact_tsupport k

private abbrev collarChartTubeDomain
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    Set ((g.data k).carrier × Set.Ico (-2 : ℝ) 1) :=
  collarChartSupport g k ×ˢ collarLowerHalf

private theorem collarChartTubeDomain_isCompact
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : IsCompact (collarChartTubeDomain g k) :=
  (collarChartSupport_isCompact g k).prod collarLowerHalf_isCompact

private theorem collarChartPush_eq_self_of_not_mem_tube
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1)
    (hz : z ∉ collarChartTubeDomain g k) : collarChartPush g k z = z := by
  by_cases ha : z.1.val ∈ tsupport (g.weight k)
  · have hs : (1 / 2 : ℝ) < z.2.val := by
      by_contra hs
      exact hz ⟨ha, le_of_not_gt hs⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact collarFiberMap_upper (collarChartPushParameters g k z.1).1
        (not_le_of_gt hs)
  · have hw : g.weight k z.1.val = 0 := by
      by_contra hw
      exact ha (subset_closure hw)
    exact collarChartPush_eq_self_of_weight_eq_zero g k z hw

private theorem collarChartPushInv_eq_self_of_not_mem_tube
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1)
    (hz : z ∉ collarChartTubeDomain g k) : collarChartPushInv g k z = z := by
  by_cases ha : z.1.val ∈ tsupport (g.weight k)
  · have hs : (1 / 2 : ℝ) < z.2.val := by
      by_contra hs
      exact hz ⟨ha, le_of_not_gt hs⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact collarFiberMap_upper (collarChartPushParameters g k z.1).2
        (not_le_of_gt hs)
  · have hw : g.weight k z.1.val = 0 := by
      by_contra hw
      exact ha (subset_closure hw)
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      have hpq : (collarChartPushParameters g k z.1).1 =
          (collarChartPushParameters g k z.1).2 := by
        apply Subtype.ext
        change collarPartialWeight g k z.1.val = collarPartialWeight g (k + 1) z.1.val
        rw [collarPartialWeight_succ, hw, add_zero]
      change collarFiberMap (collarChartPushParameters g k z.1).2.val
        (collarChartPushParameters g k z.1).1.val z.2.val = z.2.val
      rw [hpq]
      exact collarFiberMap_self (collarChartPushParameters g k z.1).2 z.2

private abbrev collarPushTube
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : Set (collarExternal X A) :=
  collarExtendedChart (g.data k) '' collarChartTubeDomain g k

private theorem collarPushTube_isCompact
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : IsCompact (collarPushTube g k) :=
  (collarChartTubeDomain_isCompact g k).image
    (collarExtendedChart_continuous (g.data k))

private theorem collarPushTube_isClosed
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : IsClosed (collarPushTube g k) :=
  (collarPushTube_isCompact g k).isClosed

private abbrev collarChartRange
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : Set (collarExternal X A) :=
  range (collarExtendedChart (g.data k))

private theorem collarChartRange_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) : IsOpen (collarChartRange g k) :=
  (collarExtendedChart_isOpenEmbedding hA (g.data k)).isOpen_range

private def collarExtendedChartHomeomorph
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 1 ≃ₜ range (collarExtendedChart d) :=
  (collarExtendedChart_isOpenEmbedding hA d).isEmbedding.toHomeomorph

private def collarRangePushHomeomorph
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) :
    collarChartRange g k ≃ₜ collarChartRange g k :=
  (collarExtendedChartHomeomorph hA (g.data k)).symm.trans
    ((collarChartPushHomeomorph g k).trans
      (collarExtendedChartHomeomorph hA (g.data k)))

private theorem collarPushTube_subset_range
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    collarPushTube g k ⊆ collarChartRange g k := by
  rintro y ⟨z, hz, rfl⟩
  exact mem_range_self z

private theorem collarRangePush_eq_self_of_not_mem_tube
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (y : collarChartRange g k)
    (hy : y.val ∉ collarPushTube g k) : collarRangePushHomeomorph hA g k y = y := by
  let chart := collarExtendedChartHomeomorph hA (g.data k)
  let z := chart.symm y
  have hz : z ∉ collarChartTubeDomain g k := by
    intro hz
    apply hy
    refine ⟨z, hz, ?_⟩
    exact congrArg Subtype.val (chart.apply_symm_apply y)
  change chart (collarChartPush g k z) = y
  rw [collarChartPush_eq_self_of_not_mem_tube g k z hz]
  exact chart.apply_symm_apply y

private theorem collarRangePush_symm_eq_self_of_not_mem_tube
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (y : collarChartRange g k)
    (hy : y.val ∉ collarPushTube g k) :
    (collarRangePushHomeomorph hA g k).symm y = y := by
  let chart := collarExtendedChartHomeomorph hA (g.data k)
  let z := chart.symm y
  have hz : z ∉ collarChartTubeDomain g k := by
    intro hz
    apply hy
    refine ⟨z, hz, ?_⟩
    exact congrArg Subtype.val (chart.apply_symm_apply y)
  change chart (collarChartPushInv g k z) = y
  rw [collarChartPushInv_eq_self_of_not_mem_tube g k z hz]
  exact chart.apply_symm_apply y

private def collarGlobalPush
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) :
    collarExternal X A ≃ₜ collarExternal X A :=
  collarExtendByIdentity (collarChartRange g k) (collarPushTube g k)
    (collarRangePushHomeomorph hA g k) (collarChartRange_isOpen hA g k)
    (collarPushTube_isClosed g k) (collarPushTube_subset_range g k)
    (collarRangePush_eq_self_of_not_mem_tube hA g k)
    (collarRangePush_symm_eq_self_of_not_mem_tube hA g k)

private theorem collarGlobalPush_chart
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1) :
    collarGlobalPush hA g k (collarExtendedChart (g.data k) z) =
      collarExtendedChart (g.data k) (collarChartPush g k z) := by
  let chart := collarExtendedChartHomeomorph hA (g.data k)
  have hy : collarExtendedChart (g.data k) z ∈ collarChartRange g k := mem_range_self z
  rw [show collarGlobalPush hA g k (collarExtendedChart (g.data k) z) =
      ((collarRangePushHomeomorph hA g k)
        ⟨collarExtendedChart (g.data k) z, hy⟩).val by
    exact collarExtendByIdentityFun_apply_mem _ _ hy]
  change (chart (collarChartPush g k (chart.symm ⟨collarExtendedChart (g.data k) z, hy⟩))).val = _
  have hz : chart.symm ⟨collarExtendedChart (g.data k) z, hy⟩ = z := by
    have hyz : (⟨collarExtendedChart (g.data k) z, hy⟩ : collarChartRange g k) =
        chart z := by
      apply Subtype.ext
      rfl
    rw [hyz, chart.symm_apply_apply]
  rw [hz]
  rfl

private theorem collarFiberMap_ge_anchor_iff
    (p q : Set.Icc (0 : ℝ) 1) (s : Set.Ico (-2 : ℝ) 1) :
    -q.val ≤ collarFiberMap p.val q.val s.val ↔ -p.val ≤ s.val := by
  constructor
  · intro h
    by_contra hs
    have hsp : s.val < -p.val := lt_of_not_ge hs
    rw [collarFiberMap_lower hsp.le] at h
    have hp : 0 < 2 - p.val := collarFiberDenomTwoPos p
    have hq : 0 < 2 - q.val := by linarith [q.property.2]
    have hs' : s.val + 2 < 2 - p.val := by linarith
    have hmul := mul_lt_mul_of_pos_right hs' hq
    have hdiv : (s.val + 2) * (2 - q.val) / (2 - p.val) < 2 - q.val := by
      apply (div_lt_iff₀ hp).2
      simpa [mul_comm] using hmul
    linarith
  · intro h
    rcases h.eq_or_lt with h | h
    · rw [← h, collarFiberMap_anchor p q]
    · by_cases hs : s.val ≤ (1 / 2 : ℝ)
      · exact (collarFiberMap_middle_bounds p q h hs).1.le
      · rw [collarFiberMap_upper p hs]
        linarith [q.property.1]

private abbrev collarStage
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) : Set (collarExternal X A) :=
  {y | y.val.2 = 0 ∨ ∃ ha : y.val.1 ∈ A,
    -collarPartialWeight g m (⟨y.val.1, ha⟩ : A) ≤ y.val.2}

private theorem collarExternalBase_range
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    range (collarExternalBase A) = {y : collarExternal X A | y.val.2 = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hy
    refine ⟨y.val.1, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hy.symm

private theorem collarStage_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) :
    collarStage g 0 = range (collarExternalBase A) := by
  rw [collarExternalBase_range]
  ext y
  constructor
  · rintro (hy | ⟨ha, hy⟩)
    · exact hy
    · have hnonpos : y.val.2 ≤ 0 := by
        rcases y.property with hy0 | hyA
        · exact hy0.2.le
        · exact hyA.2.2
      rw [collarPartialWeight_zero] at hy
      exact le_antisymm hnonpos (by simpa using hy)
  · exact Or.inl

private theorem collarExtendedChart_mem_stage_iff
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k m : ℕ)
    (z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1) :
    collarExtendedChart (g.data k) z ∈ collarStage g m ↔
      -collarPartialWeight g m z.1.val ≤ z.2.val := by
  change ((collarExtendedChart (g.data k) z).val.2 = 0 ∨
    ∃ ha : (collarExtendedChart (g.data k) z).val.1 ∈ A,
      -collarPartialWeight g m
        (⟨(collarExtendedChart (g.data k) z).val.1, ha⟩ : A) ≤
          (collarExtendedChart (g.data k) z).val.2) ↔
    -collarPartialWeight g m z.1.val ≤ z.2.val
  by_cases hs : z.2.val ≤ 0
  · rw [collarExtendedChart_val_of_nonpos (g.data k) z hs]
    constructor
    · rintro (hz | ⟨ha, ha'⟩)
      · have hz' : z.2.val = 0 := by simpa only [Prod.snd] using hz
        rw [hz']
        linarith [collarPartialWeight_nonneg g m z.1.val]
      · have hsame : (⟨z.1.val.val, ha⟩ : A) = z.1.val := by
          apply Subtype.ext
          rfl
        simpa [hsame] using ha'
    · intro hz
      exact Or.inr ⟨z.1.val.property, hz⟩
  · have hs' : 0 < z.2.val := lt_of_not_ge hs
    rw [collarExtendedChart_val_of_pos (g.data k) z hs']
    constructor
    · intro _
      linarith [collarPartialWeight_nonneg g m z.1.val]
    · intro _
      exact Or.inl rfl

private theorem collarGlobalPush_eq_self_of_not_mem_range
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A)
    (hy : y ∉ collarChartRange g k) : collarGlobalPush hA g k y = y := by
  change collarExtendByIdentityFun (collarChartRange g k)
    (collarRangePushHomeomorph hA g k) y = y
  simp [collarExtendByIdentityFun, hy]

private theorem collarWeight_eq_zero_of_external_not_mem_range
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A)
    (hyneg : y.val.2 < 0) (hy : y ∉ collarChartRange g k) :
    g.weight k (⟨y.val.1, collarExternal_fst_mem_of_snd_lt y hyneg⟩ : A) = 0 := by
  let a : A := ⟨y.val.1, collarExternal_fst_mem_of_snd_lt y hyneg⟩
  by_contra hw
  have ha : a ∈ (g.data k).carrier := g.subordinate k (subset_closure hw)
  have hlow : -2 ≤ y.val.2 := by
    rcases y.property with hy0 | hyA
    · rw [hy0.2]
      norm_num
    · exact hyA.2.1
  let z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1 :=
    (⟨a, ha⟩, ⟨y.val.2, hlow, hyneg.trans (by norm_num)⟩)
  apply hy
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [collarExtendedChart_val_of_nonpos (g.data k) z hyneg.le]

private theorem collarStage_succ_iff_of_not_mem_range
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A)
    (hy : y ∉ collarChartRange g k) : y ∈ collarStage g (k + 1) ↔ y ∈ collarStage g k := by
  by_cases hy0 : y.val.2 = 0
  · exact iff_of_true (Or.inl hy0) (Or.inl hy0)
  have hyneg : y.val.2 < 0 := by
    rcases y.property with hbase | hstrip
    · exact (hy0 hbase.2).elim
    · exact lt_of_le_of_ne hstrip.2.2 hy0
  have hw := collarWeight_eq_zero_of_external_not_mem_range g k y hyneg hy
  have hsum (ha : y.val.1 ∈ A) :
      collarPartialWeight g (k + 1) (⟨y.val.1, ha⟩ : A) =
        collarPartialWeight g k (⟨y.val.1, ha⟩ : A) := by
    rw [collarPartialWeight_succ]
    have haa : (⟨y.val.1, ha⟩ : A) =
        ⟨y.val.1, collarExternal_fst_mem_of_snd_lt y hyneg⟩ := by
      apply Subtype.ext
      rfl
    rw [haa, hw, add_zero]
  constructor
  · rintro (_ | ⟨ha, h⟩)
    · exact (hy0 ‹y.val.2 = 0›).elim
    · exact Or.inr ⟨ha, by simpa [hsum ha] using h⟩
  · rintro (_ | ⟨ha, h⟩)
    · exact (hy0 ‹y.val.2 = 0›).elim
    · exact Or.inr ⟨ha, by simpa [hsum ha] using h⟩

private theorem collarGlobalPush_mem_stage_iff
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A) :
    collarGlobalPush hA g k y ∈ collarStage g (k + 1) ↔ y ∈ collarStage g k := by
  by_cases hy : y ∈ collarChartRange g k
  · rcases hy with ⟨z, rfl⟩
    rw [collarGlobalPush_chart hA g k,
      collarExtendedChart_mem_stage_iff g k (k + 1),
      collarExtendedChart_mem_stage_iff g k k]
    exact collarFiberMap_ge_anchor_iff
      (collarPartialWeightIcc g k z.1.val)
      (collarPartialWeightIcc g (k + 1) z.1.val) z.2
  · rw [collarGlobalPush_eq_self_of_not_mem_range hA g k y hy]
    exact collarStage_succ_iff_of_not_mem_range g k y hy

private theorem collarGlobalPush_image_stage
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) :
    collarGlobalPush hA g k '' collarStage g k = collarStage g (k + 1) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (collarGlobalPush_mem_stage_iff hA g k x).2 hx
  · intro hy
    let x := (collarGlobalPush hA g k).symm y
    have hx : x ∈ collarStage g k := by
      apply (collarGlobalPush_mem_stage_iff hA g k x).1
      simpa [x] using hy
    exact ⟨x, hx, by simp [x]⟩

private def collarPartialPush
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) : ℕ → collarExternal X A ≃ₜ collarExternal X A
  | 0 => Homeomorph.refl _
  | k + 1 => (collarPartialPush hA g k).trans (collarGlobalPush hA g k)

private theorem collarPartialPush_succ_apply
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A) :
    collarPartialPush hA g (k + 1) y =
      collarGlobalPush hA g k (collarPartialPush hA g k y) := by
  rfl

private theorem collarPartialPush_image_base
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) :
    collarPartialPush hA g m '' range (collarExternalBase A) = collarStage g m := by
  induction m with
  | zero =>
      simpa [collarPartialPush] using (collarStage_zero g).symm
  | succ k ih =>
      rw [show collarPartialPush hA g (k + 1) '' range (collarExternalBase A) =
          collarGlobalPush hA g k ''
            (collarPartialPush hA g k '' range (collarExternalBase A)) by
        rw [image_image]
        rfl]
      rw [ih, collarGlobalPush_image_stage hA g k]

private def collarShiftHomeomorph : Set.Ico (0 : ℝ) 1 ≃ₜ Set.Ico (-1 : ℝ) 0 where
  toFun t := ⟨t.val - 1, by linarith [t.property.1], by linarith [t.property.2]⟩
  invFun s := ⟨s.val + 1, by linarith [s.property.1], by linarith [s.property.2]⟩
  left_inv t := by
    apply Subtype.ext
    ring
  right_inv s := by
    apply Subtype.ext
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def collarShiftInclusion : Set.Ico (-1 : ℝ) 0 → Set.Ico (-2 : ℝ) 0 :=
  Set.inclusion fun _ hs ↦ ⟨hs.1.trans' (by norm_num), hs.2⟩

private theorem collarShiftInclusion_isEmbedding :
    Topology.IsEmbedding collarShiftInclusion :=
  by
    apply Topology.IsEmbedding.inclusion
    intro x hx
    exact ⟨hx.1.trans' (by norm_num), hx.2⟩

private def collarStripMap
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    A × Set.Ico (0 : ℝ) 1 → collarExternal X A :=
  collarExternalNegativeMap A ∘
    Prod.map id (collarShiftInclusion ∘ collarShiftHomeomorph)

private theorem collarStripMap_val
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (z : A × Set.Ico (0 : ℝ) 1) :
    (collarStripMap A z).val = (z.1.val, z.2.val - 1) := by
  rfl

private theorem collarStripMap_isEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.IsEmbedding (collarStripMap A) := by
  exact (collarExternalNegativeMap_isEmbedding (X := X) (A := A)).comp
    (Topology.IsEmbedding.id.prodMap
      (collarShiftInclusion_isEmbedding.comp collarShiftHomeomorph.isEmbedding))

private theorem collarStripMap_mem_stage
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hm : collarPartialWeight g m z.1 = 1) : collarStripMap A z ∈ collarStage g m := by
  right
  rw [collarStripMap_val]
  refine ⟨z.1.property, ?_⟩
  have ha : (⟨z.1.val, z.1.property⟩ : A) = z.1 := by
    apply Subtype.ext
    rfl
  rw [ha, hm]
  linarith [z.2.property.1]

private def collarFiniteMap
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (z : A × Set.Ico (0 : ℝ) 1) : X :=
  ((collarPartialPush hA g m).symm (collarStripMap A z)).val.1

private theorem collarFiniteMap_lift
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hm : collarPartialWeight g m z.1 = 1) :
    collarExternalBase A (collarFiniteMap hA g m z) =
      (collarPartialPush hA g m).symm (collarStripMap A z) := by
  have hj : collarStripMap A z ∈ collarStage g m := collarStripMap_mem_stage g m z hm
  rw [← collarPartialPush_image_base hA g m] at hj
  rcases hj with ⟨y, ⟨x, rfl⟩, hy⟩
  have hinv : (collarPartialPush hA g m).symm (collarStripMap A z) =
      collarExternalBase A x := by
    rw [← hy]
    simp
  change collarExternalBase A
    (((collarPartialPush hA g m).symm (collarStripMap A z)).val.1) =
      (collarPartialPush hA g m).symm (collarStripMap A z)
  rw [hinv]
  rfl

private theorem collarFiniteMap_recover
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hm : collarPartialWeight g m z.1 = 1) :
    collarPartialPush hA g m (collarExternalBase A (collarFiniteMap hA g m z)) =
      collarStripMap A z := by
  rw [collarFiniteMap_lift hA g m z hm]
  simp

private theorem collarPartialWeight_mono_of_le
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) {m k : ℕ} (hmk : m ≤ k) :
    collarPartialWeight g m a ≤ collarPartialWeight g k a := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmk)
  intro i _ _
  exact g.weight.nonneg i a

private theorem collarWeight_eq_zero_of_partial_eq_one
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) {m k : ℕ}
    (hm : collarPartialWeight g m a = 1) (hmk : m ≤ k) : g.weight k a = 0 := by
  have hk : collarPartialWeight g k a = 1 := by
    apply le_antisymm (collarPartialWeight_le_one g k a)
    rw [← hm]
    exact collarPartialWeight_mono_of_le g a hmk
  have hsucc := collarPartialWeight_le_one g (k + 1) a
  rw [collarPartialWeight_succ, hk] at hsucc
  exact le_antisymm (by linarith) (g.weight.nonneg k a)

private theorem collarStripMap_not_mem_chartRange_of_not_mem
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (ha : z.1 ∉ (g.data k).carrier) : collarStripMap A z ∉ collarChartRange g k := by
  rintro ⟨w, hw⟩
  have hsneg : (collarStripMap A z).val.2 < 0 := by
    rw [collarStripMap_val]
    linarith [z.2.property.2]
  have hwneg : w.2.val < 0 := by
    by_contra h
    have hw0 : (collarExtendedChart (g.data k) w).val.2 = 0 := by
      rw [collarExtendedChart_val_of_nonneg (g.data k) w (le_of_not_gt h)]
    have := congrArg (fun y : collarExternal X A ↦ y.val.2) hw
    linarith
  have hfirst := congrArg (fun y : collarExternal X A ↦ y.val.1) hw
  rw [collarExtendedChart_val_of_nonpos (g.data k) w hwneg.le,
    collarStripMap_val] at hfirst
  apply ha
  have hza : w.1.val = z.1 := by
    apply Subtype.ext
    exact hfirst
  rw [← hza]
  exact w.1.property

private theorem collarGlobalPush_strip_eq_self_of_weight_eq_zero
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hw : g.weight k z.1 = 0) :
    collarGlobalPush hA g k (collarStripMap A z) = collarStripMap A z := by
  by_cases ha : z.1 ∈ (g.data k).carrier
  · let s : Set.Ico (-2 : ℝ) 1 :=
      ⟨z.2.val - 1, by linarith [z.2.property.1], by linarith [z.2.property.2]⟩
    let w : (g.data k).carrier × Set.Ico (-2 : ℝ) 1 := (⟨z.1, ha⟩, s)
    have hchart : collarExtendedChart (g.data k) w = collarStripMap A z := by
      apply Subtype.ext
      rw [collarExtendedChart_val_of_nonpos (g.data k) w
        (by dsimp [w, s]; linarith [z.2.property.2]), collarStripMap_val]
    rw [← hchart, collarGlobalPush_chart hA g k,
      collarChartPush_eq_self_of_weight_eq_zero g k w]
    exact hw
  · exact collarGlobalPush_eq_self_of_not_mem_range hA g k _
      (collarStripMap_not_mem_chartRange_of_not_mem g k z ha)

private theorem collarGlobalPush_symm_strip_eq_self_of_weight_eq_zero
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hw : g.weight k z.1 = 0) :
    (collarGlobalPush hA g k).symm (collarStripMap A z) = collarStripMap A z := by
  apply (collarGlobalPush hA g k).injective
  rw [(collarGlobalPush hA g k).apply_symm_apply]
  exact (collarGlobalPush_strip_eq_self_of_weight_eq_zero hA g k z hw).symm

private theorem collarPartialPush_symm_strip_stable
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (z : A × Set.Ico (0 : ℝ) 1) {m n : ℕ}
    (hm : collarPartialWeight g m z.1 = 1) (hmn : m ≤ n) :
    (collarPartialPush hA g n).symm (collarStripMap A z) =
      (collarPartialPush hA g m).symm (collarStripMap A z) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      change (collarPartialPush hA g n).symm
        ((collarGlobalPush hA g n).symm (collarStripMap A z)) = _
      rw [collarGlobalPush_symm_strip_eq_self_of_weight_eq_zero hA g n z
        (collarWeight_eq_zero_of_partial_eq_one g z.1 hm hmn)]
      exact ih

private theorem collarFiniteMap_eq_of_partial_eq_one
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (z : A × Set.Ico (0 : ℝ) 1) {m n : ℕ}
    (hm : collarPartialWeight g m z.1 = 1) (hn : collarPartialWeight g n z.1 = 1) :
    collarFiniteMap hA g m z = collarFiniteMap hA g n z := by
  let k := max m n
  have hmk : m ≤ k := le_max_left _ _
  have hnk : n ≤ k := le_max_right _ _
  have hmstable := collarPartialPush_symm_strip_stable hA g z hm hmk
  have hnstable := collarPartialPush_symm_strip_stable hA g z hn hnk
  exact congrArg (fun y : collarExternal X A ↦ y.val.1) (hmstable.symm.trans hnstable)

private theorem collarPartialWeight_eq_one_of_le
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) {m k : ℕ}
    (hm : collarPartialWeight g m a = 1) (hmk : m ≤ k) :
    collarPartialWeight g k a = 1 := by
  apply le_antisymm (collarPartialWeight_le_one g k a)
  rw [← hm]
  exact collarPartialWeight_mono_of_le g a hmk

private theorem collarExistsPartialWeightEqOne
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) :
    ∃ m, collarPartialWeight g m a = 1 := by
  obtain ⟨m, hm⟩ := collarPartialWeight_eventually_eq_one g a
  exact ⟨m, hm.eq_of_nhds⟩

private def collarStageIndex
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) : ℕ :=
  (collarExistsPartialWeightEqOne g a).choose

private theorem collarStageIndex_spec
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) :
    collarPartialWeight g (collarStageIndex g a) a = 1 :=
  (collarExistsPartialWeightEqOne g a).choose_spec

private def collarGluedMap
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (z : A × Set.Ico (0 : ℝ) 1) : X :=
  collarFiniteMap hA g (collarStageIndex g z.1) z

private theorem collarGluedMap_eq_finite
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hm : collarPartialWeight g m z.1 = 1) :
    collarGluedMap hA g z = collarFiniteMap hA g m z := by
  exact collarFiniteMap_eq_of_partial_eq_one hA g z
    (collarStageIndex_spec g z.1) hm

private theorem collarFiniteMap_continuous
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) : Continuous (collarFiniteMap hA g m) := by
  exact (continuous_fst.comp continuous_subtype_val).comp
    ((collarPartialPush hA g m).symm.continuous.comp collarStripMap_isEmbedding.continuous)

private theorem collarGluedMap_continuous
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) : Continuous (collarGluedMap hA g) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨m, hm⟩ := collarPartialWeight_eventually_eq_one g z.1
  have hmevent : ∀ᶠ w in 𝓝 z, collarPartialWeight g m w.1 = 1 :=
    continuousAt_fst.eventually hm
  have heq : collarGluedMap hA g =ᶠ[𝓝 z] collarFiniteMap hA g m := by
    filter_upwards [hmevent] with w hw
    exact collarGluedMap_eq_finite hA g m w hw
  exact (collarFiniteMap_continuous hA g m).continuousAt.congr_of_eventuallyEq heq

private theorem collarGluedMap_injective
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) : Function.Injective (collarGluedMap hA g) := by
  intro z w hzw
  let m := collarStageIndex g z.1
  let n := collarStageIndex g w.1
  let k := max m n
  have hzm : collarPartialWeight g m z.1 = 1 := collarStageIndex_spec g z.1
  have hwn : collarPartialWeight g n w.1 = 1 := collarStageIndex_spec g w.1
  have hzk : collarPartialWeight g k z.1 = 1 :=
    collarPartialWeight_eq_one_of_le g z.1 hzm (le_max_left _ _)
  have hwk : collarPartialWeight g k w.1 = 1 :=
    collarPartialWeight_eq_one_of_le g w.1 hwn (le_max_right _ _)
  have hfinite : collarFiniteMap hA g k z = collarFiniteMap hA g k w := by
    rw [← collarGluedMap_eq_finite hA g k z hzk,
      ← collarGluedMap_eq_finite hA g k w hwk]
    exact hzw
  apply collarStripMap_isEmbedding.injective
  rw [← collarFiniteMap_recover hA g k z hzk,
    ← collarFiniteMap_recover hA g k w hwk, hfinite]

private def collarAnchor
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) : collarExternal X A :=
  ⟨(a.val, -collarPartialWeight g m a), Or.inr ⟨a.property,
    by linarith [collarPartialWeight_le_one g m a],
    by linarith [collarPartialWeight_nonneg g m a]⟩⟩

private theorem collarAnchor_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) :
    collarAnchor g 0 a = collarExternalBase A a.val := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change -collarPartialWeight g 0 a = 0
    rw [collarPartialWeight_zero]
    norm_num

private theorem collarExtendedChart_anchor
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k m : ℕ) (a : A)
    (ha : a ∈ (g.data k).carrier) :
    collarExtendedChart (g.data k) (⟨a, ha⟩, collarPartialAnchor g m a) =
      collarAnchor g m a := by
  apply Subtype.ext
  rw [collarExtendedChart_val_of_nonpos (g.data k)
    (⟨a, ha⟩, collarPartialAnchor g m a)
    (by change -collarPartialWeight g m a ≤ 0
        linarith [collarPartialWeight_nonneg g m a])]
  rfl

private theorem collarAnchor_not_mem_chartRange_of_not_mem
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k m : ℕ) (a : A)
    (ha : a ∉ (g.data k).carrier) : collarAnchor g m a ∉ collarChartRange g k := by
  rintro ⟨z, hz⟩
  have hs : z.2.val ≤ 0 := by
    by_contra hs
    have hs' : 0 < z.2.val := lt_of_not_ge hs
    have hfirst := congrArg (fun y : collarExternal X A ↦ y.val.1) hz
    rw [collarExtendedChart_val_of_pos (g.data k) z hs'] at hfirst
    have hfirst' : (g.data k).map
        (z.1, ⟨z.2.val, hs'.le, z.2.property.2⟩) = a.val := by
      simpa [collarAnchor] using hfirst
    have hmem : (g.data k).map
        (z.1, ⟨z.2.val, hs'.le, z.2.property.2⟩) ∈ A := by
      rw [hfirst']
      exact a.property
    exact (g.data k).map_not_mem
      (z.1, ⟨z.2.val, hs'.le, z.2.property.2⟩) hs'
      hmem
  have hfirst := congrArg (fun y : collarExternal X A ↦ y.val.1) hz
  rw [collarExtendedChart_val_of_nonpos (g.data k) z hs] at hfirst
  apply ha
  have haz : z.1.val = a := by
    apply Subtype.ext
    exact hfirst
  rw [← haz]
  exact z.1.property

private theorem collarGlobalPush_anchor
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) (a : A) :
    collarGlobalPush hA g k (collarAnchor g k a) = collarAnchor g (k + 1) a := by
  by_cases ha : a ∈ (g.data k).carrier
  · rw [← collarExtendedChart_anchor g k k a ha,
      collarGlobalPush_chart hA g k, collarChartPush_anchor g k ⟨a, ha⟩,
      collarExtendedChart_anchor g k (k + 1) a ha]
  · have hw : g.weight k a = 0 := by
      by_contra hw
      exact ha (g.subordinate k (subset_closure hw))
    rw [collarGlobalPush_eq_self_of_not_mem_range hA g k _
      (collarAnchor_not_mem_chartRange_of_not_mem g k k a ha)]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change -collarPartialWeight g k a = -collarPartialWeight g (k + 1) a
      rw [collarPartialWeight_succ, hw, add_zero]

private theorem collarPartialPush_anchor
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (a : A) :
    collarPartialPush hA g m (collarExternalBase A a.val) = collarAnchor g m a := by
  induction m with
  | zero => exact (collarAnchor_zero g a).symm
  | succ k ih =>
      rw [collarPartialPush_succ_apply, ih, collarGlobalPush_anchor hA g k a]

private theorem collarStripMap_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A)
    (hm : collarPartialWeight g m a = 1) :
    collarStripMap A (a, ⟨(0 : ℝ), by simp⟩) = collarAnchor g m a := by
  apply Subtype.ext
  rw [collarStripMap_val]
  apply Prod.ext
  · rfl
  · change (0 : ℝ) - 1 = -collarPartialWeight g m a
    rw [hm]
    ring

private theorem collarGluedMap_zero
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (a : A) :
    collarGluedMap hA g (a, ⟨(0 : ℝ), by simp⟩) = a.val := by
  let m := collarStageIndex g a
  let z : A × Set.Ico (0 : ℝ) 1 := (a, ⟨0, by simp⟩)
  have hm : collarPartialWeight g m a = 1 := collarStageIndex_spec g a
  have hrecover := collarFiniteMap_recover hA g m z hm
  have hglued : collarGluedMap hA g z = collarFiniteMap hA g m z :=
    collarGluedMap_eq_finite hA g m z hm
  have hanchor := collarPartialPush_anchor hA g m a
  rw [← collarStripMap_zero g m a hm, ← hrecover] at hanchor
  have hbase := (collarPartialPush hA g m).injective hanchor
  have hfst := congrArg (fun y : collarExternal X A ↦ y.val.1) hbase
  change a.val = collarFiniteMap hA g m z at hfst
  change collarGluedMap hA g z = a.val
  rw [hglued]
  exact hfst.symm

private def collarStageHomeomorph
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) : X ≃ₜ collarStage g m :=
  (collarExternalBase_isClosedEmbedding hA).isEmbedding.toHomeomorph |>.trans
    ((Homeomorph.image (collarPartialPush hA g m) (range (collarExternalBase A))).trans
      (Homeomorph.setCongr (collarPartialPush_image_base hA g m)))

private theorem collarStageHomeomorph_apply_val
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (x : X) :
    (collarStageHomeomorph hA g m x).val =
      collarPartialPush hA g m (collarExternalBase A x) := by
  rfl

private def collarStageStrip
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A)
    (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
    W × Set.Ico (0 : ℝ) 1 → collarStage g m :=
  fun z ↦ ⟨collarStripMap A (z.1.val, z.2),
    collarStripMap_mem_stage g m (z.1.val, z.2) (hm z.1.val z.1.property)⟩

private theorem collarStageStrip_isEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A)
    (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
    Topology.IsEmbedding (collarStageStrip g m W hm) := by
  apply Topology.IsEmbedding.of_comp
    (Continuous.subtype_mk
      (collarStripMap_isEmbedding.continuous.comp
        (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)) _)
    continuous_subtype_val
  change Topology.IsEmbedding
    (collarStripMap A ∘ fun z : W × Set.Ico (0 : ℝ) 1 ↦ (z.1.val, z.2))
  exact collarStripMap_isEmbedding.comp
    (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id)

private theorem collarStageStrip_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A) (hW : IsOpen W)
    (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
    Topology.IsOpenEmbedding (collarStageStrip g m W hm) := by
  refine ⟨collarStageStrip_isEmbedding g m W hm, ?_⟩
  obtain ⟨O, hOopen, hOW⟩ := isOpen_induced_iff.mp hW
  let V : Set (collarStage g m) :=
    {y | y.val.val.1 ∈ O ∧ y.val.val.2 < 0}
  have hV : IsOpen V :=
    (hOopen.preimage
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))).inter
      (isOpen_lt
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)) continuous_const)
  rw [show range (collarStageStrip g m W hm) = V by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change z.1.val.val ∈ O ∧ z.2.val - 1 < 0
      exact ⟨(Set.ext_iff.mp hOW z.1.val).mpr z.1.property,
        by linarith [z.2.property.2]⟩
    · rintro ⟨hyO, hyneg⟩
      let a : A := ⟨y.val.val.1, collarExternal_fst_mem_of_snd_lt y.val hyneg⟩
      have haW : a ∈ W := by
        exact (Set.ext_iff.mp hOW a).mp hyO
      have hbound : -1 ≤ y.val.val.2 := by
        rcases y.property with hy0 | ⟨ha, ha'⟩
        · exact (ne_of_lt hyneg hy0).elim
        · have haa : (⟨y.val.val.1, ha⟩ : A) = a := by
            apply Subtype.ext
            rfl
          rw [haa, hm a haW] at ha'
          exact ha'
      let t : Set.Ico (0 : ℝ) 1 :=
        ⟨y.val.val.2 + 1, by linarith, by linarith⟩
      let z : W × Set.Ico (0 : ℝ) 1 := (⟨a, haW⟩, t)
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change collarStripMap A (z.1.val, z.2) = y.val
      apply Subtype.ext
      rw [collarStripMap_val]
      apply Prod.ext
      · rfl
      · dsimp [t]
        ring]
  exact hV

private def collarFiniteMapOn
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A) :
    W × Set.Ico (0 : ℝ) 1 → X :=
  fun z ↦ collarFiniteMap hA g m (z.1.val, z.2)

private theorem collarFiniteMapOn_eq
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A)
    (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
    collarFiniteMapOn hA g m W =
      (collarStageHomeomorph hA g m).symm ∘ collarStageStrip g m W hm := by
  funext z
  apply (collarStageHomeomorph hA g m).injective
  simp only [Function.comp_apply]
  rw [(collarStageHomeomorph hA g m).apply_symm_apply]
  apply Subtype.ext
  rw [collarStageHomeomorph_apply_val]
  exact collarFiniteMap_recover hA g m (z.1.val, z.2) (hm z.1.val z.1.property)

private theorem collarFiniteMapOn_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A) (hW : IsOpen W)
    (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
    Topology.IsOpenEmbedding (collarFiniteMapOn hA g m W) := by
  rw [collarFiniteMapOn_eq hA g m W hm]
  exact (collarStageHomeomorph hA g m).symm.isOpenEmbedding.comp
    (collarStageStrip_isOpenEmbedding g m W hW hm)

private theorem collarGluedMap_isOpenMap
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) : IsOpenMap (collarGluedMap hA g) := by
  intro S hS
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hzS, rfl⟩
  obtain ⟨m, hm⟩ := collarPartialWeight_eventually_eq_one g z.1
  obtain ⟨W, hWsub, hWopen, hzW⟩ := mem_nhds_iff.mp hm
  have hmW : ∀ a ∈ W, collarPartialWeight g m a = 1 := fun a ha ↦ hWsub ha
  let inc : W × Set.Ico (0 : ℝ) 1 → A × Set.Ico (0 : ℝ) 1 :=
    fun w ↦ (w.1.val, w.2)
  have hinc : Topology.IsOpenEmbedding inc :=
    hWopen.isOpenEmbedding_subtypeVal.prodMap Topology.IsOpenEmbedding.id
  let T : Set (W × Set.Ico (0 : ℝ) 1) := inc ⁻¹' S
  have hT : IsOpen T := hS.preimage hinc.continuous
  have hopen : IsOpen (collarFiniteMapOn hA g m W '' T) :=
    (collarFiniteMapOn_isOpenEmbedding hA g m W hWopen hmW).isOpenMap T hT
  let w : W × Set.Ico (0 : ℝ) 1 := (⟨z.1, hzW⟩, z.2)
  have hwT : w ∈ T := hzS
  have hcontains : collarGluedMap hA g z ∈ collarFiniteMapOn hA g m W '' T := by
    refine ⟨w, hwT, ?_⟩
    exact (collarGluedMap_eq_finite hA g m z (hmW z.1 hzW)).symm
  apply mem_of_superset (hopen.mem_nhds hcontains)
  rintro y ⟨q, hqT, rfl⟩
  let v : A × Set.Ico (0 : ℝ) 1 := inc q
  have hvS : v ∈ S := hqT
  refine ⟨v, hvS, ?_⟩
  exact collarGluedMap_eq_finite hA g m v (hmW q.1.val q.1.property)

private theorem collarGluedMap_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) : Topology.IsOpenEmbedding (collarGluedMap hA g) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (collarGluedMap_continuous hA g) (collarGluedMap_injective hA g)
    (collarGluedMap_isOpenMap hA g)

private theorem collarAbstractGluing
    {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {A : Set X} [Nonempty A] [LindelofSpace A] [LocallyCompactSpace A]
    [RegularSpace A] [NormalSpace A] [ParacompactSpace A]
    (hA : IsClosed A)
    (hlocal : ∀ a : A, ∃ d : collarLocalData X A, a ∈ d.carrier) :
    ∃ c : A × Set.Ico (0 : ℝ) 1 → X,
      Topology.IsOpenEmbedding c ∧
        ∀ a : A, c (a, ⟨(0 : ℝ), by simp⟩) = a.val := by
  obtain ⟨g⟩ := collarExistsGluingCover hlocal
  obtain ⟨g'⟩ := collarExistsControlledCover hA g
  obtain ⟨g''⟩ := collarPrepareCover g'
  exact ⟨collarGluedMap hA g'', collarGluedMap_isOpenEmbedding hA g'',
    collarGluedMap_zero hA g''⟩

/--
**Collar neighborhood theorem (topological form).** Let $n \ge 1$ and let $M$ be a Hausdorff,
second-countable smooth ($C^\infty$) manifold with boundary modeled on the closed half-space
$\{x \in \mathbb{R}^n : x_1 \ge 0\}$, and let $\partial M$ be its boundary. Then there is an open
embedding $c : \partial M \times [0, 1) \to M$ such that $c(b, 0) = b$ for every $b \in \partial M$.

Proves `Wanted` entry `topological_collar_neighborhood_of_smooth_manifold_with_boundary`.

Proof: Local chart collars are glued by Brown's external-collar construction, following Hatcher,
*Algebraic Topology*, Proposition 3.42, and the locally finite extension of Connelly (1971).

Source: M. Hirsch, Differential Topology, GTM 33; J. Lee, Introduction to
Smooth Manifolds, 2nd ed.; Kosinski, Differential Manifolds; Lean states topological collar
`IsOpenEmbedding` corollary for `EuclideanHalfSpace` model.
-/
theorem topological_collar_neighborhood_of_smooth_manifold_with_boundary
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] [T2Space M] [SecondCountableTopology M] :
    ∃ (c : (↥(ModelWithCorners.boundary (I := 𝓡∂ n) M) × ↥(Set.Ico (0 : ℝ) 1)) → M),
      Topology.IsOpenEmbedding c ∧
        ∀ (b : ↥(ModelWithCorners.boundary (I := 𝓡∂ n) M)),
          c (b, ⟨(0 : ℝ), by simp [Set.mem_Ico]⟩) = b.val := by
  classical
  let A : Set M := ModelWithCorners.boundary (I := 𝓡∂ n) M
  change ∃ c : A × Set.Ico (0 : ℝ) 1 → M,
    Topology.IsOpenEmbedding c ∧ ∀ b : A, c (b, ⟨(0 : ℝ), by simp⟩) = b.val
  have hA : IsClosed A := collarBoundary_isClosed (n := n) (M := M)
  rcases isEmpty_or_nonempty A with hEmpty | hNonempty
  · let _ : IsEmpty A := hEmpty
    let c : A × Set.Ico (0 : ℝ) 1 → M := fun z ↦ isEmptyElim z.1
    refine ⟨c, ?_, fun b ↦ isEmptyElim b⟩
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact continuous_of_discreteTopology
    · intro z
      exact isEmptyElim z.1
    · intro S _
      have hS : S = ∅ := eq_empty_iff_forall_notMem.mpr fun z _ ↦ isEmptyElim z.1
      rw [hS, image_empty]
      exact isOpen_empty
  · let _ : Nonempty A := hNonempty
    let _ : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (𝓡∂ n)
    let _ : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
    let _ : ParacompactSpace M := collarParacompactSpace (n := n) (M := M)
    let _ : LocallyCompactSpace A := hA.locallyCompactSpace
    let _ : ParacompactSpace A :=
      collarBoundaryParacompactSpace (n := n) (M := M)
    exact collarAbstractGluing hA (collarExistsLocalData (n := n) (M := M))

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
