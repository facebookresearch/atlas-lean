/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow

/-!
# The unit tangent bundle

For a continuous Riemannian metric on the tangent bundle, the unit tangent bundle is closed
in the tangent bundle: it is the preimage of `{1}` under the continuous fiberwise
norm-squared map. When the model space is finite-dimensional, the fiberwise linear maps of
the tangent-bundle trivialization at a point are uniformly bounded in operator norm on a
compact neighbourhood contained in the trivialization base set, and the unit vectors over
a neighbourhood of any point form a compact set. If the base manifold is compact, the unit
tangent bundle itself is compact.
-/

@[expose] public section

open Bundle
open scoped Topology

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The unit tangent bundle is closed in the tangent bundle. The map sending a tangent
vector to the inner product of its fiber component with itself is continuous for a
continuous Riemannian metric, and the unit tangent bundle is the preimage of `{1}` under
the corresponding norm-squared map. -/
theorem isClosed_unitTangentBundle : IsClosed (unitTangentBundle I M) := by
  have hid : Continuous (fun p : TangentBundle I M => (⟨p.proj, p.snd⟩ : TangentBundle I M)) :=
    continuous_id
  have hcont : Continuous (fun p : TangentBundle I M => inner ℝ p.snd p.snd) :=
    Continuous.inner_bundle hid hid
  have hset : unitTangentBundle I M
      = (fun p : TangentBundle I M => inner ℝ p.snd p.snd) ⁻¹' {1} := by
    ext p
    simp only [unitTangentBundle, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    rw [real_inner_self_eq_norm_sq]
    constructor
    · intro h
      rw [h]
      norm_num
    · intro h
      rw [sq_eq_one_iff] at h
      rcases h with h | h
      · exact h
      · have hnn := norm_nonneg p.snd
        linarith
  rw [hset]
  exact IsClosed.preimage hcont isClosed_singleton

/-- Near `x`, the fiberwise linear maps of the tangent-bundle trivialization at `x` are
uniformly bounded in operator norm on a compact neighbourhood in its base set. -/
private theorem exists_isCompact_mem_nhds_norm_trivializationAt_le [FiniteDimensional ℝ E]
    (x : M) :
    ∃ K ∈ 𝓝 x, IsCompact K ∧
      K ⊆ (trivializationAt E (fun y : M ↦ TangentSpace I y) x).baseSet ∧
      ∃ C : ℝ, ∀ y ∈ K, ∀ v : TangentSpace I y,
        ‖(trivializationAt E (fun y : M ↦ TangentSpace I y)
          x).continuousLinearMapAt ℝ y v‖ ≤ C * ‖v‖ := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  have : LocallyCompactSpace H := ModelWithCorners.locallyCompactSpace I
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨C, _, hC⟩ :=
    eventually_norm_trivializationAt_lt E (fun y : M ↦ TangentSpace I y) x
  obtain ⟨U, hUmem, hUbound⟩ := Filter.Eventually.exists_mem hC
  have hbase_mem :
      (trivializationAt E (fun y : M ↦ TangentSpace I y) x).baseSet ∈ 𝓝 x :=
    IsOpen.mem_nhds
      (Bundle.Trivialization.open_baseSet
        (trivializationAt E (fun y : M ↦ TangentSpace I y) x))
      (mem_baseSet_trivializationAt E (fun y : M ↦ TangentSpace I y) x)
  have hinter :
      U ∩ (trivializationAt E (fun y : M ↦ TangentSpace I y) x).baseSet ∈ 𝓝 x :=
    Filter.inter_mem hUmem hbase_mem
  obtain ⟨K, hKmem, hKsub, hKcompact⟩ := local_compact_nhds hinter
  refine ⟨K, hKmem, hKcompact, fun y hy => (hKsub hy).2, C, fun y hy v => ?_⟩
  have hlt :
      ‖(trivializationAt E (fun y : M ↦ TangentSpace I y)
        x).continuousLinearMapAt ℝ y‖ < C :=
    hUbound y (hKsub hy).1
  calc ‖(trivializationAt E (fun y : M ↦ TangentSpace I y)
          x).continuousLinearMapAt ℝ y v‖
      ≤ ‖(trivializationAt E (fun y : M ↦ TangentSpace I y)
          x).continuousLinearMapAt ℝ y‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt hlt) (norm_nonneg _)

/-- Every point has a neighbourhood over which the unit tangent vectors form a compact
set. The unit vectors over `K` are the intersection of the closed unit tangent bundle
with a compact trivialization image, hence compact. -/
theorem exists_mem_nhds_isCompact_unitTangentBundle_inter [FiniteDimensional ℝ E]
    (x : M) :
    ∃ K ∈ 𝓝 x, IsCompact (unitTangentBundle I M ∩ Bundle.TotalSpace.proj ⁻¹' K) := by
  obtain ⟨K, hKmem, hKcompact, hKbase, C, hC⟩ :=
    exists_isCompact_mem_nhds_norm_trivializationAt_le (E := E) (H := H) (I := I) x
  have : ProperSpace E := FiniteDimensional.proper_real E
  set e := trivializationAt E (fun y : M ↦ TangentSpace I y) x
  have hTcompact : IsCompact (K ×ˢ Metric.closedBall (0 : E) C) :=
    hKcompact.prod (isCompact_closedBall 0 C)
  have hTsub :
      K ×ˢ Metric.closedBall (0 : E) C ⊆ e.toOpenPartialHomeomorph.target := by
    intro yw hyw
    rw [Bundle.Trivialization.mem_target]
    exact hKbase hyw.1
  have hcont : ContinuousOn (e.toOpenPartialHomeomorph.symm)
      (K ×ˢ Metric.closedBall (0 : E) C) :=
    (e.toOpenPartialHomeomorph.continuousOn_symm).mono hTsub
  have hLcompact :
      IsCompact
        (e.toOpenPartialHomeomorph.symm '' (K ×ˢ Metric.closedBall (0 : E) C)) :=
    hTcompact.image_of_continuousOn hcont
  have heq :
      unitTangentBundle I M ∩ Bundle.TotalSpace.proj ⁻¹' K =
        unitTangentBundle I M ∩
          e.toOpenPartialHomeomorph.symm '' (K ×ˢ Metric.closedBall (0 : E) C) := by
    ext p
    constructor
    · intro hp
      have hprojK : p.proj ∈ K := hp.2
      have hnorm1 : ‖p.snd‖ = 1 := hp.1
      have hb : p.proj ∈ e.baseSet := hKbase hprojK
      have hsrc : p ∈ e.source :=
        (Bundle.Trivialization.mem_source e).mpr hb
      have hsrcOPH : p ∈ e.toOpenPartialHomeomorph.source := hsrc
      have hfst : (e.toOpenPartialHomeomorph p).1 ∈ K := by
        have h1 := Bundle.Trivialization.proj_toFun e p hsrc
        rw [h1]
        exact hprojK
      have hle : ‖(Bundle.Trivialization.continuousLinearMapAt ℝ e p.proj)
          p.snd‖ ≤ C := by
        have h1 := hC p.proj hprojK p.snd
        rw [hnorm1, mul_one] at h1
        exact h1
      have hcoord : (e.toOpenPartialHomeomorph p).2 =
          (Bundle.Trivialization.continuousLinearMapAt ℝ e p.proj) p.snd := by
        have h1 := Bundle.Trivialization.apply_eq_prod_continuousLinearEquivAt
          ℝ e p.proj hb p.snd
        have h2 := Bundle.Trivialization.continuousLinearMapAt_apply ℝ e p.proj
        have hcoe : (e.toOpenPartialHomeomorph p).2 = (e p).2 := by
          rw [Bundle.Trivialization.coe_coe]
        have hqeq : (e p).2 =
            (Bundle.Trivialization.continuousLinearEquivAt ℝ e p.proj hb)
              p.snd :=
          congrArg Prod.snd h1
        have hlink :
            (Bundle.Trivialization.continuousLinearEquivAt ℝ e p.proj hb)
              p.snd =
              (Bundle.Trivialization.linearMapAt ℝ e p.proj) p.snd := by
          rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq e hb,
            Bundle.Trivialization.continuousLinearMapAt_apply ℝ e p.proj]
        have hmap :
            (Bundle.Trivialization.continuousLinearMapAt ℝ e p.proj) p.snd =
              (Bundle.Trivialization.linearMapAt ℝ e p.proj) p.snd := by
          rw [h2]
        rw [hcoe, hqeq, hlink, ← hmap]
      have hball : (e.toOpenPartialHomeomorph p).2 ∈
          Metric.closedBall (0 : E) C := by
        rw [Metric.mem_closedBall, dist_zero_right, hcoord]
        exact hle
      have hmemT : (e.toOpenPartialHomeomorph p) ∈
          K ×ˢ Metric.closedBall (0 : E) C :=
        ⟨hfst, hball⟩
      have hinv : (e.toOpenPartialHomeomorph.symm)
          (e.toOpenPartialHomeomorph p) = p :=
        OpenPartialHomeomorph.left_inv _ hsrcOPH
      exact ⟨hp.1, ⟨_, hmemT, hinv⟩⟩
    · intro hp
      obtain ⟨q, hqT, hqp⟩ := hp.2
      have hqK : q.1 ∈ K := hqT.1
      have hqmem : q ∈ e.toOpenPartialHomeomorph.target := hTsub hqT
      have hright : e.toOpenPartialHomeomorph
          (e.toOpenPartialHomeomorph.symm q) = q :=
        OpenPartialHomeomorph.right_inv _ hqmem
      have hqsrc : e.toOpenPartialHomeomorph.symm q ∈
          e.toOpenPartialHomeomorph.source :=
        OpenPartialHomeomorph.map_target _ hqmem
      have hqsrcT : e.toOpenPartialHomeomorph.symm q ∈ e.source := hqsrc
      have hproj : (e.toOpenPartialHomeomorph
          (e.toOpenPartialHomeomorph.symm q)).1 =
          (e.toOpenPartialHomeomorph.symm q).proj :=
        Bundle.Trivialization.proj_toFun e _ hqsrcT
      have hpeq : p.proj = q.1 := by
        rw [← hqp, ← hproj, hright]
      have hprojK : p.proj ∈ K := by
        rw [hpeq]
        exact hqK
      exact ⟨hp.1, hprojK⟩
  refine ⟨K, hKmem, ?_⟩
  rw [heq, Set.inter_comm]
  exact hLcompact.inter_right isClosed_unitTangentBundle

/-- If the base manifold is compact and the model space is finite-dimensional, the unit
tangent bundle is compact: finitely many of the neighbourhoods over which the unit
vectors form a compact set cover the base. -/
theorem isCompact_unitTangentBundle [FiniteDimensional ℝ E] [CompactSpace M] :
    IsCompact (unitTangentBundle I M) := by
  choose K hKmem hKcompact using fun (x : M) =>
    exists_mem_nhds_isCompact_unitTangentBundle_inter (E := E) (H := H) (I := I) x
  obtain ⟨t, _, htsub⟩ :=
    isCompact_univ.elim_nhds_subcover K (fun x _ => hKmem x)
  have hUnion : IsCompact (⋃ x ∈ (↑t : Set M),
      (unitTangentBundle I M ∩ Bundle.TotalSpace.proj ⁻¹' K x)) :=
    Set.Finite.isCompact_biUnion (Finset.finite_toSet t) (fun x _ => hKcompact x)
  have hsub : unitTangentBundle I M ⊆ ⋃ x ∈ (↑t : Set M),
      (unitTangentBundle I M ∩ Bundle.TotalSpace.proj ⁻¹' K x) := by
    intro p hp
    have hprojFin : p.proj ∈ ⋃ x ∈ t, K x := htsub (Set.mem_univ _)
    simp only [Set.mem_iUnion] at hprojFin
    obtain ⟨x, hxtFin, hpx⟩ := hprojFin
    have hxt : x ∈ (↑t : Set M) := Finset.mem_coe.mpr hxtFin
    exact Set.mem_biUnion hxt ⟨hp, hpx⟩
  exact hUnion.of_isClosed_subset isClosed_unitTangentBundle hsub

/-- The unit tangent bundle over a compact manifold is a compact space. -/
instance compactSpace_unitTangentBundle [FiniteDimensional ℝ E] [CompactSpace M] :
    CompactSpace ↥(unitTangentBundle I M) :=
  isCompact_iff_compactSpace.mp isCompact_unitTangentBundle

end Manifold
