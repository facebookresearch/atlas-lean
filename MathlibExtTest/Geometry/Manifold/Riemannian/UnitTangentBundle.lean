/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.FiberBundle.Separation
import MathlibExt.Geometry.Manifold.Riemannian.UnitTangentBundle
import MathlibExt.Dynamics.TopologicalEntropy.Compact
import MathlibExt.Geometry.Manifold.RiemannianMetricExistence
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Tests for Hausdorff total spaces and compact unit tangent bundles

This file tests `FiberBundle.t2Space_totalSpace` on tangent bundles and
`Manifold.isCompact_unitTangentBundle` on the 2-sphere with a smooth metric
from existence, including compactness and nonemptiness of the unit tangent
bundle. The near-miss over `ℝ` matters because it shows the compact-base
hypothesis cannot be dropped: every real is the base of a unit vector, so a
compact unit tangent bundle would make `ℝ` compact.
-/

open Bundle
open scoped Manifold ContDiff

namespace UnitTangentBundleTests

/-- The 2-sphere as a subtype of `EuclideanSpace ℝ (Fin 3)`. -/
abbrev S2 : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1)

/-- Instance check: the tangent bundle over `S2` is Hausdorff. -/
example : T2Space (TangentBundle (𝓡 2) S2) := inferInstance

/-- Instance check: the tangent bundle over a Euclidean space is Hausdorff. -/
example : T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
    (EuclideanSpace ℝ (Fin 2))) := inferInstance

/-- Abbreviation for smooth metrics on `S2`. -/
abbrev MetS2 :=
  Bundle.ContMDiffRiemannianMetric (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
    (fun x : S2 ↦ TangentSpace (𝓡 2) x)

/-- A smooth background metric on `S2` from existence. -/
noncomputable def sphereMetric0 : MetS2 :=
  Classical.choice
    (MathlibExt.Geometry.Manifold.RiemannianMetricExistenceWanted.riemannianMetricExistence
      (I := 𝓡 2) (M := S2))

/-- Continuous version of the background metric on `S2`. -/
noncomputable def sphereCont : Bundle.ContinuousRiemannianMetric
    (EuclideanSpace ℝ (Fin 2)) (fun x : S2 ↦ TangentSpace (𝓡 2) x) :=
  sphereMetric0.toContinuousRiemannianMetric

/-- The background metric installed as a Riemannian bundle. -/
noncomputable instance sphereRiem : Bundle.RiemannianBundle
    (fun x : S2 ↦ TangentSpace (𝓡 2) x) :=
  ⟨sphereMetric0.toContinuousRiemannianMetric.toRiemannianMetric⟩

/-- Smooth metric on `S2` as a plain def with maximal regularity. -/
noncomputable def sphereSmoothTop :
    Bundle.ContMDiffRiemannianMetric (𝓡 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (fun x : S2 ↦ TangentSpace (𝓡 2) x) :=
  sphereMetric0

/-- The unit tangent bundle of `S2` is compact. -/
theorem sphere_isCompact :
    IsCompact (Manifold.unitTangentBundle (𝓡 2) S2) :=
  Manifold.isCompact_unitTangentBundle

/-- Instance check: the unit tangent bundle over `S2` is a compact space. -/
example : CompactSpace ↥(Manifold.unitTangentBundle (𝓡 2) S2) :=
  inferInstance

/-- Instance check: the unit tangent bundle over `S2` is an `R1` space. -/
example : R1Space ↥(Manifold.unitTangentBundle (𝓡 2) S2) :=
  inferInstance

/-- The unit tangent bundle of `S2` is nonempty: a rescaled tangent vector. -/
theorem sphere_nonempty :
    (Manifold.unitTangentBundle (𝓡 2) S2).Nonempty := by
  obtain ⟨w, hw⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin (2 + 1)))
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hCpos : 0 < (‖w‖)⁻¹ := inv_pos.mpr hpos
  have hxvec_norm : ‖(‖w‖)⁻¹ • w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hCpos]
    exact inv_mul_cancel₀ (ne_of_gt hpos)
  have hxvec_mem :
      (‖w‖)⁻¹ • w ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact hxvec_norm
  let x0 : S2 := ⟨(‖w‖)⁻¹ • w, hxvec_mem⟩
  obtain ⟨w0, hw0⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 2))
  let e := trivializationAt (EuclideanSpace ℝ (Fin 2))
    (fun y : S2 ↦ TangentSpace (𝓡 2) y) x0
  have hb : x0 ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  let equiv := Bundle.Trivialization.continuousLinearEquivAt ℝ e x0 hb
  have hv0_ne : equiv w0 ≠ 0 := by
    intro h
    apply hw0
    have h0 : equiv w0 = equiv 0 := by
      rw [h, map_zero]
    exact equiv.toLinearEquiv.injective h0
  let v : TangentSpace (𝓡 2) x0 := equiv w0
  have hv_ne : v ≠ 0 := hv0_ne
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have hvinv_pos : 0 < (‖v‖)⁻¹ := inv_pos.mpr hvpos
  have hv_norm : ‖(‖v‖)⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hvinv_pos]
    exact inv_mul_cancel₀ (ne_of_gt hvpos)
  have hmem : (⟨x0, (‖v‖)⁻¹ • v⟩ : TangentBundle (𝓡 2) S2) ∈
      Manifold.unitTangentBundle (𝓡 2) S2 := by
    show ‖(‖v‖)⁻¹ • v‖ = 1
    exact hv_norm
  exact ⟨⟨x0, (‖v‖)⁻¹ • v⟩, hmem⟩

/-- The unit tangent bundle over `ℝ` is not compact: the base is not compact. -/
theorem not_isCompact_R :
    ¬ IsCompact (Manifold.unitTangentBundle 𝓘(ℝ, ℝ) ℝ) := by
  intro h
  have hcont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle 𝓘(ℝ, ℝ) ℝ → ℝ) :=
    FiberBundle.continuous_proj _ _
  have himg : IsCompact
      (Bundle.TotalSpace.proj '' Manifold.unitTangentBundle 𝓘(ℝ, ℝ) ℝ) :=
    h.image hcont
  have hsurj : Bundle.TotalSpace.proj ''
      Manifold.unitTangentBundle 𝓘(ℝ, ℝ) ℝ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨w0, hw0⟩ := exists_ne (0 : ℝ)
    let e := trivializationAt ℝ (fun y : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) y) x
    have hb : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    let equiv := Bundle.Trivialization.continuousLinearEquivAt ℝ e x hb
    have hv0_ne : equiv w0 ≠ 0 := by
      intro h0eq
      apply hw0
      have h0 : equiv w0 = equiv 0 := by
        rw [h0eq, map_zero]
      exact equiv.toLinearEquiv.injective h0
    let v : TangentSpace 𝓘(ℝ, ℝ) x := equiv w0
    have hv_ne : v ≠ 0 := hv0_ne
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    have hvinv_pos : 0 < (‖v‖)⁻¹ := inv_pos.mpr hvpos
    have hv_norm : ‖(‖v‖)⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hvinv_pos]
      exact inv_mul_cancel₀ (ne_of_gt hvpos)
    have hmem : (⟨x, (‖v‖)⁻¹ • v⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) ∈
        Manifold.unitTangentBundle 𝓘(ℝ, ℝ) ℝ := by
      show ‖(‖v‖)⁻¹ • v‖ = 1
      exact hv_norm
    exact ⟨⟨x, (‖v‖)⁻¹ • v⟩, hmem, rfl⟩
  have huniv : IsCompact (Set.univ : Set ℝ) := hsurj ▸ himg
  have hbdd : Bornology.IsBounded (Set.univ : Set ℝ) := huniv.isBounded
  rw [Metric.isBounded_iff] at hbdd
  obtain ⟨C, hC⟩ := hbdd
  have hCnonneg : 0 ≤ C := by
    have h00 : dist (0 : ℝ) (0 : ℝ) ≤ C :=
      hC (Set.mem_univ (0 : ℝ)) (Set.mem_univ (0 : ℝ))
    rw [dist_self] at h00
    exact h00
  have h0le : dist (0 : ℝ) (C + 1) ≤ C :=
    hC (Set.mem_univ (0 : ℝ)) (Set.mem_univ (C + 1))
  rw [Real.dist_eq] at h0le
  have hpos : 0 < C + 1 := by
    linarith
  have habs : |0 - (C + 1)| = C + 1 := by
    rw [zero_sub, abs_neg, abs_of_pos hpos]
  rw [habs] at h0le
  linarith

/-- Statement shape for positive entropy of the time-one geodesic flow on `S2`. -/
noncomputable def PosEntropy : Prop :=
  ∀ φ : ℝ → ↥(Manifold.unitTangentBundle (𝓡 2) S2) →
    ↥(Manifold.unitTangentBundle (𝓡 2) S2),
    letI : IsContMDiffRiemannianBundle (𝓡 2) 1 (EuclideanSpace ℝ (Fin 2))
        (fun x : S2 ↦ TangentSpace (𝓡 2) x) :=
      ⟨sphereMetric0.inner, sphereMetric0.contMDiff.of_le
        (WithTop.coe_le_coe.mpr le_top), fun _ _ _ => rfl⟩;
    Manifold.IsUnitGeodesicFlow (𝓡 2) φ →
      0 < Dynamics.topologicalEntropy (φ 1)

end UnitTangentBundleTests
