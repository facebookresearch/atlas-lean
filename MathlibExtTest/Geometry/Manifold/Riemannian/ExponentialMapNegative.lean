/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.ExponentialMap
import MathlibExt.Geometry.Manifold.Riemannian.GeodesicFlow.VectorSpace

/-!
# Exponential map near misses on the plane
-/

open Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace ExpMapNegTests

noncomputable section

/-- Doubled exponential candidate on the plane. -/
def doubleExp : (x : ℂ) → TangentSpace 𝓘(ℝ, ℂ) x → ℂ :=
  fun x v ↦ x + (2 : ℝ) • (NormedSpace.fromTangentSpace x v)

/-- Constant candidate on the plane. -/
def constExp : (x : ℂ) → TangentSpace 𝓘(ℝ, ℂ) x → ℂ :=
  fun x _ ↦ x

/-- The doubled map is not the Riemannian exponential map. -/
theorem not_exp_double : ¬ IsRiemannianExp 𝓘(ℝ, ℂ) doubleExp := by
  intro h
  let v0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ) :=
    (NormedSpace.fromTangentSpace (0 : ℂ)).symm (1 : ℂ)
  obtain ⟨u, hgeo, hu0, hray⟩ := h (0 : ℂ) v0
  have hvec := (isGeodesicVelocityCurve_vectorSpace_iff u).mp hgeo
  have hfrom0 : NormedSpace.fromTangentSpace (0 : ℂ) v0 = 1 := by
    simp [v0]
  have hfromU :
      NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd) = 1 := by
    rw [hu0]
    exact hfrom0
  have hproj0 : (u 0).proj = 0 := by rw [hu0]
  have h1 := (hvec 1).1
  have hray1 := hray 1
  have hmap :
      NormedSpace.fromTangentSpace (0 : ℂ) ((1 : ℝ) • v0) = 1 := by
    rw [map_smul, hfrom0, one_smul]
  have hL : doubleExp (0 : ℂ) ((1 : ℝ) • v0) = 0 + (2 : ℝ) • (1 : ℂ) := by
    simp only [doubleExp, hmap]
  have hRr : (u 1).proj = 0 + (1 : ℝ) • (1 : ℂ) := by
    rw [hfromU, hproj0] at h1
    exact h1
  rw [hL, hRr] at hray1
  have heq : (2 : ℝ) • (1 : ℂ) = (1 : ℝ) • (1 : ℂ) := by
    simpa only [zero_add] using hray1
  have hsub : ((2 : ℝ) - (1 : ℝ)) • (1 : ℂ) = 0 := by
    rw [sub_smul, heq, sub_self]
  have hdis := smul_eq_zero.mp hsub
  rcases hdis with h01 | h10
  · norm_num at h01
  · exact one_ne_zero h10

/-- The constant map is not the Riemannian exponential map. -/
theorem not_exp_const : ¬ IsRiemannianExp 𝓘(ℝ, ℂ) constExp := by
  intro h
  let v0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ) :=
    (NormedSpace.fromTangentSpace (0 : ℂ)).symm (1 : ℂ)
  obtain ⟨u, hgeo, hu0, hray⟩ := h (0 : ℂ) v0
  have hvec := (isGeodesicVelocityCurve_vectorSpace_iff u).mp hgeo
  have hfrom0 : NormedSpace.fromTangentSpace (0 : ℂ) v0 = 1 := by
    simp [v0]
  have hfromU :
      NormedSpace.fromTangentSpace ((u 0).proj) ((u 0).snd) = 1 := by
    rw [hu0]
    exact hfrom0
  have hproj0 : (u 0).proj = 0 := by rw [hu0]
  have h1 := (hvec 1).1
  have hray1 := hray 1
  simp only [constExp] at hray1
  have hRr : (u 1).proj = 0 + (1 : ℝ) • (1 : ℂ) := by
    rw [hfromU, hproj0] at h1
    exact h1
  rw [hRr] at hray1
  have heq : (0 : ℂ) = (1 : ℝ) • (1 : ℂ) := by
    simpa only [zero_add] using hray1
  have hsub : (1 : ℝ) • (1 : ℂ) = 0 := heq.symm
  have hdis := smul_eq_zero.mp hsub
  rcases hdis with h01 | h10
  · norm_num at h01
  · exact one_ne_zero h10

/-- The constant map has injectivity radius zero at the origin. -/
theorem radius_const_zero :
    Manifold.injectivityRadiusAt 𝓘(ℝ, ℂ) constExp (0 : ℂ) = 0 := by
  have hempty : Metric.eball (0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ))
      (0 : ℝ≥0∞) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    rw [Metric.mem_eball] at hy
    exact (not_lt_of_ge bot_le) hy
  have hmem : (0 : ℝ≥0∞) ∈ {a : ℝ≥0∞ |
      Set.InjOn (constExp (0 : ℂ)) (Metric.eball 0 a) ∧
      IsLocalDiffeomorphOn 𝓘(ℝ, TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) 𝓘(ℝ, ℂ) ∞
        (constExp (0 : ℂ)) (Metric.eball 0 a)} := by
    refine ⟨?_, ?_⟩
    · rw [hempty]
      exact Set.injOn_empty _
    · rw [hempty]
      intro x
      exact absurd x.2 (Set.notMem_empty _)
  have hle :
      Manifold.injectivityRadiusAt 𝓘(ℝ, ℂ) constExp (0 : ℂ) ≤ 0 := by
    apply sSup_le
    intro a ha
    by_contra hlt
    have hpos : (0 : ℝ≥0∞) < a := not_le.mp hlt
    have hne : a ≠ 0 := ne_of_gt hpos
    have h0mem : (0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) ∈ Metric.eball 0 a := by
      rw [Metric.mem_eball, edist_self]
      exact hpos
    let v0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ) :=
      (NormedSpace.fromTangentSpace (0 : ℂ)).symm (1 : ℂ)
    have hfrom0 : NormedSpace.fromTangentSpace (0 : ℂ) v0 = 1 := by
      simp [v0]
    have hv0ne : v0 ≠ 0 := by
      intro hcon
      have h1 := congrArg (NormedSpace.fromTangentSpace (0 : ℂ)) hcon
      rw [hfrom0, map_zero] at h1
      exact one_ne_zero h1
    by_cases htop : a = ⊤
    · have huniv : Metric.eball (0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) a =
          Set.univ := by
        rw [htop, Metric.eball_top]
      have h1mem : v0 ∈ Metric.eball 0 a := by
        simp [huniv]
      have heq : constExp (0 : ℂ) (0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) =
          constExp (0 : ℂ) v0 := rfl
      have hsame := ha.1 h0mem h1mem heq
      exact hv0ne hsame.symm
    · have hto : 0 < a.toReal := ENNReal.toReal_pos hne htop
      let r := a.toReal / 2 / ‖v0‖
      have hvnorm : 0 < ‖v0‖ := norm_pos_iff.mpr hv0ne
      have hrpos : 0 < r := div_pos (half_pos hto) hvnorm
      let y := r • v0
      have hyne : y ≠ 0 := smul_ne_zero (ne_of_gt hrpos) hv0ne
      have hnormy : ‖y‖ = a.toReal / 2 := by
        simp only [y, r, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
        exact div_mul_cancel₀ _ (ne_of_gt hvnorm)
      have hedist : edist y (0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) =
          ENNReal.ofReal (a.toReal / 2) := by
        rw [edist_dist, dist_eq_norm, sub_zero, hnormy]
      have hhalf : a.toReal / 2 < a.toReal := half_lt_self hto
      have hstrict : ENNReal.ofReal (a.toReal / 2) <
          ENNReal.ofReal a.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff').mpr ⟨hhalf, hto⟩
      have hlt2 : ENNReal.ofReal (a.toReal / 2) < a := by
        rwa [ENNReal.ofReal_toReal htop] at hstrict
      have hymem : y ∈ Metric.eball (0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) a := by
        rw [Metric.mem_eball, hedist]
        exact hlt2
      have heq : constExp (0 : ℂ) (0 : TangentSpace 𝓘(ℝ, ℂ) (0 : ℂ)) =
          constExp (0 : ℂ) y := rfl
      have hsame := ha.1 h0mem hymem heq
      exact hyne hsame.symm
  exact le_antisymm hle (le_sSup hmem)

end

end ExpMapNegTests
