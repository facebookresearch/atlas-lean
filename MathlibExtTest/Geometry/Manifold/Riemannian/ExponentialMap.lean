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
# Tests for the Euclidean exponential map

Existence, uniqueness, pins, injectivity radius and domain.
-/

open Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal

noncomputable section

namespace ExpTests

variable {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The Euclidean exponential map: translation by the fiber vector read in `F`. -/
def euclideanExp (x : F)
    (v : TangentSpace 𝓘(ℝ, F) x) : F :=
  x + (NormedSpace.fromTangentSpace x) v

/-- The Euclidean map satisfies `IsRiemannianExp` on `F`. -/
theorem euclideanExp_isExp :
    Manifold.IsRiemannianExp 𝓘(ℝ, F)
      (fun x v => euclideanExp x v) := by
  intro x v
  set w : F := (NormedSpace.fromTangentSpace x) v with hw
  refine ⟨fun t => (⟨x + t • w,
    (NormedSpace.fromTangentSpace (x + t • w)).symm w⟩ :
    TangentBundle 𝓘(ℝ, F) F), ?_, ?_, ?_⟩
  · rw [Manifold.isGeodesicVelocityCurve_vectorSpace_iff]
    intro t
    refine ⟨by simp [ContinuousLinearEquiv.apply_symm_apply],
      by simp [ContinuousLinearEquiv.apply_symm_apply]⟩
  · have hbase : x + (0 : ℝ) • w = x := by simp
    have hsymm :
        (NormedSpace.fromTangentSpace x).symm w = v := by
      simp [hw]
    show (⟨x + (0 : ℝ) • w,
      (NormedSpace.fromTangentSpace (x + (0 : ℝ) • w)).symm w⟩ :
      TangentBundle 𝓘(ℝ, F) F) = ⟨x, v⟩
    rw [hbase]
    rw [hsymm]
  · intro t
    show euclideanExp x (t • v) = x + t • w
    simp [euclideanExp, map_smul, hw]

/-- The Euclidean map satisfies `IsRiemannianExp` on `ℝ`. -/
theorem euclideanExp_isExp_real :
    Manifold.IsRiemannianExp 𝓘(ℝ, ℝ)
      (fun x v => euclideanExp x v) :=
  euclideanExp_isExp

/-- The Euclidean map satisfies `IsRiemannianExp` on `ℂ`. -/
theorem euclideanExp_isExp_complex :
    Manifold.IsRiemannianExp 𝓘(ℝ, ℂ)
      (fun x v => euclideanExp x v) :=
  euclideanExp_isExp

/-- Any Riemannian exponential on `F` agrees with the Euclidean map. -/
theorem exp_unique
    (exp : (x : F) → TangentSpace 𝓘(ℝ, F) x → F)
    (h : Manifold.IsRiemannianExp 𝓘(ℝ, F) exp) (x : F)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    exp x v = euclideanExp x v := by
  obtain ⟨u, hgeo, hu0, hray⟩ := h x v
  have hchar :=
    (Manifold.isGeodesicVelocityCurve_vectorSpace_iff u).mp hgeo
  have h1 := hchar 1
  rw [hu0] at h1
  have hray1 : exp x v = (u 1).proj := by
    have h := hray 1
    simpa using h
  rw [hray1, h1.1]
  simp [euclideanExp, one_smul]

/-- Pin: every exponential on `ℂ` sends `0` at `1` to `1`. -/
theorem exp_pin_zero
    (exp : (x : ℂ) → TangentSpace 𝓘(ℝ, ℂ) x → ℂ)
    (h : Manifold.IsRiemannianExp 𝓘(ℝ, ℂ) exp) :
    exp 1 0 = 1 := by
  have h := exp_unique exp h 1 0
  simpa [euclideanExp] using h

/-- Pin: every exponential on `ℂ` sends `-2 • I` at `1` to `1 - 2 * I`. -/
theorem exp_pin_neg
    (exp : (x : ℂ) → TangentSpace 𝓘(ℝ, ℂ) x → ℂ)
    (h : Manifold.IsRiemannianExp 𝓘(ℝ, ℂ) exp) :
    exp 1 ((-2 : ℝ) •
      (NormedSpace.fromTangentSpace (1 : ℂ)).symm Complex.I) =
      1 - 2 * Complex.I := by
  have h1 := exp_unique exp h 1 ((-2 : ℝ) •
    (NormedSpace.fromTangentSpace (1 : ℂ)).symm Complex.I)
  rw [h1]
  simp only [euclideanExp, map_smul,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [Complex.ext_iff]
  refine ⟨by simp, by simp⟩

/-- Pin: every exponential on `ℝ` sends `-1` at `3` to `2`. -/
theorem exp_pin_real
    (exp : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x → ℝ)
    (h : Manifold.IsRiemannianExp 𝓘(ℝ, ℝ) exp) :
    exp 3 ((-1 : ℝ) •
      (NormedSpace.fromTangentSpace (3 : ℝ)).symm 1) = 2 := by
  have h1 := exp_unique exp h 3 ((-1 : ℝ) •
    (NormedSpace.fromTangentSpace (3 : ℝ)).symm 1)
  rw [h1]
  simp only [euclideanExp, map_smul,
    ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul]
  norm_num

omit [FiniteDimensional ℝ F] in
/-- The injectivity radius of the Euclidean map at `x` is `⊤`. -/
theorem injectivityRadiusAt_eq_top (x : F) :
    Manifold.injectivityRadiusAt 𝓘(ℝ, F)
      (fun x v => euclideanExp x v) x = ⊤ := by
  have hle : (⊤ : ℝ≥0∞) ≤
      Manifold.injectivityRadiusAt 𝓘(ℝ, F)
        (fun x v => euclideanExp x v) x := by
    unfold Manifold.injectivityRadiusAt
    apply le_sSup
    constructor
    · rw [Metric.eball_top]
      show Set.InjOn (euclideanExp x) Set.univ
      intro u _ v _ h
      simp only [euclideanExp] at h
      have h2 := add_left_cancel_iff.mp h
      exact (NormedSpace.fromTangentSpace x).injective h2
    · rw [Metric.eball_top]
      show IsLocalDiffeomorphOn
        𝓘(ℝ, TangentSpace 𝓘(ℝ, F) x) 𝓘(ℝ, F) ∞
        (euclideanExp x) Set.univ
      have hcont1 : ContDiff ℝ ∞ (fun y : F => x + y) := by
        fun_prop
      have hcont2 : ContDiff ℝ ∞ (fun y : F => -x + y) := by
        fun_prop
      let e1 : TangentSpace 𝓘(ℝ, F) x ≃ₘ[ℝ] F :=
        ContinuousLinearEquiv.toDiffeomorph
          (NormedSpace.fromTangentSpace x)
      let e2 : F ≃ₘ[ℝ] F :=
        { toFun := fun y => x + y,
          invFun := fun y => -x + y,
          left_inv := fun y => by module,
          right_inv := fun y => by module,
          contMDiff_toFun :=
            (contMDiff_iff_contDiff).mpr hcont1,
          contMDiff_invFun :=
            (contMDiff_iff_contDiff).mpr hcont2 }
      let Φ : TangentSpace 𝓘(ℝ, F) x ≃ₘ[ℝ] F :=
        e1.trans e2
      have heq : (euclideanExp x) = ⇑Φ := rfl
      have hloc : IsLocalDiffeomorph
          𝓘(ℝ, TangentSpace 𝓘(ℝ, F) x) 𝓘(ℝ, F) ∞ ⇑Φ :=
        Diffeomorph.isLocalDiffeomorph Φ
      have hon : IsLocalDiffeomorphOn
          𝓘(ℝ, TangentSpace 𝓘(ℝ, F) x) 𝓘(ℝ, F) ∞ ⇑Φ
          Set.univ :=
        hloc.isLocalDiffeomorphOn Set.univ
      rw [heq]
      exact hon
  exact top_le_iff.mp hle

omit [FiniteDimensional ℝ F] in
/-- The global injectivity radius of the Euclidean map is `⊤`. -/
theorem injectivityRadius_eq_top :
    Manifold.injectivityRadius 𝓘(ℝ, F)
      (fun x v => euclideanExp x v) = ⊤ := by
  unfold Manifold.injectivityRadius
  rw [iInf_eq_top]
  intro x
  exact injectivityRadiusAt_eq_top x

/-- The injectivity radius at `x` is `⊤` on `ℂ`. -/
theorem injectivityRadiusAt_eq_top_complex (x : ℂ) :
    Manifold.injectivityRadiusAt 𝓘(ℝ, ℂ)
      (fun x v => euclideanExp x v) x = ⊤ :=
  injectivityRadiusAt_eq_top x

/-- The global injectivity radius is `⊤` on `ℂ`. -/
theorem injectivityRadius_eq_top_complex :
    Manifold.injectivityRadius 𝓘(ℝ, ℂ)
      (fun x v => euclideanExp x v) = ⊤ :=
  injectivityRadius_eq_top

omit [FiniteDimensional ℝ F] in
/-- The injectivity domain of the Euclidean map at `x` is `univ`. -/
theorem injectivityDomain_univ (x : F) :
    Manifold.injectivityDomain 𝓘(ℝ, F)
      (fun x v => euclideanExp x v) x = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  refine ⟨2, one_lt_two, ?_⟩
  have hexp : (fun x v => euclideanExp x v) x ((2 : ℝ) • v) =
      x + (2 : ℝ) • (NormedSpace.fromTangentSpace x) v := by
    simp [euclideanExp, map_smul]
  rw [hexp, ← IsRiemannianManifold.out x _,
    edist_dist, dist_eq_norm]
  have hsub : x - (x + (2 : ℝ) •
      (NormedSpace.fromTangentSpace x) v) =
      -((2 : ℝ) • (NormedSpace.fromTangentSpace x) v) := by
    abel
  rw [hsub, norm_neg, norm_tangentSpace_vectorSpace, map_smul]

/-- The injectivity domain at `x` is `univ` on `ℂ`. -/
theorem injectivityDomain_univ_complex (x : ℂ) :
    Manifold.injectivityDomain 𝓘(ℝ, ℂ)
      (fun x v => euclideanExp x v) x = Set.univ :=
  injectivityDomain_univ x

end ExpTests
