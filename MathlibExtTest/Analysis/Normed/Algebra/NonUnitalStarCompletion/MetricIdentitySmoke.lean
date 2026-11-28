/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Normed.Algebra.NonUnitalStarCompletion.Metric
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Star.Real

/-! # Identity completion extensions with the public ring, star and action choices -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open UniformSpace.Completion

namespace MathlibExtTest.NonUnitalStarCompletion.MetricIdentitySmoke

universe uR uA

-- No unit or nontriviality is assumed. Completeness and T₀ belong to the identity target.
example {R : Type uR} {A : Type uA} [Monoid R] [NonUnitalSeminormedRing A]
    [StarRing A] [ContinuousStar A] [DistribMulAction R A]
    [UniformContinuousConstSMul R A] [CompleteSpace A] [T0Space A]
    (x : UniformSpace.Completion A) :
    let C := UniformSpace.Completion A
    let rC : NonUnitalNormedRing C := nonUnitalCompletionNormedRing A
    letI : NonUnitalNormedRing C := rC
    let rS : StarRing C := nonUnitalCompletionStarRing A
    letI : StarRing C := rS
    let mC : DistribMulAction R C := inferInstance
    letI : DistribMulAction R C := mC
    let φ : A →⋆ₙₐ[R] A := NonUnitalStarAlgHom.id R A
    let hφ : Continuous φ := continuous_id
    let Γ : C →⋆ₙₐ[R] A := NonUnitalStarAlgHom.fromCompletion φ hφ
    dist (Γ x) (Γ (0 : C)) = dist x (0 : C) ∧ (Γ x = 0 ↔ x = 0) := by
  let C := UniformSpace.Completion A
  let rC : NonUnitalNormedRing C := nonUnitalCompletionNormedRing A
  let : NonUnitalNormedRing C := rC
  let rS : StarRing C := nonUnitalCompletionStarRing A
  let : StarRing C := rS
  let mC : DistribMulAction R C := inferInstance
  let : DistribMulAction R C := mC
  let φ : A →⋆ₙₐ[R] A := NonUnitalStarAlgHom.id R A
  let hφ : Continuous φ := continuous_id
  let Γ : C →⋆ₙₐ[R] A := NonUnitalStarAlgHom.fromCompletion φ hφ
  change dist (Γ x) (Γ (0 : C)) = dist x (0 : C) ∧ (Γ x = 0 ↔ x = 0)
  have hProperties :
      (∀ z : C, ‖Γ z‖ = ‖z‖) ∧ Isometry Γ ∧ Function.Injective Γ :=
    NonUnitalStarAlgHom.fromCompletion_norm_isometry
      (fun a b : A => NonUnitalSeminormedRing.dist_eq a b) φ hφ (fun _ => rfl)
  constructor
  · exact hProperties.2.1.dist_eq x (0 : C)
  · constructor
    · intro hx
      apply hProperties.2.2
      simpa only [map_zero] using hx
    · intro hx
      simpa only [hx] using (map_zero Γ)

-- The isometry from the bundled theorem computes a distance on genuine completion points.
example :
    let C := UniformSpace.Completion ℝ
    let rC : NonUnitalNormedRing C := nonUnitalCompletionNormedRing ℝ
    letI : NonUnitalNormedRing C := rC
    let rS : StarRing C := nonUnitalCompletionStarRing ℝ
    letI : StarRing C := rS
    let mC : DistribMulAction ℝ C := inferInstance
    letI : DistribMulAction ℝ C := mC
    let φ : ℝ →⋆ₙₐ[ℝ] ℝ := NonUnitalStarAlgHom.id ℝ ℝ
    let hφ : Continuous φ := continuous_id
    let Γ : C →⋆ₙₐ[ℝ] ℝ := NonUnitalStarAlgHom.fromCompletion φ hφ
    let x : C := ((2 : ℝ) : C)
    let y : C := ((-3 : ℝ) : C)
    Γ x = 2 ∧ ‖x‖ = 2 ∧ dist x y = 5 ∧ dist (0 : C) x = 2 := by
  let C := UniformSpace.Completion ℝ
  let rC : NonUnitalNormedRing C := nonUnitalCompletionNormedRing ℝ
  let : NonUnitalNormedRing C := rC
  let rS : StarRing C := nonUnitalCompletionStarRing ℝ
  let : StarRing C := rS
  let mC : DistribMulAction ℝ C := inferInstance
  let : DistribMulAction ℝ C := mC
  let φ : ℝ →⋆ₙₐ[ℝ] ℝ := NonUnitalStarAlgHom.id ℝ ℝ
  let hφ : Continuous φ := continuous_id
  let Γ : C →⋆ₙₐ[ℝ] ℝ := NonUnitalStarAlgHom.fromCompletion φ hφ
  let x : C := ((2 : ℝ) : C)
  let y : C := ((-3 : ℝ) : C)
  change Γ x = 2 ∧ ‖x‖ = 2 ∧ dist x y = 5 ∧ dist (0 : C) x = 2
  have hProperties :
      (∀ z : C, ‖Γ z‖ = ‖z‖) ∧ Isometry Γ ∧ Function.Injective Γ :=
    NonUnitalStarAlgHom.fromCompletion_norm_isometry
      (fun a b : ℝ => NonUnitalSeminormedRing.dist_eq a b) φ hφ (fun _ => rfl)
  have hx : Γ x = 2 := NonUnitalStarAlgHom.fromCompletion_apply_coe φ hφ (2 : ℝ)
  have hy : Γ y = -3 := NonUnitalStarAlgHom.fromCompletion_apply_coe φ hφ (-3 : ℝ)
  refine ⟨hx, ?_, ?_, ?_⟩
  · rw [← hProperties.1 x, hx]
    norm_num [Real.norm_eq_abs]
  · rw [← hProperties.2.1.dist_eq x y, hx, hy]
    norm_num [Real.dist_eq]
  · rw [← hProperties.2.1.dist_eq (0 : C) x, map_zero, hx]
    norm_num [Real.dist_eq]

end MathlibExtTest.NonUnitalStarCompletion.MetricIdentitySmoke
