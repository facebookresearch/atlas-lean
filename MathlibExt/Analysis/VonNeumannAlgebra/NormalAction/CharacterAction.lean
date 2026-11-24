/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CharacterConjugation
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The actual normal character action on the generated Haar Lp algebra

Inverse spatial pullback sends the original vector functional on ξ and η to
the one on the actual positive-character vectors κχξ and κχη. Their genuine
strong continuity gives norm-continuous vector-functional orbits. All ordinary
dual pullbacks are contractions, so the set of continuous orbits is norm closed.
The actual closed vector-functional span therefore has continuous predual
orbits and supplies the continuity field of the original NormalAction bundle.

This constructs the action on the same actual C_c/Lp generated algebra. The
original Connes tensor transport and source coefficient inclusion keep their
separate construction boundaries.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.HaarL2
open scoped InnerProductSpace CStarAlgebra UniformConvergence

namespace VonNeumannAlgebra
namespace NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Actual inverse predual pullback is the original functional on the positive-character vectors. -/
theorem characterConjugation_predual_vectorFunctional (α : NormalAction G M) (χ : PontryaginDual G)
    (ξ η : Lp H 2 μ) :
    (NormalStarAlgEquiv.predualActionHom (crossedProductLp μ α) (characterConjugationNormalHom μ α χ)
      ⟨vectorFunctional (crossedProductLp μ α) ξ η,
        vectorFunctional_mem_normalFunctionalSpace (crossedProductLp μ α) ξ η⟩ :
        StrongDual ℂ (crossedProductLp μ α)) =
      vectorFunctional (crossedProductLp μ α)
        (characterMultiplier (H := H) μ χ ξ) (characterMultiplier (H := H) μ χ η) := by
  let U := characterMultiplierUnitary (H := H) μ χ
  apply ContinuousLinearMap.ext
  intro x
  rw [NormalStarAlgEquiv.predualActionHom_apply]
  simp only [vectorFunctional_apply]
  change ⟪ξ, (star U : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    ((x : Lp H 2 μ →L[ℂ] Lp H 2 μ) ((U : Lp H 2 μ →L[ℂ] Lp H 2 μ) η))⟫_ℂ =
      ⟪(U : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ,
        (x : Lp H 2 μ →L[ℂ] Lp H 2 μ) ((U : Lp H 2 μ →L[ℂ] Lp H 2 μ) η)⟫_ℂ
  calc
    _ = ⟪(star (star U) : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ,
        (x : Lp H 2 μ →L[ℂ] Lp H 2 μ) ((U : Lp H 2 μ →L[ℂ] Lp H 2 μ) η)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left (star U : Lp H 2 μ →L[ℂ] Lp H 2 μ)
        ((x : Lp H 2 μ →L[ℂ] Lp H 2 μ) ((U : Lp H 2 μ →L[ℂ] Lp H 2 μ) η)) ξ).symm
    _ = _ := by rw [star_star]

/-- Every original predual orbit is norm continuous for the actual compact-open character topology. -/
theorem characterConjugation_predual_continuous (α : NormalAction G M)
    (φ : normalFunctionalSpace (crossedProductLp μ α)) :
    Continuous fun χ : PontryaginDual G =>
      NormalStarAlgEquiv.predualActionHom (crossedProductLp μ α) (characterConjugationNormalHom μ α χ) φ := by
  let X := crossedProductLp μ α
  let A : PontryaginDual G → (StrongDual ℂ X →L[ℂ] StrongDual ℂ X) := fun χ =>
    (ContinuousLinearMap.compL ℂ X X ℂ).flip
      (characterConjugationNormalHom μ α χ).symm.toNormalStarAlgHom.toContinuousLinearMap
  have hbound (χ : PontryaginDual G) (ψ : StrongDual ℂ X) : ‖A χ ψ‖ ≤ ‖ψ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ψ)
    intro x
    change ‖ψ ((characterConjugationNormalHom μ α χ).symm x)‖ ≤ ‖ψ‖ * ‖x‖
    calc
      _ ≤ ‖ψ‖ * ‖(characterConjugationNormalHom μ α χ).symm x‖ := ψ.le_opNorm _
      _ ≤ ‖ψ‖ * ‖x‖ := mul_le_mul_of_nonneg_left
        (NonUnitalStarAlgHom.norm_apply_le
          (characterConjugationNormalHom μ α χ).symm.toNormalStarAlgHom.toStarAlgHom x)
        (norm_nonneg ψ)
  have hLip (χ : PontryaginDual G) : LipschitzWith 1 (A χ) := by
    apply LipschitzWith.mk_one
    intro ψ θ
    simp only [dist_eq_norm]
    rw [← map_sub]
    exact hbound χ (ψ - θ)
  let P : Submodule ℂ (StrongDual ℂ X) :=
    { carrier := {ψ | Continuous fun χ : PontryaginDual G => A χ ψ}
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact continuous_const
      add_mem' := by
        intro ψ θ hψ hθ
        have hcψ : Continuous fun χ : PontryaginDual G => A χ ψ := hψ
        have hcθ : Continuous fun χ : PontryaginDual G => A χ θ := hθ
        simp only [Set.mem_ofPred_eq]
        have hfun : (fun χ : PontryaginDual G => A χ (ψ + θ)) =
            (fun χ : PontryaginDual G => A χ ψ) + (fun χ : PontryaginDual G => A χ θ) := by
          funext χ
          rw [Pi.add_apply]
          exact map_add (A χ) ψ θ
        rw [hfun]
        exact hcψ.add hcθ
      smul_mem' := by
        intro c ψ hψ
        have hcψ : Continuous fun χ : PontryaginDual G => A χ ψ := hψ
        simp only [Set.mem_ofPred_eq]
        have hfun : (fun χ : PontryaginDual G => A χ (c • ψ)) =
            (fun _ : PontryaginDual G => c) • (fun χ : PontryaginDual G => A χ ψ) := by
          funext χ
          rw [Pi.smul_apply']
          exact map_smul (A χ) c ψ
        rw [hfun]
        exact (continuous_const : Continuous fun _ : PontryaginDual G => c).smul hcψ }
  have hOrbitLip : LipschitzWith 1
      (fun ψ : StrongDual ℂ X => UniformFun.ofFun (fun χ : PontryaginDual G => A χ ψ)) :=
    UniformFun.lipschitzWith_ofFun_iff.mpr hLip
  have hPclosed : IsClosed (P : Set (StrongDual ℂ X)) := by
    change IsClosed ((fun ψ : StrongDual ℂ X => UniformFun.ofFun (fun χ : PontryaginDual G => A χ ψ)) ⁻¹'
      {f : PontryaginDual G →ᵤ StrongDual ℂ X | Continuous (UniformFun.toFun f)})
    exact (UniformFun.isClosed_setOfPred_continuous (α := PontryaginDual G) (β := StrongDual ℂ X)).preimage
      hOrbitLip.continuous
  let R₀ : X →ₗ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
    LinearMap.ofClass X.toStarSubalgebra.subtype
  let R : X →L[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) := R₀.mkContinuous 1 (by
    intro x
    change ‖(x : Lp H 2 μ →L[ℂ] Lp H 2 μ)‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact le_rfl)
  let E : Lp H 2 μ →L[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) →L[ℂ] Lp H 2 μ :=
    ContinuousLinearMap.apply ℂ (Lp H 2 μ)
  let J : Lp H 2 μ →L[ℂ] X →L[ℂ] Lp H 2 μ := (E.flip.comp R).flip
  let B : Lp H 2 μ →L⋆[ℂ] Lp H 2 μ →L[ℂ] StrongDual ℂ X :=
    ContinuousLinearMap.bilinearComp (ContinuousLinearMap.compL ℂ X (Lp H 2 μ) ℂ) (innerSL ℂ) J
  have hR (x : X) : R x = (x : Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
    dsimp only [R]
    rw [LinearMap.mkContinuous_apply]
    rfl
  have hE (ξ : Lp H 2 μ) (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) : E ξ T = T ξ := by
    dsimp only [E]
    exact ContinuousLinearMap.apply_apply ξ T
  have hJ (ξ : Lp H 2 μ) (x : X) : J ξ x = (R x) ξ := by
    dsimp only [J]
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    exact hE ξ (R x)
  have hEval (ξ η : Lp H 2 μ) (x : X) :
      B ξ η x = ⟪ξ, (x : Lp H 2 μ →L[ℂ] Lp H 2 μ) η⟫_ℂ := by
    calc
      B ξ η x = innerSL ℂ ξ (J η x) := by
        simp only [B, ContinuousLinearMap.bilinearComp_apply,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
      _ = ⟪ξ, (R x) η⟫_ℂ := by rw [hJ, innerSL_apply_apply]
      _ = ⟪ξ, (x : Lp H 2 μ →L[ℂ] Lp H 2 μ) η⟫_ℂ := by rw [hR]
  have hB (ξ η : Lp H 2 μ) : B ξ η = vectorFunctional X ξ η := by
    apply ContinuousLinearMap.ext
    intro x
    exact (hEval ξ η x).trans (vectorFunctional_apply X ξ η x).symm
  have hvec (ξ η : Lp H 2 μ) : vectorFunctional X ξ η ∈ P := by
    change Continuous fun χ : PontryaginDual G => A χ (vectorFunctional X ξ η)
    have he (χ : PontryaginDual G) :
        A χ (vectorFunctional X ξ η) = B (characterMultiplier μ χ ξ) (characterMultiplier μ χ η) := by
      have h := characterConjugation_predual_vectorFunctional μ α χ ξ η
      change A χ (vectorFunctional X ξ η) =
        vectorFunctional X (characterMultiplier μ χ ξ) (characterMultiplier μ χ η) at h
      exact h.trans (hB (characterMultiplier μ χ ξ) (characterMultiplier μ χ η)).symm
    have hfun : (fun χ : PontryaginDual G => A χ (vectorFunctional X ξ η)) =
        (fun χ : PontryaginDual G => B (characterMultiplier μ χ ξ) (characterMultiplier μ χ η)) := by
      funext χ
      exact he χ
    rw [hfun]
    exact (B.continuous.comp (characterMultiplier_continuous μ ξ)).clm_apply
      (characterMultiplier_continuous μ η)
  have hAll := normalFunctionalSpace_le X hPclosed hvec
  apply continuous_induced_rng.2
  change Continuous fun χ : PontryaginDual G => A χ (φ : StrongDual ℂ X)
  exact hAll φ.property

/-- The computed positive-character normal action with its actual continuous predual inverse orbits. -/
def characterConjugationNormalAction (α : NormalAction G M) :
    NormalAction (PontryaginDual G) (crossedProductLp μ α) where
  toMonoidHom := characterConjugationNormalHom μ α
  continuous_predual_orbit := characterConjugation_predual_continuous μ α

end

end NormalAction
end VonNeumannAlgebra
