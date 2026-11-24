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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CharacterMultiplierContinuous
public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CompletionAdjoint
public import MathlibExt.MeasureTheory.Function.L2Space.RightTensorProduct

/-!
# Actual right-factor character unitaries on the original H-first tensor

The operator is the literal completed tensor of id_H and the original
scalar Haar character multiplier. Its pure a.e. values and completion
density give its actual L2 coordinates. Strong continuity is transferred
through the proved coordinates on the same stock tensor topology.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped ENNReal TensorProduct Topology InnerProductSpace CStarAlgebra

namespace MeasureTheory.HaarL2

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : Measure G) [μ.Regular]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [μ.Regular] in
/-- The actual right-factor scalar character operator has its original vector-valued L2 coordinates. -/
theorem characterMultiplierTensor_coordinates (χ : PontryaginDual G)
    (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :
    L2.tensorToLpRight μ
        (TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
          (characterMultiplierUnitary (H := ℂ) μ χ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z) =
      characterMultiplier (H := H) μ χ (L2.tensorToLpRight μ z) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq
      (E.continuous.comp (TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
        (characterMultiplierUnitary (H := ℂ) μ χ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)).continuous)
      ((characterMultiplier (H := H) μ χ).continuous.comp E.continuous)) ?_
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x f =>
    rw [TensorProduct.mapLCompletion_tmul]
    change E ((x ⊗ₜ[ℂ] characterMultiplier (H := ℂ) μ χ f : H ⊗[ℂ] (Lp ℂ 2 μ)) :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
      characterMultiplier (H := H) μ χ (E ((x ⊗ₜ[ℂ] f : H ⊗[ℂ] (Lp ℂ 2 μ)) :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))))
    apply Lp.ext
    filter_upwards [L2.tensorToLpRight_tmul_ae (𝕜 := ℂ) μ x (characterMultiplier (H := ℂ) μ χ f),
      characterMultiplier_ae_eq (H := ℂ) μ χ f,
      characterMultiplier_ae_eq (H := H) μ χ (E ((x ⊗ₜ[ℂ] f : H ⊗[ℂ] (Lp ℂ 2 μ)) :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))),
      L2.tensorToLpRight_tmul_ae (𝕜 := ℂ) μ x f] with s hleft hscalar hright hinput
    rw [hleft, hscalar, hright, hinput]
    change ((((χ s : Circle) : ℂ) * f s) • x) = ((χ s : Circle) : ℂ) • (f s • x)
    exact mul_smul _ _ _
  | add z w hz hw =>
    simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (fun x y => x + y) hz hw

/-- The actual strongly continuous character representation is id_H tensored with the scalar character unitary. -/
def characterMultiplierTensorRepresentation :
    StronglyContinuousUnitaryRepresentation (PontryaginDual G)
      (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) := by
  have hOne : (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H := ContinuousLinearMap.one_def
  let F : (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) →⋆*
      (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :=
    { toFun := TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
      map_one' := TensorProduct.mapLCompletion_id_id ℂ H (Lp ℂ 2 μ)
      map_mul' := fun A B => by
        rw [← hOne]
        simpa only [one_mul] using TensorProduct.mapLCompletion_mul (1 : H →L[ℂ] H) 1 A B
      map_star' := fun A => by
        rw [← hOne]
        simpa only [star_one] using (TensorProduct.star_mapLCompletion (1 : H →L[ℂ] H) A).symm }
  refine
    { toMonoidHom := (Unitary.map F).toMonoidHom.comp (characterMultiplierRepresentation (H := ℂ) μ).toMonoidHom
      continuous_orbit := ?_ }
  intro z
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  change Continuous fun χ : PontryaginDual G => TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
    (characterMultiplierUnitary (H := ℂ) μ χ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z
  have htransport (χ : PontryaginDual G) :
      TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
          (characterMultiplierUnitary (H := ℂ) μ χ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z =
        E.symm (characterMultiplier (H := H) μ χ (E z)) := by
    apply E.injective
    rw [E.apply_symm_apply]
    exact characterMultiplierTensor_coordinates μ χ z
  let m : PseudoMetricSpace (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :=
    (inferInstance : SeminormedAddCommGroup
      (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))).toPseudoMetricSpace
  have hUniform : m.toUniformSpace = UniformSpace.Completion.uniformSpace (H ⊗[ℂ] (Lp ℂ 2 μ)) := by
    apply UniformSpace.ext
    exact (@PseudoMetricSpace.uniformity_dist _ m).trans
      (UniformSpace.Completion.uniformity_dist (α := H ⊗[ℂ] (Lp ℂ 2 μ))).symm
  have htop : m.toUniformSpace.toTopologicalSpace =
      (UniformSpace.Completion.uniformSpace (H ⊗[ℂ] (Lp ℂ 2 μ))).toTopologicalSpace :=
    congrArg (fun w : UniformSpace (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =>
      @UniformSpace.toTopologicalSpace (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) w) hUniform
  have hc := E.symm.continuous.comp ((characterMultiplierRepresentation (H := H) μ).continuous_orbit (E z))
  change @Continuous (PontryaginDual G) (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) _
    m.toUniformSpace.toTopologicalSpace
      (fun χ => E.symm (characterMultiplier (H := H) μ χ (E z))) at hc
  rw [htop] at hc
  simpa only [htransport] using hc

/-- Every original tensor character unitary keeps its literal right-factor operator value. -/
@[simp]
theorem characterMultiplierTensorRepresentation_apply (χ : PontryaginDual G) :
    (characterMultiplierTensorRepresentation (H := H) μ χ :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
      TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
        (characterMultiplierUnitary (H := ℂ) μ χ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  rfl

/-- The literal tensor character unitary is the original vector character unitary in actual L2 coordinates. -/
theorem characterMultiplierTensor_conjStarAlgEquiv (χ : PontryaginDual G) :
    (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ).conjStarAlgEquiv
        (characterMultiplierTensorRepresentation (H := H) μ χ :
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
      (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  apply ContinuousLinearMap.ext
  intro ξ
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, characterMultiplierTensorRepresentation_apply]
  exact (characterMultiplierTensor_coordinates μ χ (E.symm ξ)).trans
    (congrArg (characterMultiplier (H := H) μ χ) (E.apply_symm_apply ξ))

end

end MeasureTheory.HaarL2
