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
# Character unitaries in the scalar tensor factor

On `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)`, let `W_χ=I_H⊗U_χ`. The tensor-to-L² unitary sends this
operator to the vector-valued character multiplier on `Lp H 2 μ`.

For a locally compact Borel topological group and regular measure, the family is strongly
continuous for compact-open character topology. The coordinate equality itself holds without
local compactness, group-operation continuity or regularity of `μ`.
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
/-- **Character multiplier compatibility with Hilbert-first L² coordinates.** Let `G` be a
group with Borel topology, `μ` any measure and `H` a complete complex Hilbert space. For
`T=Completion(H⊗Lp ℂ 2 μ)` and `U=tensorToLpRight μ`, `U((I_H⊗U_χ)z)=U_χ^H(Uz)` for every
`z∈T`, where both character multipliers have pointwise factor `χ(s)`. -/
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

/-- **Strongly continuous tensor-factor character representation.** Let `G` be a locally
compact topological group with its Borel structure, `μ` a regular measure and `H` a
complete complex Hilbert space. Let `U_χξ(s)=χ(s) • ξ(s)` on `Lp H 2 μ`, with compact-open
topology on the character group. on `T=Completion(H⊗Lp ℂ 2 μ)`,
`characterMultiplierTensorRepresentation μ χ=I_H⊗U_χ` is a strongly continuous unitary
representation. -/
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

/-- **Operator value of the tensor character unitary.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular measure and `H` a complete
complex Hilbert space. Let `U_χξ(s)=χ(s) • ξ(s)` on `Lp H 2 μ`, with compact-open topology
on the character group. for `T=Completion(H⊗Lp ℂ 2 μ)`, the representation at `χ` is
`TensorProduct.mapLCompletion I_H (characterMultiplierUnitary μ χ)=I_H⊗U_χ`. -/
@[simp]
theorem characterMultiplierTensorRepresentation_apply (χ : PontryaginDual G) :
    (characterMultiplierTensorRepresentation (H := H) μ χ :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
      TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
        (characterMultiplierUnitary (H := ℂ) μ χ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  rfl

/-- **Tensor-to-L² conjugation of a character unitary.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular measure and `H` a complete
complex Hilbert space. Let `U_χξ(s)=χ(s) • ξ(s)` on `Lp H 2 μ`, with compact-open topology
on the character group. for `U=tensorToLpRight μ`, conjugation sends the tensor
representation at `χ` to `characterMultiplierUnitary μ χ` on `Lp H 2 μ`. -/
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
