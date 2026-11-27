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

public import MathlibExt.MeasureTheory.Function.L2Space.RightTensorProduct
public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CompletionAdjoint
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRegularRepresentation

/-!
# Haar left representation in a Hilbert-first completed tensor

For a regular Haar measure and complete complex Hilbert space `H`, the representation on
`T=Completion(H⊗Lp ℂ 2 μ)` has operator `V_g=I_H⊗λ_g^ℂ`.

Its unitary group laws are tensor products of the scalar Haar laws, and strong continuity is
transported through the tensor-to-L² unitary. The group is locally compact with Borel structure
and may be nonabelian.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped TensorProduct ENNReal Topology InnerProductSpace

namespace StronglyContinuousUnitaryRepresentation

noncomputable section

universe uG uH

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Strongly continuous tensor Haar left representation.** Let `G` be a locally compact
Borel topological group with regular Haar measure `μ` and `H` a complete complex Hilbert
space. Let `λ_g^H ξ(s)=ξ(g⁻¹s)` on `Lp H 2 μ` and `T=Completion(H⊗Lp ℂ 2 μ)`, with
`U=tensorToLpRight μ : T ≃ₗᵢ[ℂ] Lp H 2 μ`. `haarLeftRegularTensor G μ H : G → U(B(T))` has
operator value `V_g=I_H⊗λ_g^ℂ`. -/
def haarLeftRegularTensor :
    StronglyContinuousUnitaryRepresentation G (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  have hintertwine (g : G) (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :
      E (TensorProduct.mapLCompletion (1 : H →L[ℂ] H)
        (haarLeftRegular G μ ℂ g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z) =
      (haarLeftRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ) (E z) := by
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq
        (E.continuous.comp (TensorProduct.mapLCompletion (1 : H →L[ℂ] H)
          (haarLeftRegular G μ ℂ g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)).continuous)
        ((haarLeftRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ).continuous.comp E.continuous)) ?_
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x f =>
      rw [TensorProduct.mapLCompletion_tmul]
      change E ((x ⊗ₜ[ℂ] ((haarLeftRegular G μ ℂ g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) f) :
          H ⊗[ℂ] (Lp ℂ 2 μ)) : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
        (haarLeftRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ)
          (E ((x ⊗ₜ[ℂ] f : H ⊗[ℂ] (Lp ℂ 2 μ)) :
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))))
      apply Lp.ext
      have hinput := L2.tensorToLpRight_tmul_ae (𝕜 := ℂ) μ x f
      have houtput := L2.tensorToLpRight_tmul_ae (𝕜 := ℂ) μ x
        ((haarLeftRegular G μ ℂ g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) f)
      have hscalar := haarLeftRegular_ae_eq G μ ℂ g f
      have hvector := haarLeftRegular_ae_eq G μ H g
        (E ((x ⊗ₜ[ℂ] f : H ⊗[ℂ] (Lp ℂ 2 μ)) :
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))))
      have hpres : MeasurePreserving (fun s : G => g⁻¹ * s) μ μ := measurePreserving_smul g⁻¹ μ
      have hquasi : QuasiMeasurePreserving (fun s : G => g⁻¹ * s) μ μ :=
        hpres.quasiMeasurePreserving
      have hcomposed := hquasi.ae_eq_comp hinput
      filter_upwards [houtput, hscalar, hvector, hcomposed] with s hout hscalar hvector hin
      simp only [Function.comp_apply] at hin
      rw [hout, hscalar, hvector, hin]
    | add z w hz hw =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (fun x y => x + y) hz hw
  let F : (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) →⋆*
      (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :=
    { toFun := TensorProduct.mapLCompletion (1 : H →L[ℂ] H)
      map_one' := TensorProduct.mapLCompletion_id_id ℂ H (Lp ℂ 2 μ)
      map_mul' := fun x y => by
        simpa only [one_mul] using TensorProduct.mapLCompletion_mul (1 : H →L[ℂ] H) 1 x y
      map_star' := fun x => by
        simpa only [star_one] using (TensorProduct.star_mapLCompletion (1 : H →L[ℂ] H) x).symm }
  refine
    { toMonoidHom := (Unitary.map F).toMonoidHom.comp (haarLeftRegular G μ ℂ).toMonoidHom
      continuous_orbit := ?_ }
  intro z
  change Continuous fun g => TensorProduct.mapLCompletion (1 : H →L[ℂ] H)
    (haarLeftRegular G μ ℂ g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z
  have htransport (g : G) : TensorProduct.mapLCompletion (1 : H →L[ℂ] H)
      (haarLeftRegular G μ ℂ g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z =
      E.symm ((haarLeftRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ) (E z)) := by
    apply E.injective
    rw [E.apply_symm_apply]
    exact hintertwine g z
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
  have hcontinuous := E.symm.continuous.comp ((haarLeftRegular G μ H).continuous_orbit (E z))
  change @Continuous G (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) _
    m.toUniformSpace.toTopologicalSpace
      (fun g => E.symm ((haarLeftRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ) (E z))) at hcontinuous
  rw [htop] at hcontinuous
  simpa only [htransport] using hcontinuous

/-- **Exact right-factor operator of tensor Haar translation.** Let `G` be a locally compact
Borel topological group with regular Haar measure `μ` and `H` a complete complex Hilbert
space. Let `λ_g^H ξ(s)=ξ(g⁻¹s)` on `Lp H 2 μ` and `T=Completion(H⊗Lp ℂ 2 μ)`, with
`U=tensorToLpRight μ : T ≃ₗᵢ[ℂ] Lp H 2 μ`. for `g∈G`, the representation value is
`TensorProduct.mapLCompletion I_H (haarLeftRegular G μ ℂ g)=I_H⊗λ_g^ℂ`. -/
@[simp]
theorem haarLeftRegularTensor_apply (g : G) :
    (haarLeftRegularTensor G μ H g :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
      TensorProduct.mapLCompletion (ContinuousLinearMap.id ℂ H)
        (haarLeftRegular G μ ℂ g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  rfl

end

end StronglyContinuousUnitaryRepresentation
