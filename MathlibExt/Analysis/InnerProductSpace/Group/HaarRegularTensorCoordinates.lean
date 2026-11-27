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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRegularTensorRepresentation

/-!
# Exact Haar coordinates of a tensor left representation

On `T=Completion(H⊗Lp ℂ 2 μ)`, the Haar unitary is `V_g=I_H⊗λ_g^ℂ`. The tensor-to-L² unitary `U`
intertwines it with the Hilbert-valued Haar operator: `U V_g=λ_g^H U`.

Equivalently, conjugation gives `U V_g U⁻¹=λ_g^H`. The identities retain the inverse
left-translation coordinate `g⁻¹s` and the same Haar and Hilbert norms.
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

/-- **Tensor-to-L² intertwining of Haar left translation.** Let `G` be a locally compact Borel
topological group with regular Haar measure `μ` and `H` a complete complex Hilbert space.
Let `λ_g^H ξ(s)=ξ(g⁻¹s)` on `Lp H 2 μ` and `T=Completion(H⊗Lp ℂ 2 μ)`, with
`U=tensorToLpRight μ : T ≃ₗᵢ[ℂ] Lp H 2 μ`. for `g∈G`, `z∈T` and `V_g=haarLeftRegularTensor
G μ H g`, `U(V_g z)=λ_g^H(Uz)` as L² classes. -/
theorem haarLeftRegularTensor_coordinates (g : G)
    (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :
    L2.tensorToLpRight μ
        ((haarLeftRegularTensor G μ H g :
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) z) =
      (haarLeftRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ) (L2.tensorToLpRight μ z) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  rw [haarLeftRegularTensor_apply]
  change E (TensorProduct.mapLCompletion (1 : H →L[ℂ] H)
      (haarLeftRegular G μ ℂ g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) z) =
    (haarLeftRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ) (E z)
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
      ⟨hpres.measurable.aemeasurable, by rw [hpres.map_eq]⟩
    have hcomposed := hquasi.ae_eq_comp hinput
    filter_upwards [houtput, hscalar, hvector, hcomposed] with s hout hscalar hvector hin
    simp only [Function.comp_apply] at hin
    rw [hout, hscalar, hvector, hin]
  | add z w hz hw =>
    simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (fun x y => x + y) hz hw

/-- **Operator conjugation of tensor Haar coordinates.** Let `G` be a locally compact Borel
topological group with regular Haar measure `μ` and `H` a complete complex Hilbert space.
Let `λ_g^H ξ(s)=ξ(g⁻¹s)` on `Lp H 2 μ` and `T=Completion(H⊗Lp ℂ 2 μ)`, with
`U=tensorToLpRight μ : T ≃ₗᵢ[ℂ] Lp H 2 μ`. for `V_g=I_H⊗λ_g^ℂ`,
`U.conjStarAlgEquiv(V_g)=λ_g^H`, equivalently `U V_g U⁻¹=λ_g^H`. -/
theorem haarLeftRegularTensor_conjStarAlgEquiv (g : G) :
    (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ).conjStarAlgEquiv
        (haarLeftRegularTensor G μ H g :
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
      (haarLeftRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  apply ContinuousLinearMap.ext
  intro ξ
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  exact (haarLeftRegularTensor_coordinates G μ H g (E.symm ξ)).trans
    (congrArg (haarLeftRegular G μ H g : Lp H 2 μ →L[ℂ] Lp H 2 μ) (E.apply_symm_apply ξ))

end

end StronglyContinuousUnitaryRepresentation
