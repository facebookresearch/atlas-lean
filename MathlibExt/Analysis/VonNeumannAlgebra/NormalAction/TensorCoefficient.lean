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
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.RegularCoefficientAlgebra

/-!
# The original coefficient action on the H-first Hilbert tensor

The source normal action acts through the actual coefficient operator and
computed tensor/L2 coordinates. The source tensor order, coefficient norm
bound, pointwise values and star-algebra laws are retained. These are the
plain bounded tensor coefficients needed by the spatial-range constructor.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.HaarL2 Filter
open scoped TensorProduct ENNReal Topology CompactlySupported InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.Regular]

/-- The original bounded coefficient operator on the actual H-first completed Hilbert tensor. -/
def regularCoefficientTensor (α : NormalAction G M) (x : M) :
    UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) :=
  (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ).symm.conjStarAlgEquiv (regularCoefficient μ α x)

/-- The original tensor coefficient action with its actual unital complex star-algebra laws. -/
def regularCoefficientTensorHom (α : NormalAction G M) :
    M →⋆ₐ[ℂ] (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :=
  (L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (regularCoefficientHom μ α)

/-- The tensor coefficient homomorphism has the same original bounded operator value. -/
@[simp]
theorem regularCoefficientTensorHom_apply (α : NormalAction G M) (x : M) :
    regularCoefficientTensorHom μ α x = regularCoefficientTensor μ α x :=
  rfl

/-- The actual source algebra norm bounds the original tensor coefficient operator. -/
theorem norm_regularCoefficientTensor_le (α : NormalAction G M) (x : M) :
    ‖regularCoefficientTensor μ α x‖ ≤ ‖x‖ := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  apply (regularCoefficientTensor μ α x).opNorm_le_bound (norm_nonneg x)
  intro z
  change ‖E.symm (regularCoefficient μ α x (E z))‖ ≤ ‖x‖ * ‖z‖
  rw [E.symm.norm_map]
  simpa only [E.norm_map] using regularCoefficient_norm_apply_le μ α x (E z)

/-- In actual L2 coordinates, every tensor coefficient has the original pointwise representative. -/
theorem regularCoefficientTensor_ae_eq (α : NormalAction G M) (x : M)
    (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :
    L2.tensorToLpRight μ (regularCoefficientTensor μ α x z) =ᵐ[μ]
      fun s => (α s⁻¹ x : H →L[ℂ] H) (L2.tensorToLpRight μ z s) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  change E (E.symm (regularCoefficient μ α x (E z))) =ᵐ[μ] _
  rw [E.apply_symm_apply]
  exact regularCoefficient_ae_eq μ α x (E z)

/-- The original pure compact-support scalar tensor has the exact source coefficient formula. -/
theorem regularCoefficientTensor_apply_compactSupport_tmul_ae (α : NormalAction G M) (x : M)
    (f : C_c(G, ℂ)) (ξ : H) :
    L2.tensorToLpRight μ
        (regularCoefficientTensor μ α x
          ((ξ ⊗ₜ[ℂ] compactSupportInclusion (H := ℂ) μ f : H ⊗[ℂ] (Lp ℂ 2 μ)) :
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))) =ᵐ[μ]
      fun s => (α s⁻¹ x : H →L[ℂ] H) (f s • ξ) := by
  have hpure := L2.tensorToLpRight_tmul_ae (𝕜 := ℂ) μ ξ (compactSupportInclusion (H := ℂ) μ f)
  have hscalar := compactSupportInclusion_ae_eq (H := ℂ) μ f
  filter_upwards [regularCoefficientTensor_ae_eq μ α x
    ((ξ ⊗ₜ[ℂ] compactSupportInclusion (H := ℂ) μ f : H ⊗[ℂ] (Lp ℂ 2 μ)) :
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))), hpure, hscalar] with s hcoeff hvector hscalar
  rw [hcoeff, hvector, hscalar]

end

end VonNeumannAlgebra.NormalAction
