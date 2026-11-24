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

public import MathlibExt.Analysis.VonNeumannAlgebra.TensorCommutant
public import MathlibExt.MeasureTheory.Function.L2Space.TensorMap
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.TensorCoefficient

/-!
# The original coefficient's actual spatial ambient range

The original tensor coefficient commutes with every constant operator from
the original source commutant. The full-right commutant extraction and the
actual bicommutant identity put it in M tensor B(L2). Its subtype star map
retains the same operator values. The stronger Connes M tensor LInfinity
coefficient target is a separate unfinished source clause.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped TensorProduct ENNReal Topology

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.Regular]

/-- The original tensor coefficient belongs to the actual source spatial ambient algebra. -/
theorem regularCoefficientTensor_mem_spatialTensorProduct
    (α : NormalAction G M) (x : M) :
    regularCoefficientTensor μ α x ∈ spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ)) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  have hpi (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :
      E (regularCoefficientTensor μ α x z) = regularCoefficient μ α x (E z) := by
    change E (E.symm (regularCoefficient μ α x (E z))) = _
    exact E.apply_symm_apply _
  have hconstant (B : H →L[ℂ] H) (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :
      E (TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) z) =
        B.compLpL 2 μ (E z) :=
    L2.tensorToLpRight_mapLCompletion μ B z
  have hcomm (B : H →L[ℂ] H) (hB : B ∈ M.commutant) :
      TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) *
          regularCoefficientTensor μ α x =
        regularCoefficientTensor μ α x *
          TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) := by
    apply ContinuousLinearMap.ext
    intro z
    apply E.injective
    change E (TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ))
        (regularCoefficientTensor μ α x z)) =
      E (regularCoefficientTensor μ α x
        (TensorProduct.mapLCompletion B (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) z))
    rw [hconstant, hpi, hpi, hconstant]
    apply Lp.ext
    filter_upwards [B.coeFn_compLpL (regularCoefficient μ α x (E z)),
      regularCoefficient_ae_eq μ α x (E z),
      regularCoefficient_ae_eq μ α x (B.compLpL 2 μ (E z)), B.coeFn_compLpL (E z)]
      with s hleft hcoefficient hright hvector
    rw [hleft, hcoefficient, hright, hvector]
    have he := mem_commutant_iff.mp hB (α s⁻¹ x : H →L[ℂ] H) (α s⁻¹ x).property
    exact (congrArg (fun C : H →L[ℂ] H => C (E z s)) he).symm
  rw [← (spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ))).commutant_commutant]
  apply mem_commutant_iff.mpr
  intro A hA
  obtain ⟨B, hB, hAB⟩ := exists_mapLCompletion_id_of_mem_commutant_spatialTensorProduct_top M A hA
  rw [hAB]
  exact hcomm B hB

/-- The original coefficient star homomorphism restricted to its proved spatial codomain. -/
def regularCoefficientSpatialHom (α : NormalAction G M) :
    M →⋆ₐ[ℂ] spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ)) where
  toFun x := ⟨regularCoefficientTensor μ α x, regularCoefficientTensor_mem_spatialTensorProduct μ α x⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (regularCoefficientTensorHom μ α)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (regularCoefficientTensorHom μ α) x y
  map_zero' := by
    apply Subtype.ext
    exact map_zero (regularCoefficientTensorHom μ α)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (regularCoefficientTensorHom μ α) x y
  commutes' c := by
    apply Subtype.ext
    exact (regularCoefficientTensorHom μ α).commutes c
  map_star' x := by
    apply Subtype.ext
    exact map_star (regularCoefficientTensorHom μ α) x

end

end VonNeumannAlgebra.NormalAction
