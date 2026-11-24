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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CrossedProductTensor
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CharacterCovariance
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.TensorCharacterMultiplier
public import MathlibExt.Analysis.VonNeumannAlgebra.UnitaryAction

/-!
# The original normal dual character action on the H-first tensor crossed product

The actual id_H tensor scalar character unitary fixes the original tensor
coefficients and scales the original id_H tensor Haar operators. Those
literal generator formulas preserve the same source generated algebra.
The verified generic normalizing unitary constructor provides its normal
actual dual action and all norm-continuous inverse predual orbits.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.HaarL2
open scoped TensorProduct CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

omit [μ.IsHaarMeasure] in
/-- The actual right-tensor character unitary fixes every original tensor coefficient operator. -/
theorem characterMultiplierTensor_fix_regularCoefficientTensor (α : NormalAction G M)
    (χ : PontryaginDual G) (x : M) :
    (characterMultiplierTensorRepresentation (H := H) μ χ :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) * regularCoefficientTensor μ α x *
      star (characterMultiplierTensorRepresentation (H := H) μ χ :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) = regularCoefficientTensor μ α x := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  let e := E.conjStarAlgEquiv
  let U := (characterMultiplierTensorRepresentation (H := H) μ χ :
    UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))
  let P := regularCoefficientTensor μ α x
  have hU : e U = (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
    characterMultiplierTensor_conjStarAlgEquiv μ χ
  have hP : e P = regularCoefficient μ α x := by
    have he : P = e.symm (regularCoefficient μ α x) := rfl
    rw [he]
    exact e.apply_symm_apply _
  apply e.injective
  calc
    e (U * P * star U) = e (U * P) * e (star U) := map_mul e _ _
    _ = (e U * e P) * star (e U) :=
      congrArg₂ (fun A B : Lp H 2 μ →L[ℂ] Lp H 2 μ => A * B) (map_mul e U P) (map_star e U)
    _ = (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) *
        regularCoefficient μ α x * star (characterMultiplierUnitary (H := H) μ χ :
          Lp H 2 μ →L[ℂ] Lp H 2 μ) := by rw [hU, hP]
    _ = regularCoefficient μ α x := characterMultiplier_fix_regularCoefficient μ α χ x
    _ = e P := hP.symm

/-- The actual right-tensor character unitary scales the original tensor Haar implementer by χ(g). -/
theorem characterMultiplierTensor_scale_haarLeftRegularTensor (χ : PontryaginDual G) (g : G) :
    (characterMultiplierTensorRepresentation (H := H) μ χ :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) *
      (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) *
      star (characterMultiplierTensorRepresentation (H := H) μ χ :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
        ((χ g : Circle) : ℂ) • (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  let e := E.conjStarAlgEquiv
  let U := (characterMultiplierTensorRepresentation (H := H) μ χ :
    UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))
  let L := (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
    UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))
  have hU : e U = (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
    characterMultiplierTensor_conjStarAlgEquiv μ χ
  have hL : e L = (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
      Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
    StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor_conjStarAlgEquiv G μ H g
  apply e.injective
  calc
    e (U * L * star U) = e (U * L) * e (star U) := map_mul e _ _
    _ = (e U * e L) * star (e U) :=
      congrArg₂ (fun A B : Lp H 2 μ →L[ℂ] Lp H 2 μ => A * B) (map_mul e U L) (map_star e U)
    _ = (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) *
        (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
          Lp H 2 μ →L[ℂ] Lp H 2 μ) * star (characterMultiplierUnitary (H := H) μ χ :
            Lp H 2 μ →L[ℂ] Lp H 2 μ) := by rw [hU, hL]
    _ = ((χ g : Circle) : ℂ) • (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) := characterMultiplier_scale_haarLeftRegular μ χ g
    _ = ((χ g : Circle) : ℂ) • e L := by rw [hL]
    _ = e (((χ g : Circle) : ℂ) • L) := (map_smul e ((χ g : Circle) : ℂ) L).symm

/-- The original right-tensor character conjugation preserves the actual generated tensor carrier. -/
theorem tensorCharacterConjugation_mem_crossedProductTensor (α : NormalAction G M) (χ : PontryaginDual G)
    (T : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) (hT : T ∈ crossedProductTensor μ α) :
    (characterMultiplierTensorRepresentation (H := H) μ χ :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) * T *
      star (characterMultiplierTensorRepresentation (H := H) μ χ :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ∈ crossedProductTensor μ α := by
  apply unitaryConjugation_generatedBy_mem (crossedProductTensorGenerators μ α)
    (characterMultiplierTensorRepresentation (H := H) μ χ) ?_ T hT
  intro A hA
  rcases hA with (⟨x, rfl⟩ | ⟨g, rfl⟩)
  · rw [characterMultiplierTensor_fix_regularCoefficientTensor μ α χ x]
    exact StarAlgebra.subset_adjoin ℂ _ (Or.inl (Set.mem_range_self x))
  · rw [characterMultiplierTensor_scale_haarLeftRegularTensor μ χ g]
    exact (StarAlgebra.adjoin ℂ (crossedProductTensorGenerators μ α)).smul_mem
      (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_range_self g))) _

/-- The original right-tensor character unitary has the exact source normalization equality. -/
theorem tensorCharacterConjugation_normalizes (α : NormalAction G M) (χ : PontryaginDual G) :
    (fun T : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) =>
      (characterMultiplierTensorRepresentation (H := H) μ χ :
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) * T *
        star (characterMultiplierTensorRepresentation (H := H) μ χ :
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))) ''
      (crossedProductTensor μ α : Set (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))) =
      (crossedProductTensor μ α : Set (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))) := by
  apply unitaryConjugationStarAlgEquiv_image (crossedProductTensor μ α)
    (characterMultiplierTensorRepresentation (H := H) μ χ)
    (tensorCharacterConjugation_mem_crossedProductTensor μ α χ)
  intro T hT
  have hstar : characterMultiplierTensorRepresentation (H := H) μ χ⁻¹ =
      star (characterMultiplierTensorRepresentation (H := H) μ χ) :=
    (characterMultiplierTensorRepresentation (H := H) μ).toMonoidHom.map_inv χ
  have hinv := tensorCharacterConjugation_mem_crossedProductTensor μ α χ⁻¹ T hT
  simpa only [hstar, Unitary.coe_star, star_star] using hinv

/-- The original tensor crossed product has its actual normal dual character action. -/
def tensorCharacterNormalAction (α : NormalAction G M) :
    NormalAction (PontryaginDual G) (crossedProductTensor μ α) :=
  unitaryConjugationNormalAction (crossedProductTensor μ α)
    (characterMultiplierTensorRepresentation (H := H) μ) (tensorCharacterConjugation_normalizes μ α)

/-- The original tensor dual action fixes the canonical original source coefficient. -/
theorem tensorCharacterNormalAction_fix_coefficient (α : NormalAction G M) (χ : PontryaginDual G) (x : M) :
    tensorCharacterNormalAction μ α χ (crossedProductTensorCoefficient μ α x) =
      crossedProductTensorCoefficient μ α x := by
  apply Subtype.ext
  change (unitaryConjugationNormalHom (crossedProductTensor μ α)
    (characterMultiplierTensorRepresentation (H := H) μ) (tensorCharacterConjugation_normalizes μ α)
      χ (crossedProductTensorCoefficient μ α x) :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) = _
  rw [unitaryConjugationNormalHom_apply, crossedProductTensorCoefficient_apply]
  exact characterMultiplierTensor_fix_regularCoefficientTensor μ α χ x

/-- The original tensor dual action has Connes's positive χ(g) scaling of the original Haar generator. -/
theorem tensorCharacterNormalAction_scale_group (α : NormalAction G M) (χ : PontryaginDual G) (g : G) :
    tensorCharacterNormalAction μ α χ (crossedProductTensorGroupUnitary μ α g : crossedProductTensor μ α) =
      ((χ g : Circle) : ℂ) • (crossedProductTensorGroupUnitary μ α g : crossedProductTensor μ α) := by
  apply Subtype.ext
  change (unitaryConjugationNormalHom (crossedProductTensor μ α)
    (characterMultiplierTensorRepresentation (H := H) μ) (tensorCharacterConjugation_normalizes μ α)
      χ (crossedProductTensorGroupUnitary μ α g : crossedProductTensor μ α) :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) = _
  rw [unitaryConjugationNormalHom_apply, crossedProductTensorGroupUnitary_coe]
  exact characterMultiplierTensor_scale_haarLeftRegularTensor μ χ g

end

end VonNeumannAlgebra.NormalAction
