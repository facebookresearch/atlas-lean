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
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CoefficientFaithfulness
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CoefficientNormality

/-!
# The original tensor crossed-product normal faithful coefficient map

The canonical coefficient map retains its original tensor operator value.
Its vector-functional pullback is the same literal functional as the one
through the already proved spatial normal coefficient map. Actual predual
pullback and the vector-functional criterion give normality in the generated
source subtype. Original tensor coefficient injectivity gives faithfulness.

This supplies the normal source embedding needed by the original H-first
crossed-product definition, with no supplied normality, model or isometry.
The stronger Connes coefficient M tensor LInfinity clause remains separate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped TensorProduct InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- The canonical source tensor coefficient map with its actual proved normality. -/
def crossedProductTensorCoefficientNormalHom (α : NormalAction G M) :
    NormalStarAlgHom M (crossedProductTensor μ α) := by
  let S := crossedProductTensor μ α
  let N := spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ))
  let f := crossedProductTensorCoefficient μ α
  let F : M →L[ℂ] S := ⟨LinearMap.ofClass f, map_continuous f⟩
  let n := regularCoefficientSpatialNormalHom μ α
  have hn (x : M) :
      (n x : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) = regularCoefficientTensor μ α x :=
    rfl
  refine NormalStarAlgHom.ofVectorFunctionalPullbacks f ?_
  intro ξ η
  let φ : normalFunctionalSpace N :=
    ⟨vectorFunctional N ξ η, vectorFunctional_mem_normalFunctionalSpace N ξ η⟩
  have hmem := n.predualPullback_mem φ
  have hEq : (vectorFunctional S ξ η).comp F =
      (vectorFunctional N ξ η).comp n.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      _ = vectorFunctional S ξ η (f x) := rfl
      _ = inner ℂ ξ ((f x : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) η) :=
        vectorFunctional_apply S ξ η (f x)
      _ = inner ℂ ξ (regularCoefficientTensor μ α x η) :=
        congrArg (fun A : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) => inner ℂ ξ (A η))
            (crossedProductTensorCoefficient_apply μ α x)
      _ = inner ℂ ξ ((n x : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) η) :=
        congrArg (fun A : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) => inner ℂ ξ (A η)) (hn x).symm
      _ = vectorFunctional N ξ η (n x) := (vectorFunctional_apply N ξ η (n x)).symm
      _ = ((vectorFunctional N ξ η).comp n.toContinuousLinearMap) x := rfl
  change (vectorFunctional S ξ η).comp F ∈ normalFunctionalSpace M
  rw [hEq]
  exact hmem

/-- The normal source coefficient map is the original canonical coefficient in the generated algebra. -/
@[simp]
theorem crossedProductTensorCoefficientNormalHom_apply (α : NormalAction G M) (x : M) :
    crossedProductTensorCoefficientNormalHom μ α x = crossedProductTensorCoefficient μ α x :=
  rfl

/-- Its underlying operator is the exact original H-first tensor coefficient. -/
@[simp]
theorem crossedProductTensorCoefficientNormalHom_coe (α : NormalAction G M) (x : M) :
    (crossedProductTensorCoefficientNormalHom μ α x :
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) = regularCoefficientTensor μ α x :=
  rfl

/-- The same actual normal coefficient embedding into the source crossed product is faithful. -/
theorem crossedProductTensorCoefficientNormalHom_injective (α : NormalAction G M) :
    Function.Injective (crossedProductTensorCoefficientNormalHom μ α) := by
  intro x y hxy
  apply regularCoefficientTensor_injective μ α
  exact congrArg (fun z : crossedProductTensor μ α =>
    (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))) hxy

end

end VonNeumannAlgebra.NormalAction
