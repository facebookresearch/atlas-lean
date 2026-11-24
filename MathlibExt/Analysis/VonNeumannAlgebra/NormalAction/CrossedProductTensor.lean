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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.SpatialCoefficient
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRegularTensorCoordinates

/-!
# The original generated crossed product on the H-first tensor

The original tensor coefficients and actual id_H tensor scalar-Haar unitaries
generate a concrete von Neumann algebra on the literal completed H-first
Hilbert tensor. Both families belong to the original spatial ambient, so the
generated algebra is its actual von Neumann subalgebra. Canonical plain
coefficient and group maps keep the original bounded operator values.

The verified tensor/L2 coordinates transport the original Haar covariance.
The normal coefficient embedding waits for its actual normality constructor.
The stronger Connes M tensor LInfinity coefficient clause and full terminal
source equivalence proofs remain separate unfinished source obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped TensorProduct Topology CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- The literal source tensor coefficient and identity-H tensor Haar generator families. -/
def crossedProductTensorGenerators (α : NormalAction G M) :
    Set (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :=
  Set.range (regularCoefficientTensor μ α) ∪
    Set.range (fun g : G => (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))))

/-- The actual original source crossed product generated on the completed H-first tensor. -/
def crossedProductTensor (α : NormalAction G M) :
    VonNeumannAlgebra (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :=
  generatedBy (crossedProductTensorGenerators μ α)

/-- Every original tensor coefficient belongs to this same source generated algebra. -/
theorem regularCoefficientTensor_mem_crossedProductTensor (α : NormalAction G M) (x : M) :
    regularCoefficientTensor μ α x ∈ crossedProductTensor μ α :=
  subset_generatedBy _ (Or.inl (Set.mem_range_self x))

/-- Every actual identity-H tensor Haar unitary belongs to this same source generated algebra. -/
theorem haarLeftRegularTensor_mem_crossedProductTensor (α : NormalAction G M) (g : G) :
    (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ∈ crossedProductTensor μ α :=
  subset_generatedBy _ (Or.inr (Set.mem_range_self g))

/-- The original generated crossed product is contained in its actual source spatial ambient. -/
theorem crossedProductTensor_le_spatialTensorProduct (α : NormalAction G M) :
    crossedProductTensor μ α ≤ spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ)) := by
  apply generatedBy_le
  intro T hT
  rcases hT with (⟨x, rfl⟩ | ⟨g, rfl⟩)
  · exact regularCoefficientTensor_mem_spatialTensorProduct μ α x
  · change (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ∈
          spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ))
    rw [StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor_apply]
    exact tensorOperator_mem_spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ)) (1 : M)
      ⟨(StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ ℂ g :
        Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ), by trivial⟩

/-- The actual original plain coefficient star homomorphism into the same source generated subtype. -/
def crossedProductTensorCoefficient (α : NormalAction G M) : M →⋆ₐ[ℂ] crossedProductTensor μ α :=
  (regularCoefficientTensorHom μ α).codRestrict (crossedProductTensor μ α).toStarSubalgebra
    (regularCoefficientTensor_mem_crossedProductTensor μ α)

/-- The canonical source coefficient map is the same original tensor operator. -/
@[simp]
theorem crossedProductTensorCoefficient_apply (α : NormalAction G M) (x : M) :
    (crossedProductTensorCoefficient μ α x :
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) = regularCoefficientTensor μ α x :=
  rfl

/-- The actual source identity-H tensor Haar implementer inside the original generated algebra. -/
def crossedProductTensorGroupUnitary (α : NormalAction G M) (g : G) :
    unitary (crossedProductTensor μ α) :=
  ⟨⟨StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g,
      haarLeftRegularTensor_mem_crossedProductTensor μ α g⟩, by
    constructor
    · apply Subtype.ext
      exact (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g).property.1
    · apply Subtype.ext
      exact (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g).property.2⟩

/-- The canonical group implementer retains the actual original tensor Haar operator value. -/
@[simp]
theorem crossedProductTensorGroupUnitary_coe (α : NormalAction G M) (g : G) :
    ((crossedProductTensorGroupUnitary μ α g : crossedProductTensor μ α) :
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
      (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :=
  rfl

/-- The literal source tensor Haar operators form their actual group map in the generated subtype. -/
def crossedProductTensorGroupUnitaryHom (α : NormalAction G M) :
    G →* unitary (crossedProductTensor μ α) where
  toFun := crossedProductTensorGroupUnitary μ α
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun U : unitary (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) => U.val)
        (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H).toMonoidHom.map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun U : unitary (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) => U.val)
        ((StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H).toMonoidHom.map_mul g h)

/-- Original tensor coefficients and identity-H tensor Haar implementers satisfy the source covariance. -/
theorem regularCoefficientTensor_covariance (α : NormalAction G M) (g : G) (x : M) :
    (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) * regularCoefficientTensor μ α x *
      star (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) =
      regularCoefficientTensor μ α (α g x) := by
  let Φ := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  let e := Φ.conjStarAlgEquiv
  let L := (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
    UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
      UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))
  let P := regularCoefficientTensor μ α x
  have hL : e L = (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
      Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
    StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor_conjStarAlgEquiv G μ H g
  have hP (y : M) : e (regularCoefficientTensor μ α y) = regularCoefficient μ α y := by
    have hTensor : regularCoefficientTensor μ α y = e.symm (regularCoefficient μ α y) := rfl
    rw [hTensor]
    exact e.apply_symm_apply _
  apply e.injective
  calc
    e (L * P * star L) = e (L * P) * e (star L) := map_mul e _ _
    _ = (e L * e P) * star (e L) :=
      congrArg₂ (fun A B : Lp H 2 μ →L[ℂ] Lp H 2 μ => A * B) (map_mul e L P) (map_star e L)
    _ = (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) * regularCoefficient μ α x *
      star (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) := by rw [hL, hP x]
    _ = regularCoefficient μ α (α g x) := regularCoefficient_covariance μ α g x
    _ = e (regularCoefficientTensor μ α (α g x)) := (hP (α g x)).symm

/-- The actual source coefficient and group maps retain covariance inside the same generated algebra. -/
theorem crossedProductTensor_covariance (α : NormalAction G M) (g : G) (x : M) :
    (crossedProductTensorGroupUnitary μ α g : crossedProductTensor μ α) *
      crossedProductTensorCoefficient μ α x *
      star (crossedProductTensorGroupUnitary μ α g : crossedProductTensor μ α) =
        crossedProductTensorCoefficient μ α (α g x) := by
  apply Subtype.ext
  exact regularCoefficientTensor_covariance μ α g x

/-- Containment of the original source crossed product is exactly containment of its actual generators. -/
theorem crossedProductTensor_le_iff (α : NormalAction G M)
    (N : VonNeumannAlgebra (UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)))) :
    crossedProductTensor μ α ≤ N ↔
      (∀ x : M, regularCoefficientTensor μ α x ∈ N) ∧
        ∀ g : G, (StronglyContinuousUnitaryRepresentation.haarLeftRegularTensor G μ H g :
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
            UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) ∈ N := by
  rw [crossedProductTensor, generatedBy_le_iff]
  simp only [crossedProductTensorGenerators, Set.union_subset_iff, Set.range_subset_iff]
  exact Iff.rfl

/-- The actual original H-first source generated algebra is weak-operator closed. -/
theorem crossedProductTensor_isClosedWOT (α : NormalAction G M) :
    IsClosed {T : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →WOT[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) | T.toCLM ∈ crossedProductTensor μ α} :=
  generatedBy_isClosedWOT (crossedProductTensorGenerators μ α)

end

end VonNeumannAlgebra.NormalAction
