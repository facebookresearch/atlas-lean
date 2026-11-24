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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.RegularCoefficientAlgebra
public import MathlibExt.Analysis.VonNeumannAlgebra.Generated
public import Mathlib.Algebra.Star.Subalgebra

/-!
# The actual generated regular crossed-product model on Haar Lp

The original regular coefficient operators and Haar left unitaries generate
the least concrete von Neumann algebra on the same Lp H 2 measure carrier.
The coefficient and group maps retain their original values in that subtype,
with the original covariance equation and weakly closed generated carrier.

This is the verified Lp/C_c regular model. A normal source embedding and the
original Connes tensor ambient transport remain separate strict prerequisites;
neither is assumed or represented by a different carrier here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped Topology CStarAlgebra

namespace VonNeumannAlgebra
namespace NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- The literal original regular coefficient and Haar left generator set. -/
def crossedProductGenerators (α : NormalAction G M) : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  Set.range (regularCoefficient μ α) ∪
    Set.range (fun g : G => (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
      Lp H 2 μ →L[ℂ] Lp H 2 μ))

/-- The least weakly closed von Neumann algebra containing the original regular pair on actual Lp. -/
def crossedProductLp (α : NormalAction G M) : VonNeumannAlgebra (Lp H 2 μ) :=
  VonNeumannAlgebra.generatedBy (crossedProductGenerators μ α)

/-- Every original regular coefficient belongs to this same generated carrier. -/
theorem regularCoefficient_mem_crossedProductLp (α : NormalAction G M) (x : M) :
    regularCoefficient μ α x ∈ crossedProductLp μ α :=
  VonNeumannAlgebra.subset_generatedBy _ (Or.inl (Set.mem_range_self x))

/-- Every original Haar left unitary belongs to this same generated carrier. -/
theorem haarLeftRegular_mem_crossedProductLp (α : NormalAction G M) (g : G) :
    (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
      Lp H 2 μ →L[ℂ] Lp H 2 μ) ∈ crossedProductLp μ α :=
  VonNeumannAlgebra.subset_generatedBy _ (Or.inr (Set.mem_range_self g))

/-- The actual canonical coefficient star homomorphism, restricted only by proved generator membership. -/
def crossedProductCoefficient (α : NormalAction G M) : M →⋆ₐ[ℂ] crossedProductLp μ α :=
  (regularCoefficientHom μ α).codRestrict (crossedProductLp μ α).toStarSubalgebra
    (regularCoefficient_mem_crossedProductLp μ α)

/-- The canonical coefficient map retains its original regular operator value. -/
@[simp]
theorem crossedProductCoefficient_apply (α : NormalAction G M) (x : M) :
    (crossedProductCoefficient μ α x : Lp H 2 μ →L[ℂ] Lp H 2 μ) = regularCoefficient μ α x :=
  rfl

/-- The actual Haar implementing unitary inside the original generated subtype. -/
def crossedProductGroupUnitary (α : NormalAction G M) (g : G) :
    unitary (crossedProductLp μ α) :=
  ⟨⟨StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g,
      haarLeftRegular_mem_crossedProductLp μ α g⟩, by
    constructor
    · apply Subtype.ext
      exact (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g).property.1
    · apply Subtype.ext
      exact (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g).property.2⟩

/-- The implementing unitary is the original Haar left operator at every group element. -/
@[simp]
theorem crossedProductGroupUnitary_coe (α : NormalAction G M) (g : G) :
    ((crossedProductGroupUnitary μ α g : crossedProductLp μ α) :
      Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  rfl

/-- The original Haar group operators form the actual unitary homomorphism into the generated carrier. -/
def crossedProductGroupUnitaryHom (α : NormalAction G M) : G →* unitary (crossedProductLp μ α) where
  toFun := crossedProductGroupUnitary μ α
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun U : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) => U.val)
      (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H).toMonoidHom.map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun U : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) => U.val)
      ((StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H).toMonoidHom.map_mul g h)

/-- The actual canonical maps in the generated carrier retain the original normal-action covariance. -/
theorem crossedProduct_covariance (α : NormalAction G M) (g : G) (x : M) :
    (crossedProductGroupUnitary μ α g : crossedProductLp μ α) * crossedProductCoefficient μ α x *
      star (crossedProductGroupUnitary μ α g : crossedProductLp μ α) =
        crossedProductCoefficient μ α (α g x) := by
  apply Subtype.ext
  exact regularCoefficient_covariance μ α g x

/-- A concrete von Neumann algebra contains this model exactly when it contains both original generator families. -/
theorem crossedProductLp_le_iff (α : NormalAction G M) (N : VonNeumannAlgebra (Lp H 2 μ)) :
    crossedProductLp μ α ≤ N ↔
      (∀ x : M, regularCoefficient μ α x ∈ N) ∧
        ∀ g : G, (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
          Lp H 2 μ →L[ℂ] Lp H 2 μ) ∈ N := by
  rw [crossedProductLp, VonNeumannAlgebra.generatedBy_le_iff]
  simp only [crossedProductGenerators, Set.union_subset_iff, Set.range_subset_iff]
  exact Iff.rfl

/-- The same generated regular carrier is closed in the actual weak operator topology. -/
theorem crossedProductLp_isClosedWOT (α : NormalAction G M) :
    IsClosed {T : Lp H 2 μ →WOT[ℂ] Lp H 2 μ | T.toCLM ∈ crossedProductLp μ α} :=
  VonNeumannAlgebra.generatedBy_isClosedWOT (crossedProductGenerators μ α)

end

end NormalAction
end VonNeumannAlgebra
