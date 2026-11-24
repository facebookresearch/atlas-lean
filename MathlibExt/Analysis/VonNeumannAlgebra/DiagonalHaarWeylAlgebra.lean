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

public import MathlibExt.MeasureTheory.Measure.RadonProduct.Haar
public import MathlibExt.Analysis.VonNeumannAlgebra.HaarWeylAlgebra

/-!
# The diagonal Weyl algebra on full Hilbert-valued Radon product L2

The original Haar left representation of the actual product group is
restricted along the diagonal homomorphism. The character representation
uses actual character pullback along the second coordinate. These operators
generate a concrete von Neumann algebra on the full `Lp H 2 (radonProd μ μ)`
for the Borel sigma-algebra of the topological product.

All group, Hilbert and measure carriers are the original ones. The
generator unitaries retain their bounded-operator values and a.e. diagonal
translation and second-coordinate character formulas. The inverse character
uses the same original multiplier at `χ⁻¹`. There is no countability,
s-finiteness or nonzero-Hilbert-space assumption.

This construction selects no Fourier unitary, spatial shear or factor
isomorphism. Their original source identifications remain separate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped Topology CStarAlgebra

namespace VonNeumannAlgebra

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual Borel measurable space of the original topological square. -/
local instance instDiagonalWeylProductMeasurableSpace : MeasurableSpace (G × G) := borel (G × G)
local instance instDiagonalWeylProductBorelSpace : BorelSpace (G × G) := ⟨rfl⟩

/-- The original product-Haar representation restricted along the actual diagonal homomorphism. -/
def diagonalHaarLeftRegular :
    StronglyContinuousUnitaryRepresentation G (Lp H 2 (Measure.radonProd μ μ)) where
  toMonoidHom :=
    (StronglyContinuousUnitaryRepresentation.haarLeftRegular (G × G) (Measure.radonProd μ μ) H).toMonoidHom.comp
      (ContinuousMonoidHom.diag G).toMonoidHom
  continuous_orbit ξ :=
    ((StronglyContinuousUnitaryRepresentation.haarLeftRegular
      (G × G) (Measure.radonProd μ μ) H).continuous_orbit ξ).comp
        (ContinuousMonoidHom.diag G).continuous

/-- The diagonal representation is the unchanged original Haar operator at `(g,g)`. -/
@[simp]
theorem diagonalHaarLeftRegular_apply (g : G) :
    (diagonalHaarLeftRegular (H := H) μ g :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
      (StronglyContinuousUnitaryRepresentation.haarLeftRegular
        (G × G) (Measure.radonProd μ μ) H (g, g) :
          Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) :=
  rfl

/-- Both original coordinates translate by `g⁻¹` on every full product-L2 vector a.e. -/
theorem diagonalHaarLeftRegular_ae_eq (g : G) (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalHaarLeftRegular (H := H) μ g :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ξ =ᵐ[Measure.radonProd μ μ]
        fun z : G × G => ξ (g⁻¹ * z.1, g⁻¹ * z.2) :=
  StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq
    (G × G) (Measure.radonProd μ μ) H (g, g) ξ

/-- Pull back the actual continuous-character group along the literal second projection. -/
def secondCoordinateCharacterMap : PontryaginDual G →ₜ* PontryaginDual (G × G) :=
  PontryaginDual.map (ContinuousMonoidHom.snd G G)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The pulled-back character is the same original character on the second coordinate. -/
@[simp]
theorem secondCoordinateCharacterMap_apply (χ : PontryaginDual G) (z : G × G) :
    secondCoordinateCharacterMap χ z = χ z.2 :=
  rfl

/-- Actual second-coordinate character multiplication on the original full Hilbert-valued square. -/
def diagonalHaarCharacterRepresentation :
    StronglyContinuousUnitaryRepresentation (PontryaginDual G) (Lp H 2 (Measure.radonProd μ μ)) where
  toMonoidHom :=
    (HaarL2.characterMultiplierRepresentation (H := H) (Measure.radonProd μ μ)).toMonoidHom.comp
      (secondCoordinateCharacterMap (G := G)).toMonoidHom
  continuous_orbit ξ :=
    ((HaarL2.characterMultiplierRepresentation (H := H)
      (Measure.radonProd μ μ)).continuous_orbit ξ).comp
        (secondCoordinateCharacterMap (G := G)).continuous

omit [μ.Regular] in
/-- The character representation is the exact original multiplier at the pulled-back character. -/
@[simp]
theorem diagonalHaarCharacterRepresentation_apply (χ : PontryaginDual G) :
    (diagonalHaarCharacterRepresentation (H := H) μ χ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) =
        HaarL2.characterMultiplier (H := H) (Measure.radonProd μ μ)
          (secondCoordinateCharacterMap χ) :=
  rfl

omit [μ.Regular] in
/-- The character multiplier has its original positive second-coordinate values on all vectors a.e. -/
theorem diagonalHaarCharacterRepresentation_ae_eq (χ : PontryaginDual G)
    (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalHaarCharacterRepresentation (H := H) μ χ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ξ =ᵐ[Measure.radonProd μ μ]
        fun z : G × G => ((χ z.2 : Circle) : ℂ) • ξ z :=
  HaarL2.characterMultiplier_ae_eq (Measure.radonProd μ μ) (secondCoordinateCharacterMap χ) ξ

omit [μ.Regular] in
/-- The actual inverse-character operator keeps the original conjugate-coordinate convention a.e. -/
theorem diagonalHaarInverseCharacterRepresentation_ae_eq (χ : PontryaginDual G)
    (ξ : Lp H 2 (Measure.radonProd μ μ)) :
    (diagonalHaarCharacterRepresentation (H := H) μ χ⁻¹ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ξ =ᵐ[Measure.radonProd μ μ]
        fun z : G × G => ((χ⁻¹ z.2 : Circle) : ℂ) • ξ z :=
  diagonalHaarCharacterRepresentation_ae_eq μ χ⁻¹ ξ

/-- The actual original diagonal translations and second-coordinate character operator ranges. -/
def diagonalHaarWeylGenerators :
    Set (Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) :=
  Set.range (fun g : G => (diagonalHaarLeftRegular (H := H) μ g :
    Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ))) ∪
    Set.range (fun χ : PontryaginDual G => (diagonalHaarCharacterRepresentation (H := H) μ χ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)))

/-- The actual diagonal Weyl algebra on the original full Hilbert-valued Radon square. -/
def diagonalHaarWeylAlgebra : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ μ)) :=
  generatedBy (diagonalHaarWeylGenerators (H := H) μ)

/-- Every original diagonal Haar unitary belongs to the same full product-L2 generated algebra. -/
theorem diagonalHaarLeftRegular_mem_diagonalHaarWeylAlgebra (g : G) :
    (diagonalHaarLeftRegular (H := H) μ g :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ∈
        diagonalHaarWeylAlgebra (H := H) μ :=
  subset_generatedBy _ (Or.inl (Set.mem_range_self g))

/-- Every original second-coordinate character unitary belongs to the same generated algebra. -/
theorem diagonalHaarCharacterRepresentation_mem_diagonalHaarWeylAlgebra (χ : PontryaginDual G) :
    (diagonalHaarCharacterRepresentation (H := H) μ χ :
      Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ∈
        diagonalHaarWeylAlgebra (H := H) μ :=
  subset_generatedBy _ (Or.inr (Set.mem_range_self χ))

/-- Containment of the actual diagonal Weyl algebra is precisely containment of its original operators. -/
theorem diagonalHaarWeylAlgebra_le_iff
    (N : VonNeumannAlgebra (Lp H 2 (Measure.radonProd μ μ))) :
    diagonalHaarWeylAlgebra (H := H) μ ≤ N ↔
      (∀ g : G, (diagonalHaarLeftRegular (H := H) μ g :
        Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ∈ N) ∧
      ∀ χ : PontryaginDual G, (diagonalHaarCharacterRepresentation (H := H) μ χ :
        Lp H 2 (Measure.radonProd μ μ) →L[ℂ] Lp H 2 (Measure.radonProd μ μ)) ∈ N := by
  rw [diagonalHaarWeylAlgebra, generatedBy_le_iff]
  simp only [diagonalHaarWeylGenerators, Set.union_subset_iff, Set.range_subset_iff]
  exact Iff.rfl

/-- The original full product-L2 diagonal Weyl carrier is closed in the actual weak operator topology. -/
theorem diagonalHaarWeylAlgebra_isClosedWOT :
    IsClosed {T : Lp H 2 (Measure.radonProd μ μ) →WOT[ℂ] Lp H 2 (Measure.radonProd μ μ) |
      T.toCLM ∈ diagonalHaarWeylAlgebra (H := H) μ} :=
  generatedBy_isClosedWOT (diagonalHaarWeylGenerators (H := H) μ)

end

end VonNeumannAlgebra
