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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CrossedProductLp
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.CharacterCovariance
public import MathlibExt.Analysis.VonNeumannAlgebra.UnitaryConjugation

/-!
# Actual normal character conjugation on the generated Haar Lp algebra

The original positive-character multiplier preserves the actual star algebra
of regular generators, and therefore its original generated double commutant.
The inverse character gives the actual inverse on that same operator carrier.
Spatial vector-functional pullback supplies its proved normality.

The canonical coefficient map is fixed and the canonical Haar implementer is
scaled by chi(g). This constructs the normal automorphism group map on the
actual C_c/Lp model. The original Connes tensor-carrier transport and normal
source embedding remain their separate source prerequisites.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.HaarL2
open scoped CStarAlgebra

namespace VonNeumannAlgebra
namespace NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- The original character multiplier conjugates the same generated operator carrier into itself. -/
theorem characterConjugation_mem_crossedProductLp (α : NormalAction G M) (χ : PontryaginDual G)
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (hT : T ∈ crossedProductLp μ α) :
    (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) * T *
      star (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) ∈
        crossedProductLp μ α := by
  apply unitaryConjugation_generatedBy_mem (crossedProductGenerators μ α)
    (characterMultiplierUnitary (H := H) μ χ) ?_ T hT
  intro a ha
  rcases ha with (⟨x, rfl⟩ | ⟨g, rfl⟩)
  · rw [characterMultiplier_fix_regularCoefficient μ α χ x]
    exact StarAlgebra.subset_adjoin ℂ _ (Or.inl (Set.mem_range_self x))
  · rw [characterMultiplier_scale_haarLeftRegular μ χ g]
    exact (StarAlgebra.adjoin ℂ (crossedProductGenerators μ α)).smul_mem
      (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_range_self g))) _

/-- Actual character conjugation, with its proved inverse and normality, on the original generated algebra. -/
def characterConjugationNormalEquiv (α : NormalAction G M) (χ : PontryaginDual G) :
    NormalStarAlgEquiv (crossedProductLp μ α) (crossedProductLp μ α) := by
  refine unitaryConjugationNormalEquiv (crossedProductLp μ α)
    (characterMultiplierUnitary (H := H) μ χ) ?_ ?_
  · intro T hT
    exact characterConjugation_mem_crossedProductLp μ α χ T hT
  · intro T hT
    have hstar : characterMultiplierUnitary (H := H) μ χ⁻¹ =
        star (characterMultiplierUnitary (H := H) μ χ) :=
      (characterMultiplierUnitaryHom (H := H) μ).map_inv χ
    have hinv := characterConjugation_mem_crossedProductLp μ α χ⁻¹ T hT
    simpa only [hstar, Unitary.coe_star, star_star] using hinv

/-- The actual normal automorphism keeps the original positive-character spatial formula. -/
@[simp]
theorem characterConjugationNormalEquiv_apply (α : NormalAction G M) (χ : PontryaginDual G)
    (x : crossedProductLp μ α) :
    (characterConjugationNormalEquiv μ α χ x : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) *
        (x : Lp H 2 μ →L[ℂ] Lp H 2 μ) *
        star (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  rfl

/-- The canonical original coefficient map is fixed inside the same generated algebra. -/
theorem characterConjugationNormalEquiv_fix_coefficient (α : NormalAction G M)
    (χ : PontryaginDual G) (x : M) :
    characterConjugationNormalEquiv μ α χ (crossedProductCoefficient μ α x) =
      crossedProductCoefficient μ α x := by
  apply Subtype.ext
  rw [characterConjugationNormalEquiv_apply, crossedProductCoefficient_apply]
  exact characterMultiplier_fix_regularCoefficient μ α χ x

/-- The canonical original Haar implementer has Connes's exact positive-character scaling. -/
theorem characterConjugationNormalEquiv_scale_group (α : NormalAction G M)
    (χ : PontryaginDual G) (g : G) :
    characterConjugationNormalEquiv μ α χ (crossedProductGroupUnitary μ α g : crossedProductLp μ α) =
      ((χ g : Circle) : ℂ) • (crossedProductGroupUnitary μ α g : crossedProductLp μ α) := by
  apply Subtype.ext
  change (characterConjugationNormalEquiv μ α χ
    (crossedProductGroupUnitary μ α g : crossedProductLp μ α) : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      ((χ g : Circle) : ℂ) • ((crossedProductGroupUnitary μ α g : crossedProductLp μ α) :
        Lp H 2 μ →L[ℂ] Lp H 2 μ)
  rw [characterConjugationNormalEquiv_apply, crossedProductGroupUnitary_coe]
  exact characterMultiplier_scale_haarLeftRegular μ χ g

/-- The computed character conjugations form their actual normal automorphism group map. -/
def characterConjugationNormalHom (α : NormalAction G M) :
    PontryaginDual G →* NormalStarAlgEquiv (crossedProductLp μ α) (crossedProductLp μ α) where
  toFun := characterConjugationNormalEquiv μ α
  map_one' := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    apply Subtype.ext
    change (characterConjugationNormalEquiv μ α (1 : PontryaginDual G) x :
      Lp H 2 μ →L[ℂ] Lp H 2 μ) = (x : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    rw [characterConjugationNormalEquiv_apply]
    have hU := (characterMultiplierUnitaryHom (H := H) μ).map_one
    change characterMultiplierUnitary (H := H) μ (1 : PontryaginDual G) =
      (1 : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ)) at hU
    rw [hU]
    simp only [Submonoid.coe_one, star_one, one_mul, mul_one]
  map_mul' χ ψ := by
    apply NormalStarAlgEquiv.ext
    apply StarAlgEquiv.ext
    intro x
    apply Subtype.ext
    change (characterConjugationNormalEquiv μ α (χ * ψ) x : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      (characterConjugationNormalEquiv μ α χ (characterConjugationNormalEquiv μ α ψ x) :
        Lp H 2 μ →L[ℂ] Lp H 2 μ)
    simp only [characterConjugationNormalEquiv_apply]
    have hU := (characterMultiplierUnitaryHom (H := H) μ).map_mul χ ψ
    change characterMultiplierUnitary (H := H) μ (χ * ψ) =
      characterMultiplierUnitary (H := H) μ χ * characterMultiplierUnitary (H := H) μ ψ at hU
    rw [hU]
    simp only [Submonoid.coe_mul, star_mul, mul_assoc]

end

end NormalAction
end VonNeumannAlgebra
