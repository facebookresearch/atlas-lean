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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CompactSupport
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Actual unitary character multiplication on the original Haar L2 carrier

A continuous unit-modulus character multiplies the same original Lp H 2
representatives. Its inverse is multiplication by the inverse character;
the original pointwise norm gives an actual unitary group homomorphism.
The character convention is Connes's positive multiplication chi(s)xi(s).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ENNReal Topology InnerProductSpace

namespace MeasureTheory
namespace HaarL2

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G)
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual original L2 operator multiplying by the continuous character at every coordinate. -/
def characterMultiplier (χ : PontryaginDual G) : Lp H 2 μ →L[ℂ] Lp H 2 μ := by
  let φ : G → ℂ := fun s => ((χ s : Circle) : ℂ)
  have hφcont : Continuous φ := continuous_subtype_val.comp (map_continuous χ)
  have hφ : MemLp φ ∞ μ := memLp_top_of_bound hφcont.aestronglyMeasurable 1
    (Eventually.of_forall fun s => (Circle.norm_coe (χ s)).le)
  have hF (ξ : Lp H 2 μ) : MemLp (φ • (ξ : G → H)) 2 μ :=
    hφ.smul (Lp.memLp ξ) (p := ∞) (q := 2) (r := 2)
  let F (ξ : Lp H 2 μ) : Lp H 2 μ := (hF ξ).toLp (φ • (ξ : G → H))
  have hFae (ξ : Lp H 2 μ) : F ξ =ᵐ[μ] fun s => φ s • ξ s := (hF ξ).coeFn_toLp
  let F₀ : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ :=
    { toFun := F
      map_add' ξ η := by
        apply Lp.ext
        filter_upwards [hFae (ξ + η), hFae ξ, hFae η, Lp.coeFn_add ξ η,
          Lp.coeFn_add (F ξ) (F η)] with s h₁ h₂ h₃ h₄ h₅
        rw [h₁, h₅]
        change φ s • (ξ + η) s = F ξ s + F η s
        rw [h₂, h₃, h₄]
        change φ s • (ξ s + η s) = φ s • ξ s + φ s • η s
        exact smul_add _ _ _
      map_smul' c ξ := by
        apply Lp.ext
        filter_upwards [hFae (c • ξ), hFae ξ, Lp.coeFn_smul c ξ,
          Lp.coeFn_smul c (F ξ)] with s h₁ h₂ h₃ h₄
        rw [RingHom.id_apply, h₁, h₄]
        change φ s • (c • ξ) s = c • F ξ s
        rw [h₂, h₃]
        change φ s • (c • ξ s) = c • (φ s • ξ s)
        exact smul_comm _ _ _ }
  have hbound (ξ : Lp H 2 μ) : ‖F₀ ξ‖ ≤ 1 * ‖ξ‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hFae ξ] with s hs
    change ‖F ξ s‖ ≤ 1 * ‖ξ s‖
    rw [hs, norm_smul]
    change ‖((χ s : Circle) : ℂ)‖ * ‖ξ s‖ ≤ 1 * ‖ξ s‖
    rw [Circle.norm_coe]
  exact F₀.mkContinuous 1 hbound

/-- Character multiplication has its literal original coordinate values almost everywhere. -/
theorem characterMultiplier_ae_eq (χ : PontryaginDual G) (ξ : Lp H 2 μ) :
    characterMultiplier (H := H) μ χ ξ =ᵐ[μ] fun s : G => ((χ s : Circle) : ℂ) • ξ s := by
  let φ : G → ℂ := fun s => ((χ s : Circle) : ℂ)
  have hφcont : Continuous φ := continuous_subtype_val.comp (map_continuous χ)
  have hφ : MemLp φ ∞ μ := memLp_top_of_bound hφcont.aestronglyMeasurable 1
    (Eventually.of_forall fun s => (Circle.norm_coe (χ s)).le)
  have hproduct : MemLp (φ • (ξ : G → H)) 2 μ :=
    hφ.smul (Lp.memLp ξ) (p := ∞) (q := 2) (r := 2)
  change hproduct.toLp (φ • (ξ : G → H)) =ᵐ[μ] fun s : G => φ s • ξ s
  exact hproduct.coeFn_toLp

/-- Actual character multiplication preserves the original Haar L2 norm. -/
theorem characterMultiplier_norm (χ : PontryaginDual G) (ξ : Lp H 2 μ) :
    ‖characterMultiplier (H := H) μ χ ξ‖ = ‖ξ‖ := by
  have h : ∀ᵐ s ∂μ, ‖characterMultiplier (H := H) μ χ ξ s‖ = ‖ξ s‖ := by
    filter_upwards [characterMultiplier_ae_eq μ χ ξ] with s hs
    rw [hs, norm_smul, Circle.norm_coe, one_mul]
  apply le_antisymm
  · exact Lp.norm_le_norm_of_ae_le (h.mono fun s hs => hs.le)
  · exact Lp.norm_le_norm_of_ae_le (h.mono fun s hs => hs.symm.le)

/-- The identity character is the identity operator on the same actual L2 space. -/
theorem characterMultiplier_one : characterMultiplier (H := H) μ (1 : PontryaginDual G) = 1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [characterMultiplier_ae_eq μ (1 : PontryaginDual G) ξ] with s hs
  change characterMultiplier (H := H) μ (1 : PontryaginDual G) ξ s = ξ s
  rw [hs, PontryaginDual.one_apply, Circle.coe_one, one_smul]

/-- Character products are actual composition products of their original L2 multipliers. -/
theorem characterMultiplier_mul (χ ψ : PontryaginDual G) :
    characterMultiplier (H := H) μ (χ * ψ) = characterMultiplier μ χ * characterMultiplier μ ψ := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [characterMultiplier_ae_eq μ (χ * ψ) ξ,
    characterMultiplier_ae_eq μ χ (characterMultiplier μ ψ ξ),
    characterMultiplier_ae_eq μ ψ ξ] with s h₁ h₂ h₃
  change characterMultiplier (H := H) μ (χ * ψ) ξ s =
    characterMultiplier μ χ (characterMultiplier μ ψ ξ) s
  rw [h₁, h₂, h₃]
  change (((χ s * ψ s : Circle) : ℂ) • ξ s) =
    ((χ s : Circle) : ℂ) • (((ψ s : Circle) : ℂ) • ξ s)
  rw [Circle.coe_mul, mul_smul]

variable [CompleteSpace H]

/-- The actual character multiplication unitary, with inverse given by the inverse character. -/
def characterMultiplierUnitary (χ : PontryaginDual G) : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  let I : Lp H 2 μ →ₗᵢ[ℂ] Lp H 2 μ :=
    { toLinearMap := (characterMultiplier μ χ).toLinearMap
      norm_map' := characterMultiplier_norm μ χ }
  have hsurj : Function.Surjective I := by
    intro ξ
    refine ⟨characterMultiplier μ χ⁻¹ ξ, ?_⟩
    change ((characterMultiplier (H := H) μ χ * characterMultiplier (H := H) μ χ⁻¹) :
      Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ = ξ
    rw [← characterMultiplier_mul, mul_inv_cancel, characterMultiplier_one]
    rfl
  exact Unitary.linearIsometryEquiv.symm (LinearIsometryEquiv.ofSurjective I hsurj)

/-- The actual character unitary retains the same original a.e. scalar multiplication formula. -/
theorem characterMultiplierUnitary_ae_eq (χ : PontryaginDual G) (ξ : Lp H 2 μ) :
    (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) ξ =ᵐ[μ]
      fun s : G => ((χ s : Circle) : ℂ) • ξ s := by
  change characterMultiplier (H := H) μ χ ξ =ᵐ[μ] _
  exact characterMultiplier_ae_eq μ χ ξ

/-- The original character multipliers form their actual unitary group homomorphism. -/
def characterMultiplierUnitaryHom : PontryaginDual G →* unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun := characterMultiplierUnitary μ
  map_one' := by
    apply Subtype.ext
    change characterMultiplier (H := H) μ (1 : PontryaginDual G) = 1
    exact characterMultiplier_one μ
  map_mul' χ ψ := by
    apply Subtype.ext
    change characterMultiplier (H := H) μ (χ * ψ) =
      characterMultiplier μ χ * characterMultiplier μ ψ
    exact characterMultiplier_mul μ χ ψ

end

end HaarL2
end MeasureTheory
