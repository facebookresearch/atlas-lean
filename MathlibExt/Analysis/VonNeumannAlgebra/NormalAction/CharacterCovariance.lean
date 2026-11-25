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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CharacterMultiplierContinuous
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.RegularCoefficientAlgebra

/-!
# The original character conjugation equations on Haar L2

Connes's actual positive character multipliers fix the original coefficient
operators and multiply the original Haar left implementer by chi(g).
These are the exact generator equations needed by the later restricted
normal dual action; its invariance, normality and predual orbit fields remain
separate construction prerequisites.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.HaarL2 Filter
open scoped ENNReal Topology InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra
namespace NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.Regular]

/-- Actual positive-character conjugation fixes every original regular coefficient operator. -/
theorem characterMultiplier_fix_regularCoefficient (α : NormalAction G M)
    (χ : PontryaginDual G) (x : M) :
    (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) *
      regularCoefficient μ α x * star (characterMultiplierUnitary (H := H) μ χ :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) = regularCoefficient μ α x := by
  have hstar : star (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      (characterMultiplierUnitary (H := H) μ χ⁻¹ : Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
    congrArg (fun U : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) => U.val)
      ((characterMultiplierUnitaryHom (H := H) μ).map_inv χ).symm
  rw [hstar]
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [characterMultiplier_ae_eq μ χ
      (regularCoefficient μ α x (characterMultiplier μ χ⁻¹ ξ)),
    regularCoefficient_ae_eq μ α x (characterMultiplier μ χ⁻¹ ξ),
    characterMultiplier_ae_eq μ χ⁻¹ ξ, regularCoefficient_ae_eq μ α x ξ] with s h₁ h₂ h₃ h₄
  change characterMultiplier (H := H) μ χ
    (regularCoefficient μ α x (characterMultiplier μ χ⁻¹ ξ)) s = regularCoefficient μ α x ξ s
  rw [h₁, h₂, h₃, h₄, map_smul, ← mul_smul]
  have hchar : ((χ s : Circle) : ℂ) * ((χ⁻¹ s : Circle) : ℂ) = 1 := by
    change ((χ s : Circle) : ℂ) * (((χ s)⁻¹ : Circle) : ℂ) = 1
    rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  rw [hchar, one_smul]

variable [μ.IsHaarMeasure]

/-- Actual positive-character conjugation gives Connes's exact chi(g) scaling of the Haar left implementer. -/
theorem characterMultiplier_scale_haarLeftRegular (χ : PontryaginDual G) (g : G) :
    (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) *
      (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) *
      star (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
        ((χ g : Circle) : ℂ) •
          (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
            Lp H 2 μ →L[ℂ] Lp H 2 μ) := by
  have hstar : star (characterMultiplierUnitary (H := H) μ χ : Lp H 2 μ →L[ℂ] Lp H 2 μ) =
      (characterMultiplierUnitary (H := H) μ χ⁻¹ : Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
    congrArg (fun U : unitary (Lp H 2 μ →L[ℂ] Lp H 2 μ) => U.val)
      ((characterMultiplierUnitaryHom (H := H) μ).map_inv χ).symm
  rw [hstar]
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  let L : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
    StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g
  have houter := characterMultiplier_ae_eq μ χ (L (characterMultiplier μ χ⁻¹ ξ))
  have hleft := StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G μ H g
    (characterMultiplier μ χ⁻¹ ξ)
  have hinner := characterMultiplier_ae_eq μ χ⁻¹ ξ
  have hpres : MeasurePreserving (fun s : G => g⁻¹ * s) μ μ := measurePreserving_smul g⁻¹ μ
  have hquasi : QuasiMeasurePreserving (fun s : G => g⁻¹ * s) μ μ :=
    ⟨hpres.measurable.aemeasurable, by rw [hpres.map_eq]⟩
  have hinner' := hquasi.ae_eq_comp hinner
  filter_upwards [houter, hleft, hinner', Lp.coeFn_smul (((χ g : Circle) : ℂ)) (L ξ),
    StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G μ H g ξ] with s h₁ h₂ h₃ h₄ h₅
  change characterMultiplier (H := H) μ χ (L (characterMultiplier μ χ⁻¹ ξ)) s =
    (((χ g : Circle) : ℂ) • L ξ) s
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₂, h₃, h₄]
  change ((χ s : Circle) : ℂ) • (((χ⁻¹ (g⁻¹ * s) : Circle) : ℂ) • ξ (g⁻¹ * s)) =
    ((χ g : Circle) : ℂ) • L ξ s
  rw [h₅, ← mul_smul]
  have hchar : ((χ s : Circle) : ℂ) * ((χ⁻¹ (g⁻¹ * s) : Circle) : ℂ) =
      ((χ g : Circle) : ℂ) := by
    have hcircle : χ s * χ⁻¹ (g⁻¹ * s) = χ g := by
      change χ s * (χ (g⁻¹ * s))⁻¹ = χ g
      rw [map_mul, map_inv, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    simpa only [Circle.coe_mul] using congrArg (fun z : Circle => (z : ℂ)) hcircle
  rw [hchar]

end

end NormalAction
end VonNeumannAlgebra
