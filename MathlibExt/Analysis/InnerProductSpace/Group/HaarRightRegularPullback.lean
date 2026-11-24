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

public import MathlibExt.MeasureTheory.Group.HaarRightTranslation
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.CovariantRepresentation

/-!
# Normalized right pullback for a regular Haar measure

The existing modular character gives the actual right-translation
pushforward factor. The normalized pullback acts on the original Haar
`L²` carrier and has the same norm as its input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace StronglyContinuousUnitaryRepresentation

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The prescribed modularly normalized right translate belongs to the same Haar `L²`. -/
theorem haarRightPullback_memLp (g : G) (ξ : Lp H 2 μ) :
    MemLp (fun x : G => (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • ξ (x * g)) 2 μ := by
  have hpres : MeasurePreserving (fun x : G => x * g) μ
      (Measure.modularCharacter g • μ) :=
    ⟨measurable_id.mul_const g, Measure.map_right_mul_modular μ g⟩
  have hscaled := (Lp.memLp ξ).smul_measure_nnreal (c := Measure.modularCharacter g)
  exact (hscaled.comp_measurePreserving hpres).const_smul _

/-- The actual normalized right pullback on the original `L²` carrier. -/
def haarRightPullback (g : G) (ξ : Lp H 2 μ) : Lp H 2 μ :=
  (haarRightPullback_memLp μ g ξ).toLp
    (fun x : G => (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • ξ (x * g))

/-- The original Haar representatives have the exact modular right-translation formula. -/
theorem haarRightPullback_ae_eq (g : G) (ξ : Lp H 2 μ) :
    haarRightPullback μ g ξ =ᵐ[μ]
      fun x : G => (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • ξ (x * g) :=
  MemLp.coeFn_toLp (haarRightPullback_memLp μ g ξ)

/-- The exact modular weight makes right pullback norm preserving. -/
theorem norm_haarRightPullback (g : G) (ξ : Lp H 2 μ) :
    ‖haarRightPullback μ g ξ‖ = ‖ξ‖ := by
  let c : ℝ≥0 := Measure.modularCharacter g
  let r : ℝ := (c : ℝ) ^ (-(2 : ℝ)⁻¹)
  have hcpos : 0 < c := Measure.modularCharacterFun_pos g
  have hcR : 0 < (c : ℝ) := hcpos
  have hrpos : 0 < r := Real.rpow_pos_of_pos hcR _
  have hweight : r * (c : ℝ) ^ (2 : ℝ)⁻¹ = 1 := by
    dsimp only [r]
    rw [← Real.rpow_add hcR]
    simp
  have hpres : MeasurePreserving (fun x : G => x * g) μ (c • μ) :=
    ⟨measurable_id.mul_const g, Measure.map_right_mul_modular μ g⟩
  have hscaled := (Lp.memLp ξ).smul_measure_nnreal (c := c)
  change ‖(haarRightPullback_memLp μ g ξ).toLp
    (r • ((ξ : G → H) ∘ fun x : G => x * g))‖ = ‖ξ‖
  rw [Lp.norm_toLp, eLpNorm_const_smul,
    eLpNorm_comp_measurePreserving hscaled.aestronglyMeasurable hpres,
    eLpNorm_smul_measure_of_ne_zero' hcpos.ne']
  simp only [ENNReal.smul_def, smul_eq_mul]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofNat, NNReal.coe_rpow, toReal_enorm]
  rw [Real.norm_eq_abs, abs_of_pos hrpos, ← mul_assoc, hweight, one_mul]
  rfl

end

end StronglyContinuousUnitaryRepresentation
