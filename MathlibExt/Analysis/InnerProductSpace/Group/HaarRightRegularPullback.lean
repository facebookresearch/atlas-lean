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
# Modularly normalized Haar right pullback

For a locally compact Borel topological group and regular Haar measure, right translation has
measure factor `Δ(g)`. Its normalized L² pullback is `R_gξ(x)=Δ(g)^(-1/2) • ξ(xg)`.

This function is square integrable and preserves the L² norm. The coefficient inner-product
space may be incomplete, and no commutativity of the group is required.
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

/-- **Square integrability of the modularly normalized right translate.** Let `G` be a locally
compact topological group with its Borel structure, `μ` a regular Haar measure and `H` a
complex normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. for `g∈G`, `ξ∈Lp H
2 μ`, `x ↦ w(g) • ξ(xg)` belongs to `MemLp 2 μ`. -/
theorem haarRightPullback_memLp (g : G) (ξ : Lp H 2 μ) :
    MemLp (fun x : G => (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • ξ (x * g)) 2 μ := by
  have hpres : MeasurePreserving (fun x : G => x * g) μ
      (Measure.modularCharacter g • μ) :=
    ⟨measurable_id.mul_const g, Measure.map_right_mul_modular μ g⟩
  have hscaled := (Lp.memLp ξ).smul_measure_nnreal (c := Measure.modularCharacter g)
  exact (hscaled.comp_measurePreserving hpres).const_smul _

/-- **Normalized right Haar pullback as an L² class.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular Haar measure and `H` a complex
normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. `haarRightPullback
μ g ξ=R_gξ` is the class of the normalized right-translate function. -/
def haarRightPullback (g : G) (ξ : Lp H 2 μ) : Lp H 2 μ :=
  (haarRightPullback_memLp μ g ξ).toLp
    (fun x : G => (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • ξ (x * g))

/-- **Almost-everywhere normalized right Haar coordinates.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular Haar measure and `H` a complex
normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. `haarRightPullback
μ g ξ =ᵐ[μ] (x ↦ Δ(g)^(-1/2) • ξ(xg))`. -/
theorem haarRightPullback_ae_eq (g : G) (ξ : Lp H 2 μ) :
    haarRightPullback μ g ξ =ᵐ[μ]
      fun x : G => (Measure.modularCharacter g : ℝ) ^ (-(2 : ℝ)⁻¹) • ξ (x * g) :=
  MemLp.coeFn_toLp (haarRightPullback_memLp μ g ξ)

/-- **Norm preservation of normalized right Haar pullback.** Let `G` be a locally compact
topological group with its Borel structure, `μ` a regular Haar measure and `H` a complex
normed inner-product space, possibly incomplete. Put `w(g)=Δ(g)^(-1/2)` for
`Δ=Measure.modularCharacter` and `R_gξ(x)=w(g) • ξ(xg)` on `Lp H 2 μ`. for `g∈G`, `ξ∈Lp H
2 μ`, `‖R_gξ‖=‖ξ‖`. -/
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
