/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.CrystalPacking

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for crystal structures and packing

Numeric checks of the atomic packing factor identities against reference
decimals, checks that the domain-safe physical APIs evaluate through the raw
helpers, plus `#print axioms` audits for every public declaration of
`PhyslibExt.CondensedMatter.CrystalPacking`.
-/

@[expose] public section

open CondensedMatter.CrystalPacking

/-- SC packing factor `π/6 ≈ 0.52360`. -/
example : |atomicPackingFactorRaw 1 1 8 - 0.52360| < 0.001 := by
  have hid : atomicPackingFactorRaw 1 1 8 = Real.pi / 6 :=
    apf_simpleCubic 1 2 8 (by norm_num) (by norm_num) (by norm_num)
  rw [hid]
  have hpi1 := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  rw [abs_lt]
  constructor <;> linarith

/-- BCC packing factor `π√3/8 ≈ 0.68017`. -/
example : |atomicPackingFactorRaw 2 (Real.sqrt 3) 64 - 0.68017| < 0.001 := by
  have hs3pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
  have hid : atomicPackingFactorRaw 2 (Real.sqrt 3) 64 =
      Real.pi * Real.sqrt 3 / 8 :=
    apf_bcc (Real.sqrt 3) 4 64 hs3pos (by ring) (by norm_num)
  rw [hid]
  have hpi1 := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  have hb := sqrt3_bounds
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h31416 : (0 : ℝ) < 3.1416 := by norm_num
  have h1731 : (0 : ℝ) < 1.731 := by norm_num
  have e1 : Real.pi * Real.sqrt 3 < 3.1416 * Real.sqrt 3 :=
    mul_lt_mul_of_pos_right hpi2 hs3pos
  have e2 : (3.1416 : ℝ) * Real.sqrt 3 < 3.1416 * 1.733 :=
    mul_lt_mul_of_pos_left hb.2 h31416
  have e3 : (3.1415 : ℝ) * 1.731 < Real.pi * 1.731 :=
    mul_lt_mul_of_pos_right hpi1 h1731
  have e4 : Real.pi * (1.731 : ℝ) < Real.pi * Real.sqrt 3 :=
    mul_lt_mul_of_pos_left hb.1 hpi_pos
  rw [abs_lt]
  constructor <;> linarith [e1, e2, e3, e4]

/-- FCC packing factor `π/(3√2) ≈ 0.74048`. -/
example : |atomicPackingFactorRaw 4 (Real.sqrt 2) 64 - 0.74048| < 0.001 := by
  have hs2pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  have hid : atomicPackingFactorRaw 4 (Real.sqrt 2) 64 =
      Real.pi / (3 * Real.sqrt 2) :=
    apf_fcc (Real.sqrt 2) 4 64 hs2pos (by ring) (by norm_num)
  rw [hid]
  have hpi1 := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  have hb := sqrt2_bounds
  have h3s2 : (0 : ℝ) < 3 * Real.sqrt 2 := by linarith [hs2pos]
  have hlo : (0.73948 : ℝ) < Real.pi / (3 * Real.sqrt 2) := by
    rw [lt_div_iff₀ h3s2]
    linarith [hpi1, hb.2]
  have hhi : Real.pi / (3 * Real.sqrt 2) < 0.74148 := by
    rw [div_lt_iff₀ h3s2]
    linarith [hpi2, hb.1]
  rw [abs_lt]
  constructor <;> linarith [hlo, hhi]

/-- Diamond packing factor `π√3/16 ≈ 0.34009`. -/
example : |atomicPackingFactorRaw 8 (Real.sqrt 3) 512 - 0.34009| < 0.001 := by
  have hs3pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
  have hid : atomicPackingFactorRaw 8 (Real.sqrt 3) 512 =
      Real.pi * Real.sqrt 3 / 16 :=
    apf_diamond (Real.sqrt 3) 8 512 hs3pos (by ring) (by norm_num)
  rw [hid]
  have hpi1 := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  have hb := sqrt3_bounds
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h31416 : (0 : ℝ) < 3.1416 := by norm_num
  have h31416 : (0 : ℝ) < 3.1416 := by norm_num
  have h1731 : (0 : ℝ) < 1.731 := by norm_num
  have e1 : Real.pi * Real.sqrt 3 < 3.1416 * Real.sqrt 3 :=
    mul_lt_mul_of_pos_right hpi2 hs3pos
  have e2 : (3.1416 : ℝ) * Real.sqrt 3 < 3.1416 * 1.733 :=
    mul_lt_mul_of_pos_left hb.2 h31416
  have e3 : (3.1415 : ℝ) * 1.731 < Real.pi * 1.731 :=
    mul_lt_mul_of_pos_right hpi1 h1731
  have e4 : Real.pi * (1.731 : ℝ) < Real.pi * Real.sqrt 3 :=
    mul_lt_mul_of_pos_left hb.1 hpi_pos
  rw [abs_lt]
  constructor <;> linarith [e1, e2, e3, e4]

/-- The physical packing factor on its domain evaluates through the raw helper:
SC packing factor `π/6`. -/
example : atomicPackingFactor 1 1 8 one_pos (by norm_num) = Real.pi / 6 := by
  rw [atomicPackingFactor_eq_raw]
  exact apf_simpleCubic 1 2 8 (by norm_num) (by norm_num) (by norm_num)

/-- The physical density on its domain evaluates through the raw helper: the
MAT-C1 fixture. -/
example :
    |theoreticalDensity 4 64 (64e-24) 6.02214076e23 (by norm_num) (by norm_num)
        (by norm_num) - 6.64216| < 0.001 := by
  rw [theoreticalDensity_eq_raw]
  exact density_mat_c1 _ rfl

#print axioms atomicPackingFactorRaw
#print axioms atomicPackingFactor
#print axioms atomicPackingFactor_eq_raw
#print axioms theoreticalDensityRaw
#print axioms theoreticalDensity
#print axioms theoreticalDensity_eq_raw
#print axioms sqrt2_bounds
#print axioms sqrt3_bounds
#print axioms sqrt32_bounds
#print axioms apf_simpleCubic
#print axioms apf_bcc
#print axioms apf_fcc
#print axioms apf_hcp
#print axioms apf_diamond
#print axioms theoreticalDensityRaw_eq
#print axioms angstrom_cubed_to_cm_cubed
#print axioms density_mat_c1
#print axioms density_unit_conversion
#print axioms equilateral_centroid_sq
#print axioms equilateral_centroid_dist
#print axioms tetrahedron_height
#print axioms hcp_ideal_ratio
#print axioms fcc_octahedral_hole
#print axioms fcc_tetrahedral_hole
#print axioms radiusRatio_eq_two_div_sqrt_three_sub_one
#print axioms radiusRatio_eq_sqrt_three_halves_sub_one
#print axioms radiusRatio_eq_sqrt_two_sub_one
#print axioms radiusRatio_eq_sqrt_three_sub_one
