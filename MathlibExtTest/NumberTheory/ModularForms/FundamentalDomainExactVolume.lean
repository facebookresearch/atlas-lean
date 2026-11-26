/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.FundamentalDomainExactVolume

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups Modular Pointwise NNReal ENNReal

/-- Consumer with the original statement: the volume of `𝒟`. -/
theorem exactSource : volume 𝒟 = ENNReal.ofReal (Real.pi / 3) :=
  ModularGroup.volume_fd_eq

/-- Unfolding the lower arc at the centre and a point of the region. -/
example : ModularGroup.lowerArc 0 = 1 ∧ (0, 1) ∈ ModularGroup.fundamentalRegion := by
  refine ⟨ModularGroup.lowerArc_zero, ?_⟩
  rw [ModularGroup.mem_fundamentalRegion]
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  simp [ModularGroup.lowerArc]

/-- A point below the arc is outside, so the arc bound matters. -/
example : (0, 0) ∉ ModularGroup.fundamentalRegion := by
  rw [ModularGroup.mem_fundamentalRegion]
  push Not
  intro _
  simp [ModularGroup.lowerArc]

/-- Nontrivial consequences: finite positive volume and its real value. -/
example : (volume 𝒟).toReal = Real.pi / 3 ∧ volume 𝒟 ≠ 0 ∧ volume 𝒟 < ⊤ :=
  ⟨ModularGroup.volume_fd_toReal, ModularGroup.volume_fd_ne_zero,
    ModularGroup.volume_fd_lt_top⟩

example : ∫ x in (-(1 / 2) : ℝ)..(1 / 2), (Real.sqrt (1 - x ^ 2))⁻¹ = Real.pi / 3 :=
  integral_inv_sqrt_one_sub_sq
