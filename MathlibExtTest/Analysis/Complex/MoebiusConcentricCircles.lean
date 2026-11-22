/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.Analysis.Complex.MoebiusConcentricCircles

set_option autoImplicit false

open Metric
open scoped Pointwise

-- Two concentric circles: the theorem applies (with `g = 1` in the proof).
example : ∃ (g : GL (Fin 2) ℂ) (c : ℂ) (r' s' : ℝ), 0 < r' ∧ 0 < s' ∧
    g • ((↑) '' sphere (0 : ℂ) 1 : Set (OnePoint ℂ)) = ((↑) '' sphere c r' : Set (OnePoint ℂ)) ∧
    g • ((↑) '' sphere (0 : ℂ) 2 : Set (OnePoint ℂ)) = ((↑) '' sphere c s' : Set (OnePoint ℂ)) := by
  refine Complex.exists_smul_sphere_eq_concentric_of_disjoint one_pos two_pos ?_
  refine Set.disjoint_left.mpr fun z hz hz' ↦ ?_
  rw [mem_sphere_zero_iff_norm] at hz hz'
  linarith

-- Two external circles `|z| = 1` and `|z - 3| = 1`.
example : ∃ (g : GL (Fin 2) ℂ) (c : ℂ) (r' s' : ℝ), 0 < r' ∧ 0 < s' ∧
    g • ((↑) '' sphere (0 : ℂ) 1 : Set (OnePoint ℂ)) = ((↑) '' sphere c r' : Set (OnePoint ℂ)) ∧
    g • ((↑) '' sphere (3 : ℂ) 1 : Set (OnePoint ℂ)) = ((↑) '' sphere c s' : Set (OnePoint ℂ)) := by
  refine Complex.exists_smul_sphere_eq_concentric_of_disjoint one_pos one_pos ?_
  refine Set.disjoint_left.mpr fun z hz hz' ↦ ?_
  rw [mem_sphere_zero_iff_norm] at hz
  rw [mem_sphere_iff_norm] at hz'
  have h := norm_sub_le z (z - 3)
  rw [sub_sub_cancel, hz, hz'] at h
  norm_num at h

-- Two nested, non-concentric circles `|z| = 3` and `|z - 1| = 1`. Their images are distinct
-- concentric circles: equal radii would make the two original circles equal.
example : ∃ (c : ℂ) (r' s' : ℝ), 0 < r' ∧ 0 < s' ∧ r' ≠ s' ∧ ∃ g : GL (Fin 2) ℂ,
    g • ((↑) '' sphere (0 : ℂ) 3 : Set (OnePoint ℂ)) = ((↑) '' sphere c r' : Set (OnePoint ℂ)) ∧
    g • ((↑) '' sphere (1 : ℂ) 1 : Set (OnePoint ℂ)) = ((↑) '' sphere c s' : Set (OnePoint ℂ)) := by
  have hdisj : Disjoint (sphere (0 : ℂ) 3) (sphere 1 1) := by
    refine Set.disjoint_left.mpr fun z hz hz' ↦ ?_
    rw [mem_sphere_zero_iff_norm] at hz
    rw [mem_sphere_iff_norm] at hz'
    have h := norm_add_le (z - 1) 1
    rw [sub_add_cancel, hz, hz', norm_one] at h
    norm_num at h
  obtain ⟨g, c, r', s', hr', hs', hA, hB⟩ :=
    Complex.exists_smul_sphere_eq_concentric_of_disjoint (by norm_num) one_pos hdisj
  refine ⟨c, r', s', hr', hs', ?_, g, hA, hB⟩
  rintro rfl
  have h := congrArg (g⁻¹ • ·) (hA.trans hB.symm)
  simp only [inv_smul_smul] at h
  have h3 : (3 : ℂ) ∈ sphere (1 : ℂ) 1 := by
    rw [← OnePoint.coe_injective.image_injective h, mem_sphere_zero_iff_norm]
    norm_num
  rw [mem_sphere_iff_norm] at h3
  norm_num at h3

#print axioms Complex.exists_smul_sphere_eq_concentric_of_disjoint
