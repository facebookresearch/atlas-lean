/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Code.Walls.gc38sharp

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedVariables false
set_option linter.style.openClassical false

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]







theorem gc95b_ursell3_eq_U4_add_triple (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y
      = gc37_U4 G β h o x y + 2 * gc37_triple G β h o x y :=
  gc37_ursell3_eq_U4_add_triple G β h o x y




theorem gc95b_U4_nonpos (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc37_U4 G β h o x y ≤ 0 :=
  gc38_U4_nonpos_unconditional G β h hβ hh o x y hox hoy hxy


theorem gc95b_triple_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ gc37_triple G β h o x y :=
  gc37_triple_nonneg G β h hβ hh o x y








theorem gc95b_U4_nonpos_gives_only_ursell_le_two_triple (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 2 * gc37_triple G β h o x y := by
  rw [gc95b_ursell3_eq_U4_add_triple]
  have hU4 := gc95b_U4_nonpos G β h hβ hh o x y hox hoy hxy
  linarith







theorem gc95b_ghs_iff_U4_le_neg_two_triple (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y ≤ 0
      ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y :=
  gc37_ursell3_nonpos_iff_sharp G β h o x y





theorem gc95b_ghs_of_sharp_residue (β h : ℝ) (o x y : V)
    (hres : gc38_SharpGHSResidue G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc38_ursell3_nonpos_of_sharpResidue G β h o x y hres










theorem gc95b_U4_route_insufficient (β h : ℝ) (o x y : V)
    (hU4_le : gc37_U4 G β h o x y ≤ 0)
    (htriple_pos : 0 < gc37_triple G β h o x y)
    (hU4_gt : -2 * gc37_triple G β h o x y < gc37_U4 G β h o x y) :
    ¬ (eg_ursell3 G β h o x y ≤ 0) := by
  rw [gc95b_ghs_iff_U4_le_neg_two_triple]
  
  exact not_le.mpr hU4_gt






theorem gc95b_boundary_U4_suffices_only_at_triple_zero (β h : ℝ) (o x y : V)
    (htriple_zero : gc37_triple G β h o x y = 0)
    (hU4_le : gc37_U4 G β h o x y ≤ 0) :
    eg_ursell3 G β h o x y ≤ 0 := by
  rw [gc95b_ursell3_eq_U4_add_triple, htriple_zero]
  linarith
















theorem gc95b_downstream_audit (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (eg_ursell3 G β h o x y = gc37_U4 G β h o x y + 2 * gc37_triple G β h o x y)
      ∧ (0 ≤ gc37_triple G β h o x y)
      ∧ (gc37_U4 G β h o x y ≤ 0)
      ∧ (eg_ursell3 G β h o x y ≤ 0
          ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y)
      ∧ (eg_ursell3 G β h o x y ≤ 2 * gc37_triple G β h o x y) := by
  refine ⟨gc95b_ursell3_eq_U4_add_triple G β h o x y,
    gc95b_triple_nonneg G β h hβ hh o x y,
    gc95b_U4_nonpos G β h hβ hh o x y hox hoy hxy,
    gc95b_ghs_iff_U4_le_neg_two_triple G β h o x y,
    gc95b_U4_nonpos_gives_only_ursell_le_two_triple G β h hβ hh o x y hox hoy hxy⟩

end StatMech.Walls
