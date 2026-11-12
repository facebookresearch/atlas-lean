/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Walls.gc38sharp
import Code.Walls.gc20closure

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]













theorem ghx_eq24_U4_nonpos (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc37_U4 G β h o x y ≤ 0 :=
  gc38_U4_nonpos_unconditional G β h hβ hh o x y hox hoy hxy





theorem ghx_eq24_U4_nonpos_of_connRep (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hrep : gc37_U4a_connRep G β h o x y) :
    gc37_U4 G β h o x y ≤ 0 :=
  gc37_U4_nonpos_of_connRep G β h hβ hh o x y hrep











theorem ghx_ursell3_eq_U4_add_triple (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y = gc37_U4 G β h o x y + 2 * gc37_triple G β h o x y :=
  gc37_ursell3_eq_U4_add_triple G β h o x y



theorem ghx_triple_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ gc37_triple G β h o x y :=
  gc37_triple_nonneg G β h hβ hh o x y






theorem ghx_standardGHS_iff_sharpResidue (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y ≤ 0
      ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y :=
  gc37_ursell3_nonpos_iff_sharp G β h o x y





theorem ghx_eq24_gives_only_ursell_le_two_triple (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 2 * gc37_triple G β h o x y := by
  rw [ghx_ursell3_eq_U4_add_triple]
  have hU4 := ghx_eq24_U4_nonpos G β h hβ hh o x y hox hoy hxy
  linarith





theorem ghx_eq24_wrong_sign_obstruction :
    ∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧ 0 < a + 2 * b :=
  ⟨-1, 1, by norm_num, by norm_num, by norm_num⟩












theorem ghx_standardGHS_of_perConfig (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y) :
    GHSThreePointSym G β h o :=
  gc15_ghs_of_perConfig G β h hβ hh o hsign






theorem ghx_standardGHS_of_fiberRegime (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hreg : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
      gc20_FiberConnRegime G β h o x y m) :
    GHSThreePointSym G β h o :=
  gc20_ghs_of_trichotomy G β h hβ hh o hreg







theorem ghx_perConfig_implies_sharpResidue (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsign : gc15_PerConfigUrsellSign G β h o x y) :
    gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y :=
  (ghx_standardGHS_iff_sharpResidue G β h o x y).mp
    (gc15_ursell_nonpos_of_perConfig G β h o x y hox hoy hxy hsign)





theorem ghx_standardGHS_of_sharpResidue (β h : ℝ) (o x y : V)
    (hres : gc38_SharpGHSResidue G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc38_ursell3_nonpos_of_sharpResidue G β h o x y hres



















theorem ghx_eq24_insufficient_for_standard_ghs (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc37_U4 G β h o x y ≤ 0)
      ∧ (0 ≤ gc37_triple G β h o x y)
      ∧ (eg_ursell3 G β h o x y ≤ 0
          ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y)
      ∧ (eg_ursell3 G β h o x y ≤ 2 * gc37_triple G β h o x y)
      ∧ (∀ hres : gc38_SharpGHSResidue G β h o x y, eg_ursell3 G β h o x y ≤ 0) := by
  refine ⟨ghx_eq24_U4_nonpos G β h hβ hh o x y hox hoy hxy,
    ghx_triple_nonneg G β h hβ hh o x y,
    ghx_standardGHS_iff_sharpResidue G β h o x y,
    ghx_eq24_gives_only_ursell_le_two_triple G β h hβ hh o x y hox hoy hxy,
    fun hres => ghx_standardGHS_of_sharpResidue G β h o x y hres⟩





theorem ghx_standardGHS_iff_residualStep (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y ≤ 0 ↔ gc38_SharpGHSResidue G β h o x y := by
  rw [gc38_SharpGHSResidue]
  exact ghx_standardGHS_iff_sharpResidue G β h o x y











theorem ghx_sign_holds_at_h_zero (β : ℝ) (o x y : V) :
    eg_ursell3 G β 0 o x y ≤ 0 :=
  ghx_standardGHS_of_sharpResidue G β 0 o x y (gc38_sharpResidue_at_zero G β o x y)





theorem ghx_sign_holds_degenerate (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x y : V) (hxy : x ≠ y) :
    eg_ursell3 G β h x x y ≤ 0 :=
  ghc_ursell_nonpos_degenerate G β h hβ hh x y hxy







theorem ghx_eq24_route_insufficient_offBoundary (β h : ℝ) (o x y : V)
    (hU4_le : gc37_U4 G β h o x y ≤ 0)
    (htriple_pos : 0 < gc37_triple G β h o x y)
    (hU4_gt : -2 * gc37_triple G β h o x y < gc37_U4 G β h o x y) :
    ¬ (eg_ursell3 G β h o x y ≤ 0) := by
  rw [ghx_standardGHS_iff_sharpResidue]
  exact not_le.mpr hU4_gt

end StatMech.Walls
