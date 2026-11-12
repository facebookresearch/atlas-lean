/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib
import Code.Walls.gc25resummation
import Code.Walls.gc37hdom
import Code.Walls.gc80bookroute
import Code.Walls.FaithfulnessAudit

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
















private noncomputable def cs81 (β h : ℝ) (A : Finset (Option V)) : ℝ :=
  currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) A







noncomputable def gc81_natRes_residual (β h : ℝ) (o x y : V) : ℝ :=
  (gc15_Z0 G β h + 2) * gc25_nativeAllConnMass G β h o x y
    - gc15_Z0 G β h * (cs81 G β h {some o, some x} * cs81 G β h {some y, none})
    - gc15_Z0 G β h * (cs81 G β h {some o, some y} * cs81 G β h {some x, none})
    + 2 * (cs81 G β h {some o, none} * cs81 G β h {some x, none} * cs81 G β h {some y, none})






theorem gc81_natRes_iff_residualZero (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc25_NativeResummation G β h o x y ↔ gc81_natRes_residual G β h o x y = 0 := by
  unfold gc25_NativeResummation gc81_natRes_residual cs81
  rw [gc25_threeGap_sum_decomp G β h o x y hox hoy hxy]
  constructor
  · intro h1; linarith [h1]
  · intro h1; linarith [h1]




















noncomputable def gc81_grahamAllConnMass (β h : ℝ) (o x y : V) : ℝ :=
  - (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y / 2






theorem gc81_grahamResummation (β h : ℝ) (o x y : V) :
    (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = -2 * gc81_grahamAllConnMass G β h o x y := by
  unfold gc81_grahamAllConnMass; ring





theorem gc81_ursell_nonpos_iff_grahamMass_nonneg (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y ≤ 0 ↔ 0 ≤ gc81_grahamAllConnMass G β h o x y := by
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ3 : 0 < (gc15_Z0 G β h) ^ 3 := pow_pos hZ 3
  unfold gc81_grahamAllConnMass
  constructor
  · intro hu
    have : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hZ3) hu
    nlinarith [this]
  · intro hd
    nlinarith [hd, hZ3]












theorem gc81_grahamMass_sub_leadingGap (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc81_grahamAllConnMass G β h o x y - gc25_nativeAllConnMass G β h o x y
      = - gc81_natRes_residual G β h o x y / 2 := by
  have hsum := gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy
  have hdecomp := gc25_threeGap_sum_decomp G β h o x y hox hoy hxy
  
  have hpoly : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = gc15_Z0 G β h * gc25_nativeAllConnMass G β h o x y
        - gc15_Z0 G β h * cs81 G β h {some o, some x} * cs81 G β h {some y, none}
        - gc15_Z0 G β h * cs81 G β h {some o, some y} * cs81 G β h {some x, none}
        + 2 * (cs81 G β h {some o, none} * cs81 G β h {some x, none}
            * cs81 G β h {some y, none}) := by
    unfold cs81
    rw [hsum, hdecomp]
  unfold gc81_grahamAllConnMass gc81_natRes_residual
  linear_combination (- hpoly / 2)






theorem gc81_grahamMass_eq_gap_iff (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc81_grahamAllConnMass G β h o x y = gc25_nativeAllConnMass G β h o x y
      ↔ gc25_NativeResummation G β h o x y := by
  rw [gc81_natRes_iff_residualZero G β h o x y hox hoy hxy]
  have hsub := gc81_grahamMass_sub_leadingGap G β h o x y hox hoy hxy
  constructor
  · intro heq
    have : gc81_grahamAllConnMass G β h o x y - gc25_nativeAllConnMass G β h o x y = 0 := by
      rw [heq]; ring
    rw [hsub] at this; linarith [this]
  · intro hR
    have : gc81_grahamAllConnMass G β h o x y - gc25_nativeAllConnMass G β h o x y = 0 := by
      rw [hsub, hR]; ring
    linarith [this]













theorem gc81_leadingGap_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ gc25_nativeAllConnMass G β h o x y :=
  gc25_nativeAllConnMass_nonneg G β h hβ hh o x y






















def gc81_absResidual (z s4 ao ax ay pxy pox poy : ℝ) : ℝ :=
  (z + 2) * (s4 * z - ao * pxy) - z * (pox * ay) - z * (poy * ax) + 2 * (ao * ax * ay)








theorem gc81_absResidual_nonzero :
    ∃ z s4 ao ax ay pxy pox poy : ℝ,
      gc81_absResidual z s4 ao ax ay pxy pox poy ≠ 0 := by
  refine ⟨1, 1, 0, 0, 0, 0, 0, 0, ?_⟩
  unfold gc81_absResidual; norm_num







theorem gc81_natRes_residual_eq_abs (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc81_natRes_residual G β h o x y
      = gc81_absResidual (gc15_Z0 G β h)
          (cs81 G β h {some o, some x, some y, none})
          (cs81 G β h {some o, none}) (cs81 G β h {some x, none}) (cs81 G β h {some y, none})
          (cs81 G β h {some x, some y}) (cs81 G β h {some o, some x}) (cs81 G β h {some o, some y}) := by
  have hgap := gc25_nativeAllConnMass_eq_gap G β h o x y hox hoy hxy
  unfold gc81_natRes_residual gc81_absResidual cs81
  rw [hgap]
  unfold gc15_Z0
  ring












theorem gc81_ghs_of_grahamMass_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hmass : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → 0 ≤ gc81_grahamAllConnMass G β h o x y) :
    GHSThreePointSym G β h o := by
  rw [ghc_ghsSym_iff_ursell_nonpos]
  intro x y he
  have hxy : x ≠ y := by rw [SimpleGraph.mem_edgeFinset] at he; exact G.ne_of_adj he
  by_cases hox : o = x
  · subst hox; exact ghc_ursell_nonpos_degenerate G β h hβ hh o y hxy
  · by_cases hoy : o = y
    · subst hoy; rw [ghc_ursell_swap]; exact ghc_ursell_nonpos_degenerate G β h hβ hh o x hox
    · exact (gc81_ursell_nonpos_iff_grahamMass_nonneg G β h o x y).mpr (hmass x y hox hoy hxy)




theorem gc81_aizenman_barsky_of_grahamMass_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o : V) (J : ℝ)
    (hmass : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → 0 ≤ gc81_grahamAllConnMass G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J
    (gc81_ghs_of_grahamMass_nonneg G β h hβ hh o hmass) hfactor












theorem gc81_grahamMass_at_zero (β : ℝ) (o x y : V) :
    gc81_grahamAllConnMass G β 0 o x y = 0 := by
  unfold gc81_grahamAllConnMass
  rw [fa_ghs_ursell3_h0_eq_zero G β o x y]; ring

























theorem gc81_graham_status (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc25_NativeResummation G β h o x y ↔ gc81_natRes_residual G β h o x y = 0)
    ∧ ((gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = -2 * gc81_grahamAllConnMass G β h o x y)
    ∧ (eg_ursell3 G β h o x y ≤ 0 ↔ 0 ≤ gc81_grahamAllConnMass G β h o x y) := by
  refine ⟨gc81_natRes_iff_residualZero G β h o x y hox hoy hxy,
    gc81_grahamResummation G β h o x y,
    gc81_ursell_nonpos_iff_grahamMass_nonneg G β h o x y⟩

end StatMech.Walls
