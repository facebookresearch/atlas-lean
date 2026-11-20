/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Walls.gc25resummation
import Code.Walls.gc9core
import Code.Walls.gc15core
import Code.Walls.ghc_urselleqgap

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
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap
open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]















theorem gc28_delta_eq_Z0sq_cov3 (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc25_nativeAllConnMass G β h o x y
      = (gc15_Z0 G β h) ^ 2 * cov3sym G β h o s(x, y) := by
  have h9 := gc9_eq20_perBond_cov3 G β h o x y hox hoy hxy
  have hZ : gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) = (gc15_Z0 G β h) ^ 2 := rfl
  unfold gc25_nativeAllConnMass
  rw [← h9, hZ]
















theorem gc28_nativeResummation_forces_ursell_proportional (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc25_NativeResummation G β h o x y) :
    gc15_Z0 G β h * eg_ursell3 G β h o x y = -2 * cov3sym G β h o s(x, y) := by
  have hsum := gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy
  have hδ := gc28_delta_eq_Z0sq_cov3 G β h o x y hox hoy hxy
  unfold gc25_NativeResummation at hres
  rw [← hsum, hδ] at hres
  
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ2 : (gc15_Z0 G β h) ^ 2 ≠ 0 := by positivity
  
  have key : (gc15_Z0 G β h) ^ 2
      * (gc15_Z0 G β h * eg_ursell3 G β h o x y - (-2 * cov3sym G β h o s(x, y))) = 0 := by
    ring_nf; ring_nf at hres; linarith [hres]
  have := (mul_eq_zero.mp key).resolve_left hZ2
  linarith [this]












theorem gc28_nativeResummation_forces_rigid (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc25_NativeResummation G β h o x y) :
    (gc15_Z0 G β h + 2) * cov3sym G β h o s(x, y)
      = gc15_Z0 G β h * ghsBoundSym G β h o s(x, y) := by
  have hprop := gc28_nativeResummation_forces_ursell_proportional G β h o x y hox hoy hxy hres
  have hu : eg_ursell3 G β h o x y = cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y) := by
    rw [← ghc_ursellEqGap]
  rw [hu] at hprop
  
  ring_nf; ring_nf at hprop; linarith [hprop]























theorem gc28_native_ursell_decomp (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
    ∑ m ∈ M, hnw_gap G β J m A o x y
      = (∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A)
        - 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) :=
  hnw_inclusion_exclusion_decomp G β J M hnd A hm hox hoy hxy hcoh






theorem gc28_native_closure_of_hdom (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m A o x y :=
  hnw_closure_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom













theorem gc28_proportional_closes_ghs (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hprop : gc15_Z0 G β h * eg_ursell3 G β h o x y = -2 * cov3sym G β h o s(x, y)) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hcov : 0 ≤ cov3sym G β h o s(x, y) := gc9_cov3_nonneg_of_eq20 G β h hβ hh o x y hox hoy hxy
  nlinarith [hprop, hZ, hcov]







theorem gc28_cov3_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    0 ≤ cov3sym G β h o s(x, y) :=
  gc9_cov3_nonneg_of_eq20 G β h hβ hh o x y hox hoy hxy

end StatMech.Walls
