/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Walls.gc81grahamthreereplica
import Code.Walls.gc17core
import Code.Walls.gc10allconnforcing

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

















def gc82_allConn (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) : Prop :=
  gc10_allConn (endsM (withGhost G) m) (some o) (some x) (some y) (none) univ


noncomputable instance (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) :
    Decidable (gc82_allConn G β h o x y m) := Classical.dec _












def gc82_ThreeGapNonpos (β h : ℝ) (o x y : V) : Prop :=
  ∀ m : ↥(withGhost G).edgeFinset → ℕ, gc15_threeGap G β h o x y m ≤ 0








theorem gc82_ThreeGapNonpos_iff_gc15 (β h : ℝ) (o x y : V) :
    gc82_ThreeGapNonpos G β h o x y ↔ gc15_PerConfigUrsellSign G β h o x y := Iff.rfl









def gc82_ThreeGapAllConnSupported (β h : ℝ) (o x y : V) : Prop :=
  ∀ m : ↥(withGhost G).edgeFinset → ℕ,
    ¬ gc82_allConn G β h o x y m → gc15_threeGap G β h o x y m = 0



















noncomputable def gc82_delta3 (β h : ℝ) (o x y : V) : ℝ :=
  ∑' m : ↥(withGhost G).edgeFinset → ℕ,
    (if gc82_allConn G β h o x y m then (- (1/2) * gc15_threeGap G β h o x y m) else 0)












theorem gc82_gated_eq_ungated (β h : ℝ) (o x y : V)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    (if gc82_allConn G β h o x y m then (- (1/2) * gc15_threeGap G β h o x y m) else 0)
      = - (1/2) * gc15_threeGap G β h o x y m := by
  by_cases hac : gc82_allConn G β h o x y m
  · rw [if_pos hac]
  · rw [if_neg hac, hsupp m hac]; ring









theorem gc82_delta3_eq_neg_half_tsum (β h : ℝ) (o x y : V)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    gc82_delta3 G β h o x y
      = - (1/2) * ∑' m, gc15_threeGap G β h o x y m := by
  unfold gc82_delta3
  rw [← tsum_mul_left]
  exact tsum_congr (fun m => gc82_gated_eq_ungated G β h o x y hsupp m)













theorem gc82_summand_nonneg (β h : ℝ) (o x y : V)
    (hsign : gc82_ThreeGapNonpos G β h o x y)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    0 ≤ (if gc82_allConn G β h o x y m then (- (1/2) * gc15_threeGap G β h o x y m) else 0) := by
  by_cases hac : gc82_allConn G β h o x y m
  · rw [if_pos hac]
    have := hsign m
    linarith
  · rw [if_neg hac]








theorem gc82_delta3_nonneg (β h : ℝ) (o x y : V)
    (hsign : gc82_ThreeGapNonpos G β h o x y) :
    0 ≤ gc82_delta3 G β h o x y := by
  unfold gc82_delta3
  exact tsum_nonneg (fun m => gc82_summand_nonneg G β h o x y hsign m)


















theorem gc82_grahamResummation (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = -2 * gc82_delta3 G β h o x y := by
  rw [gc82_delta3_eq_neg_half_tsum G β h o x y hsupp,
      ← gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]
  ring






theorem gc82_delta3_eq_gc81 (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    gc82_delta3 G β h o x y = gc81_grahamAllConnMass G β h o x y := by
  rw [gc82_delta3_eq_neg_half_tsum G β h o x y hsupp,
      ← gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]
  unfold gc81_grahamAllConnMass
  ring













theorem gc82_ursell_nonpos (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsign : gc82_ThreeGapNonpos G β h o x y)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ3 : 0 < (gc15_Z0 G β h) ^ 3 := pow_pos hZ 3
  have hid := gc82_grahamResummation G β h o x y hox hoy hxy hsupp
  have hδ := gc82_delta3_nonneg G β h o x y hsign
  have hpoly : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y ≤ 0 := by
    rw [hid]; nlinarith [hδ]
  nlinarith [hZ3, hpoly]






theorem gc82_ghs (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc82_ThreeGapNonpos G β h o x y)
    (hsupp : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc82_ThreeGapAllConnSupported G β h o x y) :
    GHSThreePointSym G β h o := by
  rw [ghc_ghsSym_iff_ursell_nonpos]
  intro x y he
  have hxy : x ≠ y := by rw [SimpleGraph.mem_edgeFinset] at he; exact G.ne_of_adj he
  by_cases hox : o = x
  · subst hox; exact ghc_ursell_nonpos_degenerate G β h hβ hh o y hxy
  · by_cases hoy : o = y
    · subst hoy; rw [ghc_ursell_swap]; exact ghc_ursell_nonpos_degenerate G β h hβ hh o x hox
    · exact gc82_ursell_nonpos G β h o x y hox hoy hxy (hsign x y hox hoy hxy) (hsupp x y hox hoy hxy)




theorem gc82_aizenman_barsky (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc82_ThreeGapNonpos G β h o x y)
    (hsupp : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc82_ThreeGapAllConnSupported G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J (gc82_ghs G β h hβ hh o hsign hsupp) hfactor
















theorem gc82_delta3_at_zero_of_residues (β : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsupp : gc82_ThreeGapAllConnSupported G β 0 o x y) :
    gc82_delta3 G β 0 o x y = 0 := by
  rw [gc82_delta3_eq_neg_half_tsum G β 0 o x y hsupp,
      ← gc15_u3_eq_tsum_threeGap G β 0 o x y hox hoy hxy,
      fa_ghs_ursell3_h0_eq_zero G β o x y]
  ring





theorem gc82_delta3_eq_gc81_at_zero (β : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsupp : gc82_ThreeGapAllConnSupported G β 0 o x y) :
    gc82_delta3 G β 0 o x y = gc81_grahamAllConnMass G β 0 o x y := by
  rw [gc82_delta3_at_zero_of_residues G β o x y hox hoy hxy hsupp,
      gc81_grahamMass_at_zero G β o x y]























theorem gc82_graham_geometric_status (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsign : gc82_ThreeGapNonpos G β h o x y)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    ((gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = -2 * gc82_delta3 G β h o x y)
    ∧ (0 ≤ gc82_delta3 G β h o x y)
    ∧ (eg_ursell3 G β h o x y ≤ 0) :=
  ⟨gc82_grahamResummation G β h o x y hox hoy hxy hsupp,
   gc82_delta3_nonneg G β h o x y hsign,
   gc82_ursell_nonpos G β h o x y hox hoy hxy hsign hsupp⟩

end StatMech.Walls
