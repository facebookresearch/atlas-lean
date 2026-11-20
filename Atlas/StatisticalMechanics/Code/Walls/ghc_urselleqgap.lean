/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2
import Code.Sharpness.GHSFull
import Code.Ising.AizenmanBarsky
import Code.Ising.GHSThreePoint

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Walls

namespace GhcEqGap

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]












noncomputable def eg_ursell3 (β h : ℝ) (o x y : V) : ℝ :=
  isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
    - isingExpectation G β h (fun s => spin s o)
        * isingExpectation G β h (fun s => spin s x * spin s y)
    - isingExpectation G β h (fun s => spin s o * spin s x)
        * isingExpectation G β h (fun s => spin s y)
    - isingExpectation G β h (fun s => spin s o * spin s y)
        * isingExpectation G β h (fun s => spin s x)
    + 2 * isingExpectation G β h (fun s => spin s o)
        * isingExpectation G β h (fun s => spin s x)
        * isingExpectation G β h (fun s => spin s y)












theorem ghc_ursellEqGap (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y) = eg_ursell3 G β h o x y := by
  rw [cov3sym_mk, ghsBoundSym_mk]
  unfold eg_ursell3 cov2 onePt
  ring







theorem ghc_ursell_nonpos_iff_ghs (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y ≤ 0
      ↔ cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y) := by
  rw [← ghc_ursellEqGap]
  constructor <;> intro hle <;> linarith







theorem ghc_ursell_swap (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y = eg_ursell3 G β h o y x := by
  unfold eg_ursell3
  have e1 : (fun s : ConfigSpace V => spin s o * (spin s x * spin s y))
      = (fun s => spin s o * (spin s y * spin s x)) := by funext s; ring
  have e2 : (fun s : ConfigSpace V => spin s x * spin s y)
      = (fun s => spin s y * spin s x) := by funext s; ring
  rw [e1, e2]
  ring









theorem ghc_ghs_of_ursell_nonpos (β h : ℝ) (o : V)
    (h0 : ∀ x y : V, eg_ursell3 G β h o x y ≤ 0) :
    GHSThreePointSym G β h o := by
  intro e _
  induction e with
  | h x y => exact (ghc_ursell_nonpos_iff_ghs G β h o x y).mp (h0 x y)




theorem ghc_ursell_nonpos_of_ghs (β h : ℝ) (o : V)
    (hghs : GHSThreePointSym G β h o) {x y : V} (he : s(x, y) ∈ G.edgeFinset) :
    eg_ursell3 G β h o x y ≤ 0 :=
  (ghc_ursell_nonpos_iff_ghs G β h o x y).mpr (hghs s(x, y) he)








theorem ghc_ghsSym_iff_ursell_nonpos (β h : ℝ) (o : V) :
    GHSThreePointSym G β h o
      ↔ ∀ x y : V, s(x, y) ∈ G.edgeFinset → eg_ursell3 G β h o x y ≤ 0 := by
  constructor
  · intro hghs x y he
    exact ghc_ursell_nonpos_of_ghs G β h o hghs he
  · intro h0 e he
    induction e with
    | h x y => exact (ghc_ursell_nonpos_iff_ghs G β h o x y).mp (h0 x y he)









theorem ghc_ursell_degenerate (β h : ℝ) (x y : V) :
    eg_ursell3 G β h x x y
      = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h x y := by
  rw [← ghc_ursellEqGap]
  exact ghs_degenerate_diff G β h x y









theorem ghc_ursell_nonpos_degenerate (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (x y : V) (hxy : x ≠ y) :
    eg_ursell3 G β h x x y ≤ 0 := by
  rw [ghc_ursell_degenerate]
  have hspin : 0 ≤ isingExpectation G β h (fun s => spin s x) :=
    expectation_spin_nonneg G β h hβ hh x
  have hcov : 0 ≤ cov2 G β h x y := cov2_nonneg G β h hβ hh x y hxy
  nlinarith [mul_nonneg hspin hcov]













theorem ghc_aizenman_barsky_of_ursell (β h : ℝ) (o : V) (J : ℝ)
    (h0 : ∀ x y : V, eg_ursell3 G β h o x y ≤ 0)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J (ghc_ghs_of_ursell_nonpos G β h o h0) hfactor

end GhcEqGap
end Walls

end StatMech
