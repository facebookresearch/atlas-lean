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
import Code.Walls.ghc_urselleqgap

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech

namespace Walls

namespace Gc5EqGap

open StatMech.Ising StatMech.Sharpness
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




















noncomputable def eg_ursell4_ghost (β h : ℝ) (o x y : V) : ℝ :=
  isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
    - isingExpectation G β h (fun s => spin s o * spin s x)
        * isingExpectation G β h (fun s => spin s y)
    - isingExpectation G β h (fun s => spin s o * spin s y)
        * isingExpectation G β h (fun s => spin s x)
    - isingExpectation G β h (fun s => spin s o)
        * isingExpectation G β h (fun s => spin s x * spin s y)



noncomputable def eg_tripleProduct (β h : ℝ) (o x y : V) : ℝ :=
  isingExpectation G β h (fun s => spin s o)
    * isingExpectation G β h (fun s => spin s x)
    * isingExpectation G β h (fun s => spin s y)














theorem gc5_ursellEqGap (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y
      = eg_ursell4_ghost G β h o x y + 2 * eg_tripleProduct G β h o x y := by
  unfold eg_ursell3 eg_ursell4_ghost eg_tripleProduct
  ring



theorem gc5_ursell4_ghost_eq (β h : ℝ) (o x y : V) :
    eg_ursell4_ghost G β h o x y
      = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
          - isingExpectation G β h (fun s => spin s o * spin s x)
              * isingExpectation G β h (fun s => spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s y)
              * isingExpectation G β h (fun s => spin s x)
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x * spin s y) := rfl




theorem gc5_ursell3_eq_ursell4_ghost_sub (β h : ℝ) (o x y : V) :
    eg_ursell4_ghost G β h o x y
      = eg_ursell3 G β h o x y - 2 * eg_tripleProduct G β h o x y := by
  rw [gc5_ursellEqGap]; ring







theorem gc5_ursell4_ghost_swap (β h : ℝ) (o x y : V) :
    eg_ursell4_ghost G β h o x y = eg_ursell4_ghost G β h o y x := by
  unfold eg_ursell4_ghost
  have e1 : (fun s : ConfigSpace V => spin s o * (spin s x * spin s y))
      = (fun s => spin s o * (spin s y * spin s x)) := by funext s; ring
  have e2 : (fun s : ConfigSpace V => spin s x * spin s y)
      = (fun s => spin s y * spin s x) := by funext s; ring
  rw [e1, e2]
  ring
















theorem gc5_ursell4_ghost_eq_gap (β h : ℝ) (o x y : V) :
    eg_ursell4_ghost G β h o x y
      = (cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y))
          - 2 * eg_tripleProduct G β h o x y := by
  rw [gc5_ursell3_eq_ursell4_ghost_sub, ghc_ursellEqGap]









theorem gc5_ghs_iff_ursell4_ghost (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y) ≤ ghsBoundSym G β h o s(x, y)
      ↔ eg_ursell4_ghost G β h o x y ≤ -2 * eg_tripleProduct G β h o x y := by
  rw [gc5_ursell4_ghost_eq_gap]
  constructor <;> intro hle <;> linarith











theorem gc5_ursell4_ghost_degenerate (β h : ℝ) (x y : V) :
    eg_ursell4_ghost G β h x x y
      = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h x y
        - 2 * (isingExpectation G β h (fun s => spin s x)
            * isingExpectation G β h (fun s => spin s x))
          * isingExpectation G β h (fun s => spin s y) := by
  rw [gc5_ursell3_eq_ursell4_ghost_sub, ghc_ursell_degenerate]
  unfold eg_tripleProduct
  ring











theorem gc5_ursell4_ghost_nonpos_degenerate (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (x y : V) (hxy : x ≠ y) :
    eg_ursell4_ghost G β h x x y ≤ 0 := by
  rw [gc5_ursell4_ghost_degenerate]
  have hspinx : 0 ≤ isingExpectation G β h (fun s => spin s x) :=
    expectation_spin_nonneg G β h hβ hh x
  have hspiny : 0 ≤ isingExpectation G β h (fun s => spin s y) :=
    expectation_spin_nonneg G β h hβ hh y
  have hcov : 0 ≤ cov2 G β h x y := cov2_nonneg G β h hβ hh x y hxy
  nlinarith [mul_nonneg hspinx hcov, mul_nonneg (mul_nonneg hspinx hspinx) hspiny]















theorem gc5_ghs_of_ursell4_ghost (β h : ℝ) (o : V)
    (h0 : ∀ x y : V, eg_ursell4_ghost G β h o x y ≤ -2 * eg_tripleProduct G β h o x y) :
    GHSThreePointSym G β h o := by
  intro e _
  induction e with
  | h x y => exact (gc5_ghs_iff_ursell4_ghost G β h o x y).mpr (h0 x y)

end Gc5EqGap

end Walls

end StatMech
