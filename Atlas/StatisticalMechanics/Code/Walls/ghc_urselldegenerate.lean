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

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]









noncomputable def ursell3 (β h : ℝ) (o x y : V) : ℝ :=
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







theorem ursell3_eq_gap (β h : ℝ) (o x y : V) :
    ursell3 G β h o x y = cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y) := by
  rw [ursell3, ghsThreePoint_eq_ursell]









theorem ghc_u3_degenerate_eq_gap (β h : ℝ) (x y : V) :
    ursell3 G β h x x y
      = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h x y := by
  rw [ursell3_eq_gap, ghs_degenerate_diff]









theorem ghc_ursell_degenerate_left (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (x y : V) (hxy : x ≠ y) :
    ursell3 G β h x x y ≤ 0 := by
  have hid := ghc_u3_degenerate_eq_gap G β h x y
  have hspin : 0 ≤ isingExpectation G β h (fun s => spin s x) :=
    expectation_spin_nonneg G β h hβ hh x
  have hcov : 0 ≤ cov2 G β h x y := cov2_nonneg G β h hβ hh x y hxy
  nlinarith [hid, mul_nonneg hspin hcov]





theorem ghc_ursell_degenerate_right (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (x y : V) (hxy : x ≠ y) :
    ursell3 G β h y x y ≤ 0 := by
  have hsymm : ursell3 G β h y x y = ursell3 G β h y y x := by
    unfold ursell3
    have e1 : (fun s : ConfigSpace V => spin s y * (spin s x * spin s y))
        = (fun s => spin s y * (spin s y * spin s x)) := by funext s; ring
    have e2 : (fun s : ConfigSpace V => spin s x * spin s y)
        = (fun s => spin s y * spin s x) := by funext s; ring
    rw [e1, e2]; ring
  rw [hsymm]
  exact ghc_ursell_degenerate_left G β h hβ hh y x hxy.symm










theorem ghc_ursell_degenerate (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o x y : V) (hxy : x ≠ y) (hoxy : o = x ∨ o = y) :
    ursell3 G β h o x y ≤ 0 := by
  rcases hoxy with rfl | rfl
  · exact ghc_ursell_degenerate_left G β h hβ hh o y hxy
  · exact ghc_ursell_degenerate_right G β h hβ hh x o hxy










theorem ghc_ursell_degenerate_of_mem (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o : V) (e : Sym2 V) (he : e ∈ G.edgeFinset) (hoe : o ∈ e) :
    cov3sym G β h o e - ghsBoundSym G β h o e ≤ 0 := by
  have := ghsThreePoint_of_mem G β h hβ hh o e he hoe
  linarith

end Walls

end StatMech
