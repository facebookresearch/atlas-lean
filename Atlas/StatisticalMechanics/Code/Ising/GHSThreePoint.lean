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

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]












theorem ghsThreePoint_eq_ursell (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y) - ghsBoundSym G β h o s(x, y)
      = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y))
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x * spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s x)
              * isingExpectation G β h (fun s => spin s y)
          - isingExpectation G β h (fun s => spin s o * spin s y)
              * isingExpectation G β h (fun s => spin s x)
          + 2 * isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x)
              * isingExpectation G β h (fun s => spin s y) := by
  rw [cov3sym_mk, ghsBoundSym_mk]
  unfold cov2 onePt
  ring




theorem expectation_spin_mul_self (β h : ℝ) (x : V) :
    isingExpectation G β h (fun s => spin s x * spin s x) = 1 := by
  have hsq : (fun s => spin s x * spin s x) = (fun _ : ConfigSpace V => (1 : ℝ)) := by
    funext s; exact spin_sq s x
  rw [hsq]
  unfold isingExpectation
  simp [isingProb_sum_eq_one G β h]


theorem expectation_spin_self_mul (β h : ℝ) (x y : V) :
    isingExpectation G β h (fun s => spin s x * (spin s x * spin s y))
      = isingExpectation G β h (fun s => spin s y) := by
  congr 1; funext s; rw [← mul_assoc, spin_sq, one_mul]





theorem cov2_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x : V) (hox : o ≠ x) :
    0 ≤ cov2 G β h o x := by
  unfold cov2
  have := cov_nonneg G β h hβ hh o x hox
  linarith











theorem ghs_degenerate_diff (β h : ℝ) (x y : V) :
    cov3sym G β h x s(x, y) - ghsBoundSym G β h x s(x, y)
      = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h x y := by
  rw [cov3sym_mk, ghsBoundSym_mk]
  unfold cov2 onePt
  rw [expectation_spin_self_mul, expectation_spin_mul_self]
  ring










theorem ghs_degenerate_left (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x y : V) (hxy : x ≠ y) :
    cov3sym G β h x s(x, y) ≤ ghsBoundSym G β h x s(x, y) := by
  have hid := ghs_degenerate_diff G β h x y
  have hspin : 0 ≤ isingExpectation G β h (fun s => spin s x) :=
    expectation_spin_nonneg G β h hβ hh x
  have hcov : 0 ≤ cov2 G β h x y := cov2_nonneg G β h hβ hh x y hxy
  nlinarith [hid, mul_nonneg hspin hcov]



theorem ghs_degenerate_right (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x y : V) (hxy : x ≠ y) :
    cov3sym G β h y s(x, y) ≤ ghsBoundSym G β h y s(x, y) := by
  rw [Sym2.eq_swap]
  exact ghs_degenerate_left G β h hβ hh y x hxy.symm














theorem ghsThreePoint_of_mem (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) (hoe : o ∈ e) :
    cov3sym G β h o e ≤ ghsBoundSym G β h o e := by
  
  induction e with
  | h x y =>
    have hxy : x ≠ y := by
      have := (SimpleGraph.mem_edgeFinset).mp he
      exact (SimpleGraph.Adj.ne this)
    rw [Sym2.mem_iff] at hoe
    rcases hoe with rfl | rfl
    · exact ghs_degenerate_left G β h hβ hh o y hxy
    · exact ghs_degenerate_right G β h hβ hh x o hxy

end Ising

end StatMech
