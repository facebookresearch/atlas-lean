/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Ising.GKS
import Code.Sharpness.GHSFull
import Code.Sharpness.GHSConcavity
import Code.Walls.ghc_urselleqgap
import Code.Walls.ghc_twicediff
import Code.Walls.gc_core

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness
open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]









noncomputable def gc4_D1cov2 (β h : ℝ) (o x : V) : ℝ :=
    (β * (isingExpectation G β h (fun s => (spin s o * spin s x) * totalSpin s)
        - isingExpectation G β h (fun s => spin s o * spin s x) * isingExpectation G β h totalSpin))
    - ((β * (isingExpectation G β h (fun s => spin s o * totalSpin s)
            - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpin))
          * isingExpectation G β h (fun s => spin s x)
        + isingExpectation G β h (fun s => spin s o)
          * (β * (isingExpectation G β h (fun s => spin s x * totalSpin s)
              - isingExpectation G β h (fun s => spin s x) * isingExpectation G β h totalSpin)))





theorem gc4_hasDerivAt_cov2 (β h : ℝ) (o x : V) :
    HasDerivAt (fun h => cov2 G β h o x) (gc4_D1cov2 G β h o x) h := by
  unfold cov2 gc4_D1cov2
  exact (hasDerivAt_expectation G β h (fun s => spin s o * spin s x)).sub
    ((hasDerivAt_expectation G β h (fun s => spin s o)).mul
      (hasDerivAt_expectation G β h (fun s => spin s x)))










theorem gc4_D1cov2_eq_sum_u3 (β h : ℝ) (o x : V) :
    gc4_D1cov2 G β h o x = β * ∑ y, eg_ursell3 G β h o x y := by
  unfold gc4_D1cov2
  rw [expectation_mul_totalSpin, expectation_mul_totalSpin, expectation_mul_totalSpin,
    expectation_totalSpin]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  have hassoc : isingExpectation G β h (fun s => spin s o * spin s x * spin s y)
      = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) := by
    congr 1; funext s; ring
  unfold eg_ursell3
  rw [hassoc]
  ring




theorem gc4_deriv_magnetization_eq_fun (β : ℝ) (o : V) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o))
      = (fun h => β * ∑ x, cov2 G β h o x) := by
  funext h
  rw [deriv_magnetization_eq_sum_cov]
  simp only [cov2]




theorem gc4_hasDerivAt_sumcov2 (β h : ℝ) (o : V) :
    HasDerivAt (fun h => β * ∑ x, cov2 G β h o x)
      (β * ∑ x, gc4_D1cov2 G β h o x) h := by
  have hsum : HasDerivAt (fun h => ∑ x, cov2 G β h o x) (∑ x, gc4_D1cov2 G β h o x) h := by
    have hpt : (fun h => ∑ x, cov2 G β h o x)
        = ∑ x : V, (fun h => cov2 G β h o x) := by rw [Finset.sum_fn]
    rw [hpt]
    exact HasDerivAt.sum (fun x _ => gc4_hasDerivAt_cov2 G β h o x)
  exact hsum.const_mul β






theorem gc4_hasDerivAt_deriv_magnetization (β h : ℝ) (o : V) :
    HasDerivAt (deriv (fun h => isingExpectation G β h (fun s => spin s o)))
      (β * (β * ∑ x, ∑ y, eg_ursell3 G β h o x y)) h := by
  rw [gc4_deriv_magnetization_eq_fun]
  have hval : (β * ∑ x, gc4_D1cov2 G β h o x) = β * (β * ∑ x, ∑ y, eg_ursell3 G β h o x y) := by
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => gc4_D1cov2_eq_sum_u3 G β h o x)
  rw [← hval]
  exact gc4_hasDerivAt_sumcov2 G β h o





theorem gc4_deriv2_magnetization_eq (β h : ℝ) (o : V) :
    deriv^[2] (fun h => isingExpectation G β h (fun s => spin s o)) h
      = β * (β * ∑ x, ∑ y, eg_ursell3 G β h o x y) := by
  change deriv (deriv (fun h => isingExpectation G β h (fun s => spin s o))) h = _
  exact (gc4_hasDerivAt_deriv_magnetization G β h o).deriv












theorem gc4_deriv2_magnetization_nonpos (β : ℝ) (hβ : 0 ≤ β) (o : V) (h : ℝ) (hh : 0 ≤ h)
    (hsd : GHSSignDominance G β h o) :
    deriv^[2] (fun h => isingExpectation G β h (fun s => spin s o)) h ≤ 0 := by
  rw [gc4_deriv2_magnetization_eq]
  have hsum : ∑ x, ∑ y, eg_ursell3 G β h o x y ≤ 0 :=
    Finset.sum_nonpos (fun x _ => Finset.sum_nonpos (fun y _ =>
      gc_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y))
  have hββ : 0 ≤ β * β := mul_nonneg hβ hβ
  nlinarith [hsum, hββ]












theorem gc4_magnetization_concaveOn (β : ℝ) (hβ : 0 ≤ β) (o : V)
    (hsd : ∀ h, 0 ≤ h → GHSSignDominance G β h o) :
    ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)) := by
  apply gtd_magnetization_concaveOn_of_deriv2_nonpos
  intro h hh
  rw [interior_Ici] at hh
  exact gc4_deriv2_magnetization_nonpos G β hβ o h (le_of_lt hh) (hsd h (le_of_lt hh))









theorem gc4_ursell_nonpos_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y





theorem gc4_ghs_concavity_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) :
    GHSThreePointSym G β h o :=
  gc_ghs_concavity_of_signDominance G β h hβ hh o hsd









theorem gc4_aizenman_barsky_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hsd : GHSSignDominance G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc_aizenman_barsky_of_signDominance G β h hβ hh o J hsd hfactor





















theorem gc4_concavitySharpness (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hsd : ∀ h', 0 ≤ h' → GHSSignDominance G β h' o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    GHSThreePointSym G β h o
      ∧ ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))
      ∧ bondEnergySusceptibility G β h o
          ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  ⟨gc4_ghs_concavity_of_signDominance G β h hβ hh o (hsd h hh),
    gc4_magnetization_concaveOn G β hβ o hsd,
    gc4_aizenman_barsky_of_signDominance G β h hβ hh o J (hsd h hh) hfactor⟩

end StatMech.Walls
