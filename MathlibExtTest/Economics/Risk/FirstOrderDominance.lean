/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Risk.FirstOrderDominance
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Risk.FirstOrderDominance`

On prizes `0 < 1 < 2`, the sure prize `2` dominates the fifty-fifty lottery over `0` and `2`
(expected values `2` and `1`), and not conversely. -/

open Convexity
open MathlibExt.Economics.ExpectedUtility
open MathlibExt.Probability.StrassenCouplingWanted
open MathlibExt.Economics.Risk

namespace MathlibExtTest.Economics.Risk.FirstOrderDominance

/-- Test lottery `p`: `StdSimplex.duple 0 2` with weights `1/2, 1/2`. -/
noncomputable def exP : StdSimplex ℝ (Fin 3) :=
  StdSimplex.duple (0 : Fin 3) (2 : Fin 3) (s := (1 / 2 : ℝ)) (t := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)

/-- Test lottery `q`: `StdSimplex.single 2`. -/
noncomputable def exQ : StdSimplex ℝ (Fin 3) := StdSimplex.single (2 : Fin 3)

theorem exQ_w0 : exQ.weights 0 = 0 := by simp [exQ, StdSimplex.weights_single]
theorem exQ_w1 : exQ.weights 1 = 0 := by simp [exQ, StdSimplex.weights_single]
theorem exQ_w2 : exQ.weights 2 = 1 := by simp [exQ, StdSimplex.weights_single]
theorem exP_w0 : exP.weights 0 = 1 / 2 := by simp [exP, StdSimplex.weights_duple, Finsupp.add_apply]
theorem exP_w1 : exP.weights 1 = 0 := by simp [exP, StdSimplex.weights_duple, Finsupp.add_apply]
theorem exP_w2 : exP.weights 2 = 1 / 2 := by simp [exP, StdSimplex.weights_duple, Finsupp.add_apply]

theorem ex_f0 : Finset.univ.filter (· ≤ (0 : Fin 3)) = {0} := by decide
theorem ex_f1 : Finset.univ.filter (· ≤ (1 : Fin 3)) = {0, 1} := by decide
theorem ex_f2 : Finset.univ.filter (· ≤ (2 : Fin 3)) = {0, 1, 2} := by decide

theorem ex_m01 : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)) := by decide
theorem ex_m12 : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by decide
theorem ex_ne01 : (0 : Fin 3) ≠ 1 := by decide

theorem ex_c0 : ((0 : Fin 3) : ℝ) = 0 := by simp
theorem ex_c1 : ((1 : Fin 3) : ℝ) = 1 := by simp
theorem ex_c2 : ((2 : Fin 3) : ℝ) = 2 := by simp

/-- (a) `q` first-order dominates `p`. -/
theorem ex_firstOrderDominates : FirstOrderDominates exQ exP := by
  intro t
  fin_cases t
  · change ∑ x ∈ Finset.univ.filter (· ≤ (0 : Fin 3)), exQ.weights x ≤
        ∑ x ∈ Finset.univ.filter (· ≤ (0 : Fin 3)), exP.weights x
    rw [ex_f0, Finset.sum_singleton, Finset.sum_singleton, exQ_w0, exP_w0]
    norm_num
  · change ∑ x ∈ Finset.univ.filter (· ≤ (1 : Fin 3)), exQ.weights x ≤
        ∑ x ∈ Finset.univ.filter (· ≤ (1 : Fin 3)), exP.weights x
    rw [ex_f1, Finset.sum_pair ex_ne01, Finset.sum_pair ex_ne01,
      exQ_w0, exQ_w1, exP_w0, exP_w1]
    norm_num
  · change ∑ x ∈ Finset.univ.filter (· ≤ (2 : Fin 3)), exQ.weights x ≤
        ∑ x ∈ Finset.univ.filter (· ≤ (2 : Fin 3)), exP.weights x
    rw [ex_f2, Finset.sum_insert ex_m01, Finset.sum_insert ex_m01,
      Finset.sum_insert ex_m12, Finset.sum_insert ex_m12,
      Finset.sum_singleton, Finset.sum_singleton,
      exQ_w0, exQ_w1, exQ_w2, exP_w0, exP_w1, exP_w2]
    norm_num

/-- (b) Expected utilities under `u i = i`. -/
theorem ex_expectedUtility_p : expectedUtility (fun i : Fin 3 => (i : ℝ)) exP = 1 := by
  simp only [expectedUtility, Fin.sum_univ_three]
  rw [exP_w0, exP_w1, exP_w2, ex_c0, ex_c1, ex_c2]
  norm_num

theorem ex_expectedUtility_q : expectedUtility (fun i : Fin 3 => (i : ℝ)) exQ = 2 := by
  simp only [expectedUtility, Fin.sum_univ_three]
  rw [exQ_w0, exQ_w1, exQ_w2, ex_c0, ex_c1, ex_c2]
  norm_num

/-- (c) Dominance is not symmetric here. -/
theorem ex_not_firstOrderDominates : ¬ FirstOrderDominates exP exQ := by
  intro hcon
  have h0 := hcon 0
  rw [ex_f0, Finset.sum_singleton, Finset.sum_singleton, exP_w0, exQ_w0] at h0
  norm_num at h0

end MathlibExtTest.Economics.Risk.FirstOrderDominance
