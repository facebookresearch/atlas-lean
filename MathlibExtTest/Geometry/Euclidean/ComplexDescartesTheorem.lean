/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Euclidean.ComplexDescartesTheorem

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the complex Descartes theorem

The bounding circle of radius `6` centred at `0` and the circles of radii `3, 3, 2` centred at
`3, -3, 4i` satisfy hypothesis (b) of the theorem with `e = 0`, so the theorem applies; the
products curvature × center are `(0, 1, -1, 2i)` and the relation reads
`(2i)² = -4 = 2 (1 + 1 - 4)`.
-/

namespace MathlibExtTest.Geometry.Euclidean.ComplexDescartesTheorem

open Complex MathlibExt.Geometry.Euclidean.ComplexDescartesTheorem

/-- Centers of the test configuration. -/
noncomputable def c : Fin 4 → ℂ := ![0, 3, -3, 4 * I]

/-- Radii of the test configuration. -/
noncomputable def r : Fin 4 → ℝ := ![6, 3, 3, 2]

/-- Signed curvatures of the test configuration. -/
noncomputable def k : Fin 4 → ℝ := ![-1 / 6, 1 / 3, 1 / 3, 1 / 2]

theorem dist_c (i j : Fin 4) {d : ℝ} (hd : 0 ≤ d) (h : normSq (c i - c j) = d ^ 2) :
    dist (c i) (c j) = d := by
  rw [dist_eq_norm]
  have h2 : ‖c i - c j‖ ^ 2 = d ^ 2 := by rw [Complex.sq_norm, h]
  exact (pow_left_inj₀ (norm_nonneg _) hd two_ne_zero).1 h2

theorem hyp : ∃ e : Fin 4, k e = -1 / r e ∧ (∀ j, j ≠ e → k j = 1 / r j) ∧
    (∀ j, j ≠ e → dist (c e) (c j) = r e - r j) ∧
    ∀ i j, i ≠ e → j ≠ e → i ≠ j → dist (c i) (c j) = r i + r j := by
  refine ⟨0, by norm_num [k, r], ?_, ?_, ?_⟩
  · intro j hj
    fin_cases j <;> simp_all [k, r]
  · intro j hj
    fin_cases j
    · simp at hj
    all_goals
      refine dist_c _ _ (by norm_num [r]) ?_
      simp [c, r, normSq_apply]; norm_num
  · intro i j hi hj hij
    fin_cases i <;> fin_cases j <;> simp at hi hj hij
    all_goals
      refine dist_c _ _ (by norm_num [r]) ?_
      simp [c, r, normSq_apply]; norm_num

/-- The complex Descartes theorem applied to the test configuration. -/
example : (∑ i, (k i : ℂ) * c i) ^ 2 = 2 * ∑ i, ((k i : ℂ) * c i) ^ 2 :=
  complex_descartes_theorem c r k (fun i => by fin_cases i <;> norm_num [r]) (Or.inr hyp)

/-- The same identity checked by direct computation. -/
example : (∑ i, (k i : ℂ) * c i) ^ 2 = -4 := by
  simp [Fin.sum_univ_four, k, c]
  ring_nf
  rw [I_sq]
  ring

end MathlibExtTest.Geometry.Euclidean.ComplexDescartesTheorem
