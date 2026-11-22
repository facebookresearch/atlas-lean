/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil

namespace MathlibExtTest.Analysis.Numerical.PeriodicLeapfrogStencil

/-- Nonconstant periodic vectors on `N = 3`, `h = 1/2`: `⟪D₊ v, u⟫_h = ⟪v, -D₋ u⟫_h = -5`,
while the wrong-sign pairing `⟪v, D₋ u⟫_h` is `+5`. -/
example :
    weightedInner (1 / 2) (dPlus (1 / 2) ![1, 2, 4]) ![3, -1, 2] = -5 ∧
      weightedInner (1 / 2) ![1, 2, 4] (-dMinus (1 / 2) ![3, -1, 2]) = -5 ∧
      weightedInner (1 / 2) ![1, 2, 4] (dMinus (1 / 2) ![3, -1, 2]) = 5 := by
  have s0 : periodicSucc (0 : Fin 3) = 1 := rfl
  have s1 : periodicSucc (1 : Fin 3) = 2 := rfl
  have s2 : periodicSucc (2 : Fin 3) = 0 := rfl
  have p0 : periodicPred (0 : Fin 3) = 2 := rfl
  have p1 : periodicPred (1 : Fin 3) = 0 := rfl
  have p2 : periodicPred (2 : Fin 3) = 1 := rfl
  unfold weightedInner dPlus dMinus
  simp only [Fin.sum_univ_three, s0, s1, s2, p0, p1, p2, Pi.neg_apply]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Forward difference with the periodic wrap omitted: the last cell's term is dropped. -/
noncomputable def dPlusNoWrap {N : ℕ} (h : ℝ) (v : Fin N → ℝ) : Fin N → ℝ :=
  fun j => if j.val + 1 < N then (v (periodicSucc j) - v j) / h else 0

/-- Omitting the periodic wrap breaks summation by parts (`N = 3`, `h = 1/2`). -/
example :
    ¬ IsWeightedAdjoint (1 / 2) (dPlusNoWrap (N := 3) (1 / 2)) (-dMinus (1 / 2)) := by
  intro H
  have hH := H ![3, -1, 2] ![1, 2, 4]
  simp only [Pi.neg_apply] at hH
  have hLHS : weightedInner (1 / 2) (dPlusNoWrap (N := 3) (1 / 2) ![1, 2, 4])
      ![3, -1, 2] = 1 := by
    have s0 : periodicSucc (0 : Fin 3) = 1 := rfl
    have s1 : periodicSucc (1 : Fin 3) = 2 := rfl
    have c0 : (0 : Fin 3).val + 1 < 3 := by decide
    have c1 : (1 : Fin 3).val + 1 < 3 := by decide
    have c2 : ¬ (2 : Fin 3).val + 1 < 3 := by decide
    unfold weightedInner dPlusNoWrap
    simp only [Fin.sum_univ_three, ite_eq_left c0, ite_eq_left c1, ite_eq_right c2,
      s0, s1]
    norm_num
  have hRHS : weightedInner (1 / 2) ![1, 2, 4] (-dMinus (1 / 2) ![3, -1, 2]) = -5 := by
    have p0 : periodicPred (0 : Fin 3) = 2 := rfl
    have p1 : periodicPred (1 : Fin 3) = 0 := rfl
    have p2 : periodicPred (2 : Fin 3) = 1 := rfl
    unfold weightedInner dMinus
    simp only [Fin.sum_univ_three, p0, p1, p2, Pi.neg_apply]
    norm_num
  rw [hLHS, hRHS] at hH
  have h01 : (0 : ℝ) < 1 := zero_lt_one
  rw [hH] at h01
  have hneg : ¬((0 : ℝ) < -5) := by norm_num
  exact hneg h01


/-- A concrete leapfrog step: the velocity update at each cell. -/
example (u v : Fin 3 → ℝ) (j : Fin 3) :
    (leapfrogStep (1 / 2) 2 (1 / 4) u v).2 j =
      v j + 2 * (1 / 4) * (u j - u (periodicPred j)) / (1 / 2) :=
  (leapfrogStep_apply (1 / 2) 2 (1 / 4) (by norm_num) u v j).1

end MathlibExtTest.Analysis.Numerical.PeriodicLeapfrogStencil
