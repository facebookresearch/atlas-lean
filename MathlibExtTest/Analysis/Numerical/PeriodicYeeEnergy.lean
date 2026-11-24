/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.PeriodicYeeEnergy
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
open MathlibExt.Analysis.Numerical.PeriodicYeeEnergy

namespace MathlibExtTest.Analysis.Numerical.PeriodicYeeEnergy

/-- Concrete state `u = (3, -1, 2)`, `v = (1, 2, 4)` at
`h = 1 / 2`, `c = 2`, `dt = 1 / 8`: the energy is `75 / 4` and the
squared pair norm is `35 / 2`. -/
example :
    yeeEnergy (N := 3) (1 / 2) 2 (1 / 8) ![3, -1, 2] ![1, 2, 4] = 75 / 4 ∧
      pairNormSq (N := 3) (1 / 2) ![3, -1, 2] ![1, 2, 4] = 35 / 2 := by
  have s0 : periodicSucc (0 : Fin 3) = 1 := rfl
  have s1 : periodicSucc (1 : Fin 3) = 2 := rfl
  have s2 : periodicSucc (2 : Fin 3) = 0 := rfl
  have hE : yeeEnergy (N := 3) (1 / 2) 2 (1 / 8) ![3, -1, 2] ![1, 2, 4] =
      75 / 4 := by
    unfold yeeEnergy weightedNormSq weightedInner
      scaledForwardDifference dPlus
    simp only [Fin.sum_univ_three, s0, s1, s2, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    norm_num
  have hP : pairNormSq (N := 3) (1 / 2) ![3, -1, 2] ![1, 2, 4] = 35 / 2 := by
    unfold pairNormSq weightedNormSq weightedInner
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    norm_num
  exact ⟨hE, hP⟩

/-- The zero pair has zero energy at the same grid data. -/
example : yeeEnergy (N := 3) (1 / 2) 2 (1 / 8) 0 0 = 0 :=
  yeeEnergy_zero (1 / 2) 2 (1 / 8)

/-- One step and five steps from the concrete state keep the energy at
`75 / 4`. -/
example :
    yeeEnergy (N := 3) (1 / 2) 2 (1 / 8)
        (leapfrogStep (1 / 2) 2 (1 / 8) ![3, -1, 2] ![1, 2, 4]).1
        (leapfrogStep (1 / 2) 2 (1 / 8) ![3, -1, 2] ![1, 2, 4]).2 = 75 / 4 ∧
      yeeEnergy (N := 3) (1 / 2) 2 (1 / 8)
        (leapfrogIterate (1 / 2) 2 (1 / 8) ![3, -1, 2] ![1, 2, 4] 5).1
        (leapfrogIterate (1 / 2) 2 (1 / 8) ![3, -1, 2] ![1, 2, 4] 5).2 =
        75 / 4 := by
  have s0 : periodicSucc (0 : Fin 3) = 1 := rfl
  have s1 : periodicSucc (1 : Fin 3) = 2 := rfl
  have s2 : periodicSucc (2 : Fin 3) = 0 := rfl
  have hE : yeeEnergy (N := 3) (1 / 2) 2 (1 / 8) ![3, -1, 2] ![1, 2, 4] =
      75 / 4 := by
    unfold yeeEnergy weightedNormSq weightedInner
      scaledForwardDifference dPlus
    simp only [Fin.sum_univ_three, s0, s1, s2, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    norm_num
  exact ⟨(leapfrogStep_yeeEnergy _ _ _ _ _).trans hE,
    (leapfrogIterate_yeeEnergy _ _ _ _ _ _).trans hE⟩

/-- Energy invariance needs no grid-size or spacing assumption: it holds
on a one-cell grid at any spacing, including `h = 0`. -/
example (h c dt : ℝ) (u v : Fin 1 → ℝ) :
    yeeEnergy h c dt (leapfrogStep h c dt u v).1 (leapfrogStep h c dt u v).2 =
      yeeEnergy h c dt u v :=
  leapfrogStep_yeeEnergy h c dt u v

/-- At `h = 1 / 2`, `c = 2`, `dt = 1 / 8` the Courant number is `1 / 2`,
so with `rho = 1 / 2` the energy is trapped between half and
three halves of the squared pair norm. -/
example (u v : Fin 3 → ℝ) :
    (1 - 1 / 2) * pairNormSq (1 / 2) u v ≤ yeeEnergy (1 / 2) 2 (1 / 8) u v ∧
      yeeEnergy (1 / 2) 2 (1 / 8) u v ≤ (1 + 1 / 2) * pairNormSq (1 / 2) u v :=
  yeeEnergy_pairNormSq_bounds (1 / 2) 2 (1 / 8) (1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) u v

/-- At the same data every iterate has pair norm at most `sqrt 3` times
the initial pair norm. -/
example (u0 v0 : Fin 3 → ℝ) (n : ℕ) :
    pairNorm (1 / 2) (leapfrogIterate (1 / 2) 2 (1 / 8) u0 v0 n).1
        (leapfrogIterate (1 / 2) 2 (1 / 8) u0 v0 n).2 ≤
      Real.sqrt 3 * pairNorm (1 / 2) u0 v0 := by
  have hb := leapfrogIterate_pairNorm_le (1 / 2) 2 (1 / 8) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    u0 v0 n
  have h3 : ((1 : ℝ) + 1 / 2) / (1 - 1 / 2) = 3 := by norm_num
  rwa [h3] at hb

/-- Courant boundary on the even grid `N = 2` at Courant number one
(`h = c = dt = 1`): the alternating pair `u = (1, -1)`, `v = -u` is
nonzero but has zero energy. -/
example :
    yeeEnergy (N := 2) 1 1 1 ![1, -1] ![-1, 1] = 0 ∧
      pairNormSq (N := 2) 1 ![1, -1] ![-1, 1] = 4 := by
  have s0 : periodicSucc (0 : Fin 2) = 1 := rfl
  have s1 : periodicSucc (1 : Fin 2) = 0 := rfl
  constructor
  · unfold yeeEnergy weightedNormSq weightedInner
      scaledForwardDifference dPlus
    simp only [Fin.sum_univ_two, s0, s1, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · unfold pairNormSq weightedNormSq weightedInner
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-- Hence at `N = 2` and Courant number one no positive constant
bounds the energy below by the squared pair norm. -/
example :
    ¬ ∃ eps : ℝ, 0 < eps ∧
      ∀ u v : Fin 2 → ℝ, eps * pairNormSq 1 u v ≤ yeeEnergy 1 1 1 u v :=
  no_positive_coercivity_of_courant_ge_one le_rfl even_two 1 1 1 one_pos
    (by norm_num)

end MathlibExtTest.Analysis.Numerical.PeriodicYeeEnergy
