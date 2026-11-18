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

end MathlibExtTest.Analysis.Numerical.PeriodicYeeEnergy
