/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.LinearProgrammingMaximumPrinciple

/-! # Tests for the maximum principle for linear programming -/

namespace MathlibExtTest.Geometry.LinearProgrammingMaximumPrinciple

open MathlibExt.Geometry.LinearProgrammingWanted.ConvexGeometry

-- With no constraint rows, the feasible region is the nonnegative ray.
private noncomputable def rayLP (c : ℝ) : LinearProgram 1 0 where
  c := fun _ => c
  b := 0
  A := 0

private theorem mem_feasible_rayLP (c : ℝ) (x : Fin 1 → ℝ) :
    x ∈ (rayLP c).feasible ↔ 0 ≤ x 0 := by
  simp [LinearProgram.feasible, Pi.le_def, Fin.forall_fin_one]

-- Maximising the negative of the coordinate gives a boundary optimum on the unbounded ray.
example : IsMaxOn (rayLP (-1)).objective (rayLP (-1)).feasible 0 ∧
    (0 : Fin 1 → ℝ) ∈ frontier (rayLP (-1)).feasible := by
  have hx := (mem_feasible_rayLP (-1) 0).2 (by simp)
  have hlocal : IsLocalMaxOn (rayLP (-1)).objective (rayLP (-1)).feasible 0 := by
    apply IsMaxOn.isLocalMaxOn
    refine isMaxOn_iff.2 fun y hy => ?_
    simpa [LinearProgram.objective, rayLP, dotProduct] using
      neg_nonpos.mpr ((mem_feasible_rayLP (-1) y).1 hy)
  have hc : (rayLP (-1)).c ≠ 0 := by
    intro h
    simpa [rayLP] using congrFun h 0
  obtain ⟨hmax, hfrontier⟩ := lp_maximum_principle (rayLP (-1)) 0 (_hx := hx) (_hlocal := hlocal)
  exact ⟨hmax, hfrontier hc⟩

-- With zero objective, an interior point can be a global optimum.
example : IsMaxOn (rayLP 0).objective (rayLP 0).feasible 1 ∧
    (1 : Fin 1 → ℝ) ∈ interior (rayLP 0).feasible := by
  have hx := (mem_feasible_rayLP 0 1).2 (by simp)
  have hlocal : IsLocalMaxOn (rayLP 0).objective (rayLP 0).feasible 1 := by
    have hobjective : (rayLP 0).objective = fun _ => 0 := by
      funext y
      simp [LinearProgram.objective, rayLP, dotProduct]
    rw [hobjective]
    exact isLocalMaxOn_const
  have hopen : IsOpen {x : Fin 1 → ℝ | 0 < x 0} :=
    isOpen_lt continuous_const (continuous_apply 0)
  refine ⟨(lp_maximum_principle (rayLP 0) 1 hx hlocal).1, mem_interior_iff_mem_nhds.2 ?_⟩
  exact Filter.mem_of_superset (hopen.mem_nhds (show 0 < (1 : ℝ) from zero_lt_one))
    fun x hy => (mem_feasible_rayLP 0 x).2 (le_of_lt hy)

end MathlibExtTest.Geometry.LinearProgrammingMaximumPrinciple
