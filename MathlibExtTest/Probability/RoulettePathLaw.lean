/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RoulettePathLaw
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open RussianRoulette

/-- `listPathWeight` on `[]` is `0`. -/
example (q : Unit → ℝ) (Q : Unit → Unit → ℝ) (i : Unit) :
    listPathWeight q Q i [] = 0 :=
  rfl

/-- `listPathWeight` on a wrong-start singleton is `0`. -/
example (q : Bool → ℝ) (Q : Bool → Bool → ℝ) (i j : Bool) (hne : j ≠ i) :
    listPathWeight q Q i [j] = 0 := by
  have h : listPathWeight q Q i [j]
      = (if j = i then ENNReal.ofReal (q j) else 0) := rfl
  rw [h, ite_eq_right hne]

/-- One-state `q = 1 / 2`: `[x]` has weight `1 / 2`. -/
example : listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) () [()]
    = ENNReal.ofReal (1 / 2 : ℝ) := by
  have h : listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
        (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) ()
        [()]
      = (if () = () then ENNReal.ofReal (1 / 2 : ℝ) else 0) := rfl
  rw [h, ite_eq_left rfl]

/-- One-state `q = 1 / 2`: `[x, x]` has weight `1 / 4`. -/
example : listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) ()
      [(), ()]
    = ENNReal.ofReal (1 / 4 : ℝ) := by
  have h : listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
        (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) ()
        [(), ()]
      = (if () = () then ENNReal.ofReal (((1 : ℝ) - 1 / 2) * 1 * (1 / 2))
        else 0) := rfl
  rw [h, ite_eq_left rfl]
  congr 1
  norm_num

/-- `listCompletedWeight_ofFn` at `n = 1` with concrete values. -/
example : listCompletedWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ)))
      (List.ofFn (fun _ : Fin (1 + 1) => ())) = 1 / 4 := by
  rw [listCompletedWeight_ofFn]
  simp only [completedWeight, survivalWeight, stepKernel, Fin.prod_univ_one]
  norm_num

end
public section
