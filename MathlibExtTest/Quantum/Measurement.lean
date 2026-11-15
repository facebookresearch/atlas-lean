/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.Measurement

@[expose] public section

/-- Splitting a vector into itself and zero: only one outcome has weight. -/
example (x : ℂ) : ∑ i : Fin 2, ‖(fun j : Fin 2 => if j = 0 then x else 0) i‖ ^ 2 = ‖x‖ ^ 2 :=
  measurement_prob_sum (fun (j : Fin 2) (v : ℂ) => if j = 0 then v else 0) x
    (by simp) (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)

/-- The same split of a unit vector gives total probability 1. -/
example : ∑ i : Fin 2, ‖(fun j : Fin 2 => if j = 0 then (1 : ℂ) else 0) i‖ ^ 2 = 1 :=
  measurement_prob_sum_one (fun (j : Fin 2) (v : ℂ) => if j = 0 then v else 0) 1
    (by simp) (by simp) (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)

end
