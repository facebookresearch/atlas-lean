/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real










namespace StatMech.FrontierA


def quantumIsingSpinSign (s : Bool) : ℝ :=
  if s then 1 else -1

@[simp] theorem quantumIsingSpinSign_false :
    quantumIsingSpinSign false = -1 := rfl

@[simp] theorem quantumIsingSpinSign_true :
    quantumIsingSpinSign true = 1 := rfl

theorem quantumIsingSpinSign_mul_self (s : Bool) :
    quantumIsingSpinSign s * quantumIsingSpinSign s = 1 := by
  cases s <;> norm_num [quantumIsingSpinSign]

theorem quantumIsingSpinSign_mul_eq_neg_one_of_ne
    {s t : Bool} (hst : s ≠ t) :
    quantumIsingSpinSign s * quantumIsingSpinSign t = -1 := by
  cases s <;> cases t <;> simp_all [quantumIsingSpinSign]



noncomputable def quantumIsingTrotterKernel
    (beta h : ℝ) (n : ℕ) (s t : Bool) : ℝ :=
  if s = t then 1 else beta * h / (2 * n)


noncomputable def quantumIsingVerticalCoupling
    (beta h : ℝ) (n : ℕ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (beta * h / (2 * n))



theorem quantumIsingTrotterKernel_eq_verticalWeight
    (beta h : ℝ) (n : ℕ) (s t : Bool)
    (hpos : 0 < beta * h / (2 * n)) :
    quantumIsingTrotterKernel beta h n s t =
      Real.exp (-quantumIsingVerticalCoupling beta h n) *
        Real.exp
          (quantumIsingVerticalCoupling beta h n *
            (quantumIsingSpinSign s * quantumIsingSpinSign t)) := by
  by_cases hst : s = t
  · subst t
    simp only [quantumIsingTrotterKernel,
      quantumIsingSpinSign_mul_self, mul_one]
    rw [← Real.exp_add]
    simp
  · rw [quantumIsingTrotterKernel, if_neg hst,
      quantumIsingSpinSign_mul_eq_neg_one_of_ne hst]
    rw [← Real.exp_add]
    have hcoupling :
        -quantumIsingVerticalCoupling beta h n +
            quantumIsingVerticalCoupling beta h n * -1 =
          Real.log (beta * h / (2 * n)) := by
      simp [quantumIsingVerticalCoupling]
      ring
    rw [hcoupling, Real.exp_log hpos]

end StatMech.FrontierA
