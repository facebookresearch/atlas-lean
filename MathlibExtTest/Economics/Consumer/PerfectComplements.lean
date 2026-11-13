/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.PerfectComplements

/-!
# Tests for perfect-complements demand

For `u = min x₀ (2 x₁)`, prices `(1, 1)` and wealth `6`, the demand is the kink `(4, 2)` with
utility `4`; it is a Marshallian demand, and the utility is not differentiable there.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Consumer.PerfectComplements

open Matrix MathlibExt.Economics.Consumer

example : leontiefDemand 1 2 ![1, 1] 6 = ![4, 2] := by
  have h0 : (6 : ℝ) / ((1 : ℝ) / 1 + 1 / 2) / 1 = 4 := by norm_num
  have h1 : (6 : ℝ) / ((1 : ℝ) / 1 + 1 / 2) / 2 = 2 := by norm_num
  unfold leontiefDemand
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h0, h1]

example : leontief 1 2 ![4, 2] = 4 := by
  unfold leontief
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [min_self]

example : IsMarshallianDemand (leontief 1 2) twoGoodSet ![1, 1] 6 ![4, 2] := by
  have hp : ∀ i : Fin 2, 0 < (![1, 1] : Fin 2 → ℝ) i := by
    rw [Fin.forall_fin_two]
    constructor <;> simp
  have h := isMarshallianDemand_leontief (a := 1) (b := 2) (p := ![1, 1]) (w := 6)
    (by norm_num) (by norm_num) hp (by norm_num)
  have e : leontiefDemand 1 2 ![1, 1] 6 = ![4, 2] := by
    have h0 : (6 : ℝ) / ((1 : ℝ) / 1 + 1 / 2) / 1 = 4 := by norm_num
    have h1 : (6 : ℝ) / ((1 : ℝ) / 1 + 1 / 2) / 2 = 2 := by norm_num
    unfold leontiefDemand
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h0, h1]
  rw [e] at h
  exact h

example : ¬ DifferentiableAt ℝ (leontief 1 2) ![4, 2] := by
  have hp : ∀ i : Fin 2, 0 < (![1, 1] : Fin 2 → ℝ) i := by
    rw [Fin.forall_fin_two]
    constructor <;> simp
  have h := not_differentiableAt_leontief_leontiefDemand (a := 1) (b := 2)
    (p := ![1, 1]) (w := 6) (by norm_num) (by norm_num) hp (by norm_num)
  have e : leontiefDemand 1 2 ![1, 1] 6 = ![4, 2] := by
    have h0 : (6 : ℝ) / ((1 : ℝ) / 1 + 1 / 2) / 1 = 4 := by norm_num
    have h1 : (6 : ℝ) / ((1 : ℝ) / 1 + 1 / 2) / 2 = 2 := by norm_num
    unfold leontiefDemand
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h0, h1]
  rw [e] at h
  exact h

end MathlibExtTest.Economics.Consumer.PerfectComplements
