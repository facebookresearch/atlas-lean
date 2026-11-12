/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainPoincare

open MathlibExt.Probability.FiniteProbability
open MathlibExt.Probability.MarkovChainPoincare

/-- The zero-step bound needs only the one-step inequality, not
stochasticity, stationarity, or a range restriction on the gap. -/
example {α : Type*} [Fintype α] {K : Matrix α α ℝ} {π : α → ℝ} {gap : ℝ}
    (hcontract : ∀ f : α → ℝ,
      variance π (K.mulVec f) ≤ (1 - gap) ^ 2 * variance π f)
    (f : α → ℝ) :
    variance π ((Matrix.mulVec K)^[0] f) ≤ ((1 - gap) ^ 2) ^ 0 * variance π f :=
  variance_iterate_le (sq_nonneg _) hcontract f 0

/-- The zero-step evolution is the identity. -/
example {α : Type*} [Fintype α] (K : Matrix α α ℝ) (f : α → ℝ) :
    (Matrix.mulVec K)^[0] f = f := rfl

/-- Constants have zero variance for the uniform weights on `Fin 2`. -/
private theorem variance_const_fin2 (c : ℝ) :
    variance (fun _ : Fin 2 => (1 : ℝ) / 2) (fun _ => c) = 0 := by
  simp [variance, expectation]

/-- The initial nonconstant function has strictly positive variance. -/
example : variance (fun _ : Fin 2 => (1 : ℝ) / 2) ![0, 1] = 1 / 4 := by
  simp [variance, expectation, Fin.sum_univ_two]
  norm_num

/-- The averaging kernel sends each function to its arithmetic mean. -/
private theorem mulVec_collapse (g : Fin 2 → ℝ) :
    Matrix.mulVec (fun _ _ : Fin 2 => (1 : ℝ) / 2) g =
      fun _ => (g 0 + g 1) / 2 := by
  funext x
  change (∑ y : Fin 2, (1 / 2 : ℝ) * g y) = (g 0 + g 1) / 2
  simp [Fin.sum_univ_two]
  ring

/-- After one step the nonconstant initial function has zero variance. -/
example : variance (fun _ : Fin 2 => (1 : ℝ) / 2)
    ((Matrix.mulVec (fun _ _ : Fin 2 => (1 : ℝ) / 2))^[1] ![0, 1]) = 0 := by
  rw [Function.iterate_one, mulVec_collapse]
  exact variance_const_fin2 _

/-- The generic iteration theorem gives the zero-factor bound at a nonzero time. -/
example : variance (fun _ : Fin 2 => (1 : ℝ) / 2)
    ((Matrix.mulVec (fun _ _ : Fin 2 => (1 : ℝ) / 2))^[1] ![0, 1]) ≤
      (0 : ℝ) ^ 1 * variance (fun _ : Fin 2 => (1 : ℝ) / 2) ![0, 1] := by
  apply variance_iterate_le (by norm_num)
  intro g
  rw [mulVec_collapse, variance_const_fin2]
  simp
