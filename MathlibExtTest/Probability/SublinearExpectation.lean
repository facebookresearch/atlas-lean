/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SublinearExpectation

@[expose] public section

open MathlibExt.Probability.SublinearExpectation

namespace MathlibExtTest.Probability.SublinearExpectation

/-- The worst-case expectation on two scenarios, `E[X] = max (X 0) (X 1)` (Peng,
arXiv:1002.4546v1, Chapter I, Exercise 1.9), is a sublinear expectation that is not linear. -/
theorem isSublinearExpectation_max :
    IsSublinearExpectation (⊤ : Submodule ℝ (Fin 2 → ℝ)) (fun X ↦ max (X 0) (X 1)) where
  const_mem _ := Submodule.mem_top
  mono X _ Y _ hYX := max_le_max (hYX 0) (hYX 1)
  const c := max_self c
  subadd X _ Y _ := max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
    (add_le_add (le_max_right _ _) (le_max_right _ _))
  pos_hom X _ c hc := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (mul_max_of_nonneg _ _ hc).symm

/-- Non-vacuity of the finite representation: `max (X 0) (X 1)` is attained by a probability
vector dominated by the worst-case expectation. -/
example (X : Fin 2 → ℝ) :
    IsGreatest {r | ∃ q : Fin 2 → ℝ, (∀ ω, 0 ≤ q ω) ∧ ∑ ω, q ω = 1 ∧
      (∀ Y : Fin 2 → ℝ, ∑ ω, q ω * Y ω ≤ max (Y 0) (Y 1)) ∧ r = ∑ ω, q ω * X ω}
      (max (X 0) (X 1)) :=
  isSublinearExpectation_max.isGreatest_finite X

/-- The worst-case expectation is not linear, so the representation is not a triviality:
`E[X] + E[-X] > 0` for `X = (1, -1)`. -/
example : max ((fun i : Fin 2 ↦ if i = 0 then (1 : ℝ) else -1) 0)
    ((fun i : Fin 2 ↦ if i = 0 then (1 : ℝ) else -1) 1) +
    max (-(fun i : Fin 2 ↦ if i = 0 then (1 : ℝ) else -1) 0)
      (-(fun i : Fin 2 ↦ if i = 0 then (1 : ℝ) else -1) 1) = 2 := by
  norm_num

/-- The induced coherent risk measure `ρ(X) = E[-X] = -min (X 0) (X 1)`, and its acceptance set
`{X : min (X 0) (X 1) ≥ 0}`, are coherent. -/
example : IsCoherentRiskMeasure (⊤ : Submodule ℝ (Fin 2 → ℝ))
    (fun X ↦ max ((-X) 0) ((-X) 1)) :=
  isSublinearExpectation_max.isCoherentRiskMeasure

example : IsCoherentAcceptableSet (⊤ : Submodule ℝ (Fin 2 → ℝ))
    {X | X ∈ (⊤ : Submodule ℝ (Fin 2 → ℝ)) ∧ max ((-X) 0) ((-X) 1) ≤ 0} :=
  isSublinearExpectation_max.isCoherentRiskMeasure.isCoherentAcceptableSet

/-- The abstract representation on a vector space: the absolute value on `ℝ` is the maximum of
the linear functionals `x ↦ a x` with `|a| ≤ 1` that it dominates. -/
example (x : ℝ) : IsGreatest {r | ∃ f : ℝ →ₗ[ℝ] ℝ, (∀ y, f y ≤ |y|) ∧ r = f x} |x| :=
  isGreatest_linear_le (fun y : ℝ ↦ |y|) (fun y z ↦ abs_add_le y z)
    (fun c hc y ↦ by rw [smul_eq_mul, abs_mul, abs_of_pos hc]) x

end MathlibExtTest.Probability.SublinearExpectation
