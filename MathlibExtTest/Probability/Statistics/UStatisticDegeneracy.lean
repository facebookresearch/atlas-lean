/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.UStatisticDegeneracy

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Positive case: coordinate evaluation under the product law keeps nonzero
variance (the shape of a nondegenerate linear first projection). -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {X : Fin 1 → α → ℝ}
    (hpos : Var[X 0; μ] ≠ 0) :
    Var[(fun y : Fin 1 → α => X 0 (y 0)); Measure.pi fun _ : Fin 1 => μ] ≠ 0 := by
  let e : (Fin 1 → α) ≃ᵐ α :=
    { toFun := fun y => y 0
      invFun := fun a _ => a
      left_inv := fun y => by
        funext i
        exact congrArg y (Subsingleton.elim _ _)
      right_inv := fun _ => rfl
      measurable_toFun := measurable_pi_apply 0
      measurable_invFun := Measurable.of_eval (fun _ => measurable_id) }
  have hmap : Measure.map e (Measure.pi fun _ => μ) = μ := by
    have hpres := measurePreserving_eval (μ := fun _ : Fin 1 => μ) (0 : Fin 1)
    have heq : ⇑e = Function.eval (0 : Fin 1) := rfl
    rw [heq]
    exact hpres.map_eq
  have hvar := variance_map_equiv (X 0) e (μ := Measure.pi fun _ => μ)
  rw [hmap] at hvar
  have hfun : (fun y : Fin 1 → α => X 0 (y 0)) = (X 0) ∘ e := rfl
  rw [hfun, ← hvar]
  exact hpos

/-- Boundary case: a constant kernel is degenerate with zero variance. -/
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (c : ℝ) :
    Var[hoeffdingProj μ (fun _ : Fin 1 → α => c) 1;
      Measure.pi fun _ : Fin 1 => μ] = 0 := by
  have hproj : hoeffdingProj μ (fun _ : Fin 1 → α => c) 1 = fun _ => c := by
    funext y
    simp [hoeffdingProj]
  rw [hproj, variance_eq_integral aemeasurable_const]
  simp

/-- Degenerate convention: `m > n` is not degeneracy; the U-statistic is `0`
by the empty-sum convention. -/
example {α : Type*} [MeasurableSpace α] {m n : ℕ} (hmn : n < m)
    (h : (Fin m → α) → ℝ) (x : Fin n → α) :
    uStatistic h x = 0 := by
  have hz : n.descFactorial m = 0 := Nat.descFactorial_of_lt hmn
  simp [uStatistic, hz]
