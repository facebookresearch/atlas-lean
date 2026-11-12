/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainPoincare

open MathlibExt.Probability.MarkovChainPoincare

/-- Boundary check: at time `0` the decay bound is the trivial
identity factor `1`. -/
example {α : Type*} [Fintype α] {K : α → α → ℝ} {π : α → ℝ} {gap : ℝ}
    (hgap : 0 < gap ∧ gap ≤ 1)
    (hK_nonneg : ∀ x y, 0 ≤ K x y) (hK_sum : ∀ x, ∑ y, K x y = 1)
    (hπ_nonneg : ∀ x, 0 ≤ π x) (hπ_sum : ∑ x, π x = 1)
    (hstat : ∀ y, ∑ x, π x * K x y = π y)
    (hcontract : ∀ f : α → ℝ, piVar π (applyK K f) ≤ (1 - gap) ^ 2 * piVar π f)
    (f : α → ℝ) :
    piVar π (applyKIter K 0 f) ≤ ((1 - gap) ^ 2) ^ 0 * piVar π f :=
  piVar_decay hgap hK_nonneg hK_sum hπ_nonneg hπ_sum hstat hcontract f 0

/-- The zero-step evolution is the identity. -/
example {α : Type*} [Fintype α] (K : α → α → ℝ) (f : α → ℝ) :
    applyKIter K 0 f = f := rfl

/-- The variance of a constant function is zero, for the uniform
distribution on `Fin 2`. -/
private theorem piVar_const_fin2 (c : ℝ) :
    piVar (fun _ : Fin 2 => (1 : ℝ) / 2) (fun _ => c) = 0 := by
  simp [piVar, MathlibExt.Probability.FiniteProbability.variance,
    MathlibExt.Probability.FiniteProbability.expectation]

/-- On `Fin 2`, with uniform `π` and `f = ![0, 1]`, the variance is `1 / 4`. -/
example :
    piVar (fun _ : Fin 2 => (1 : ℝ) / 2) ![0, 1] = 1 / 4 := by
  simp [piVar, MathlibExt.Probability.FiniteProbability.variance,
    MathlibExt.Probability.FiniteProbability.expectation, Fin.sum_univ_two]
  norm_num

/-- On `Fin 2`, the collapsing kernel `K x y = 1 / 2` sends every
function to the constant `(g 0 + g 1) / 2`. -/
private theorem applyK_collapse (g : Fin 2 → ℝ) :
    applyK (fun _ _ : Fin 2 => (1 : ℝ) / 2) g = fun _ => (g 0 + g 1) / 2 := by
  funext x
  rw [applyK_apply]
  simp [Fin.sum_univ_two]
  ring

/-- Nonzero-step check: after one step of the collapsing kernel,
the variance of `![0, 1]` is `0`, and `piVar_decay` with `gap = 1`
gives the bound `0`. -/
example :
    piVar (fun _ : Fin 2 => (1 : ℝ) / 2)
        (applyKIter (fun _ _ : Fin 2 => (1 : ℝ) / 2) 1 ![0, 1]) = 0 := by
  have hstep : applyKIter (fun _ _ : Fin 2 => (1 : ℝ) / 2) 1 ![0, 1] =
      fun _ => ((![0, 1] : Fin 2 → ℝ) 0 + (![0, 1] : Fin 2 → ℝ) 1) / 2 := by
    show applyK (fun _ _ : Fin 2 => (1 : ℝ) / 2) ![0, 1] = _
    exact applyK_collapse ![0, 1]
  rw [hstep]
  have hval : ((![0, 1] : Fin 2 → ℝ) 0 + (![0, 1] : Fin 2 → ℝ) 1) / 2 = 1 / 2 := by
    norm_num
  rw [hval]
  exact piVar_const_fin2 (1 / 2)

example :
    piVar (fun _ : Fin 2 => (1 : ℝ) / 2)
        (applyKIter (fun _ _ : Fin 2 => (1 : ℝ) / 2) 1 ![0, 1])
      ≤ ((1 - (1 : ℝ)) ^ 2) ^ 1 *
        piVar (fun _ : Fin 2 => (1 : ℝ) / 2) ![0, 1] := by
  apply piVar_decay (K := fun _ _ : Fin 2 => (1 : ℝ) / 2)
    (π := fun _ : Fin 2 => (1 : ℝ) / 2) (gap := 1)
  · exact ⟨by norm_num, by norm_num⟩
  · intro x y; norm_num
  · intro x
    simp
  · intro x; norm_num
  · simp
  · intro y
    simp
  · intro g
    rw [applyK_collapse, piVar_const_fin2]
    simp
