/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.Replicator.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Smoke tests for `MathlibExt.Dynamics.Replicator.Basic`, imported on its own, without the
`Domains` theory built on it: the mean fitness of a two-strategy state and its matrix-game form, a
rest point and a state that is not one, the constant solution at a rest point, and a strictly
dominant strategy as a Nash equilibrium and an evolutionarily stable state, against a strategy
that is neither. -/

namespace MathlibExtTest.Dynamics.Replicator.Basic

open Matrix MathlibExt.Biology.Dynamics.Replicator

/-- **Constant fitness.** Strategy `0` earns `1` and strategy `1` earns `0` in every state. -/
noncomputable def fit : (Fin 2 → ℝ) → Fin 2 → ℝ := fun _ => ![1, 0]

/-- **Mean fitness of the even mix.** Half the population earns `1`, half earns `0`. -/
example : meanFitness fit ![1 / 2, 1 / 2] = 1 / 2 := by
  norm_num [meanFitness, fit, Fin.sum_univ_two]

/-- **Matrix-game mean fitness.** For the fitness `x ↦ A x`, `meanFitness` is `x · A x` by
definition, as the module documentation says. -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    meanFitness (fun z => A *ᵥ z) x = x ⬝ᵥ (A *ᵥ x) :=
  rfl

/-- **A vertex is a rest point.** The pure state of strategy `0` earns the mean fitness. -/
theorem isRestPoint_vertex : IsRestPoint fit ![1, 0] := by
  intro i
  fin_cases i <;> norm_num [meanFitness, fit, Fin.sum_univ_two]

/-- **The even mix is not a rest point.** Strategy `0` earns `1` against a mean of `1 / 2`. -/
example : ¬ IsRestPoint fit ![1 / 2, 1 / 2] := by
  intro h
  have h0 := h 0
  norm_num [meanFitness, fit, Fin.sum_univ_two] at h0

/-- **Constant solutions at rest points.** For any fitness `f`, the constant trajectory at a rest
point of `f` solves the replicator equation. This is `isSolution_const` of
`Domains.Biology.Dynamics.Replicator`, proved here from the foundation's definitions alone. -/
theorem isSolution_const {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hx : IsRestPoint f x) : IsSolution f (fun _ => x) where
  hasDerivAt i t _ := by
    simpa [hx i] using hasDerivAt_const t (x i)

example : IsSolution fit (fun _ => ![1, 0]) :=
  isSolution_const isRestPoint_vertex

/-- **A dominance game.** Strategy `0` earns `1` against every strategy and strategy `1` earns
`0`. -/
def dom : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]

/-- **Payoff against the pure state of strategy `0`.** A mixed strategy `q` earns `q 0`. -/
theorem dotProduct_dom_vertex (q : Fin 2 → ℝ) : q ⬝ᵥ (dom *ᵥ ![1, 0]) = q 0 := by
  simp [dom, dotProduct, mulVec, Fin.sum_univ_two]

/-- **The pure state of strategy `0` is a mixed strategy.** -/
theorem vertex_mem_simplex :
    (∀ i, 0 ≤ (![1, 0] : Fin 2 → ℝ) i) ∧ ∑ i, (![1, 0] : Fin 2 → ℝ) i = 1 :=
  ⟨fun i => by fin_cases i <;> norm_num, by norm_num [Fin.sum_univ_two]⟩

/-- **The dominant strategy is a Nash equilibrium.** -/
example : IsNash dom ![1, 0] := by
  unfold IsNash
  refine ⟨vertex_mem_simplex, ?_⟩
  rintro q ⟨hq, hq1⟩
  rw [dotProduct_dom_vertex, dotProduct_dom_vertex]
  rw [Fin.sum_univ_two] at hq1
  norm_num
  linarith [hq 1]

/-- **The dominant strategy is evolutionarily stable.** Every other mixed strategy earns strictly
less against it. -/
example : IsESS dom ![1, 0] := by
  unfold IsESS
  refine ⟨vertex_mem_simplex, ?_⟩
  rintro q ⟨hq, hq1⟩ hne
  left
  rw [dotProduct_dom_vertex, dotProduct_dom_vertex]
  rw [Fin.sum_univ_two] at hq1
  norm_num
  by_contra hle
  have h1 : 1 ≤ q 0 := not_lt.mp hle
  refine hne (funext fun i => ?_)
  fin_cases i <;> simp <;> linarith [hq 0, hq 1]

/-- **The dominated strategy is not a Nash equilibrium.** Switching to strategy `0` earns `1`
instead of `0`. -/
example : ¬ IsNash dom ![0, 1] := by
  intro h
  unfold IsNash at h
  have := h.2 ![1, 0] vertex_mem_simplex
  norm_num [dom, dotProduct, mulVec, Fin.sum_univ_two] at this

end MathlibExtTest.Dynamics.Replicator.Basic
