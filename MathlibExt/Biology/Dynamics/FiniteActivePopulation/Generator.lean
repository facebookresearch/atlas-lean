/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite active-population generator

The birth-death generator on finitely many active states has nonnegative off-diagonal entries and closed endpoints.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Biology.Dynamics.FiniteActivePopulation.Generator

/-- The birth-death generator on states `Fin (N + 1)`: births at
rate `b i = (N - i) * f i`, deaths at rate `d i = alpha * i`, with
the negative row sum on the diagonal and zero elsewhere. -/
noncomputable def birthDeathGenerator (N : ℕ) (alpha : ℝ) (f : ℕ → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j =>
    if j = i + 1 then ((N : ℝ) - i) * f i
    else if (j : ℕ) + 1 = i then alpha * (i : ℝ)
    else if j = i then -(((N : ℝ) - i) * f i + alpha * (i : ℝ))
    else 0

/-- **Off-diagonal entries are nonnegative.** For `alpha ≥ 0`,
`f i ≥ 0`, and states `i ≤ N`, every off-diagonal entry of the
birth-death generator is nonnegative. -/
theorem birthDeath_offDiag_nonneg (N : ℕ) (alpha : ℝ) (f : ℕ → ℝ)
    (halpha : 0 ≤ alpha) (hf : ∀ i, 0 ≤ f i)
    {i j : Fin (N + 1)} (hij : i ≠ j) :
    0 ≤ birthDeathGenerator N alpha f i j := by
  unfold birthDeathGenerator
  by_cases h1 : j = i + 1
  · simp only [h1, ite_true]
    apply mul_nonneg _ (hf _)
    exact sub_nonneg.mpr (Nat.cast_le.mpr (Fin.is_le i))
  · simp only [h1, ite_false]
    by_cases h2 : (j : ℕ) + 1 = i
    · simp only [h2, ite_true]
      apply mul_nonneg halpha
      exact Nat.cast_nonneg _
    · simp only [h2, ite_false]
      have h3 : ¬(j = i) := fun h => hij h.symm
      simp only [h3, ite_false, le_refl]

/-- **Endpoints close the population.** There is no death from
state `0` and no birth from state `N`: the would-be outward rates
vanish at the endpoints. -/
theorem birthDeath_endpoints (N : ℕ) (alpha : ℝ) (f : ℕ → ℝ) :
    alpha * (0 : ℝ) = 0 ∧ ((N : ℝ) - N) * f N = 0 := by
  exact ⟨mul_zero alpha, by rw [sub_self, zero_mul]⟩


end MathlibExt.Biology.Dynamics.FiniteActivePopulation.Generator
