/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.ReactionEvolutionElementalTotals

/-!
# Reaction-evolution elemental-total checks

Concrete consumers of
`PhyslibExt.EarthScience.ReactionEvolutionElementalTotals`: the
two-species conversion trajectory, whose `(1, 1)`-weighted total stays
`2`, and the constant-trajectory boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results. In the
conversion, species `0` (initial amount `2`) turns into species `1`
(initial amount `0`) at unit rate, so the total is `2` at every time.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.ReactionEvolutionElementalTotals`
-/

/-- The public statement shape of total preservation. -/
example {n m : ℕ} (S : Fin n → Fin m → ℝ) (l : Fin n → ℝ)
    (c : ℝ → Fin n → ℝ) (rate : (Fin n → ℝ) → Fin m → ℝ) (t : ℝ)
    (hnull : ∀ j, ∑ i, l i * S i j = 0)
    (hode : ∀ i, ∀ s : ℝ, HasDerivAt (fun t => c t i) (∑ j, S i j * rate (c s) j) s) :
    ∑ i, l i * c t i = ∑ i, l i * c 0 i :=
  EarthScience.reaction_evolution_preserves_elemental_total S l c rate t hnull hode

/-- Conversion trajectory: total stays `2` at every time. -/
example (t : ℝ) :
    ∑ i : Fin 2, (1 : ℝ) * (if i = 0 then 2 - t else t) =
      ∑ i : Fin 2, (1 : ℝ) * (if i = 0 then (2 : ℝ) - 0 else 0) := by
  have hode : ∀ i : Fin 2, ∀ s : ℝ, HasDerivAt (fun u => if i = 0 then 2 - u else u)
      (∑ _j : Fin 1, (if i = 0 then (-1 : ℝ) else 1) * (1 : ℝ)) s := by
    exact Fin.forall_fin_two.mpr ⟨fun s => by
      simp only [Fin.sum_univ_one]
      simpa using (HasDerivAt.const_sub (2 : ℝ) (hasDerivAt_id' s)),
      fun s => by
      simp only [Fin.sum_univ_one]
      simpa using (hasDerivAt_id' s)⟩
  have h := EarthScience.reaction_evolution_preserves_elemental_total
    (fun i _ => if i = 0 then (-1 : ℝ) else 1) (fun _ => (1 : ℝ))
    (fun u i => if i = 0 then 2 - u else u) (fun _ _ => (1 : ℝ)) t
    (fun j => by norm_num [Fin.sum_univ_two]) hode
  exact h

/-- Boundary case: a constant trajectory trivially preserves its total. -/
example (t : ℝ) :
    ∑ _i : Fin 2, (1 : ℝ) * (1 : ℝ) = ∑ _i : Fin 2, (1 : ℝ) * (1 : ℝ) := by
  have hode : ∀ _i : Fin 2, ∀ s : ℝ, HasDerivAt (fun _ => (1 : ℝ))
      (∑ _j : Fin 1, (0 : ℝ) * (0 : ℝ)) s := by
    intro _i _s
    simpa using (hasDerivAt_const _s (1 : ℝ))
  have h := EarthScience.reaction_evolution_preserves_elemental_total
    (fun _ : Fin 2 => fun _ : Fin 1 => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) t
    (fun _j => by simp) hode
  exact h
