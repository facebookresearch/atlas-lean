/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.BoxReactorSteadyState

/-!
# Box-reactor steady-state checks

Concrete consumers of
`PhyslibExt.EarthScience.BoxReactorSteadyState`: the two-species
conversion steady state with `c = [2, 2]`, `cIn = [3, 1]`, unit rate,
whose `(1, 1)`-weighted totals are both `4`, and the zero-rate boundary
where `c = cIn`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.BoxReactorSteadyState`
-/

/-- The public statement shape of steady-state elemental conservation. -/
example {n m : ℕ} (S : Fin n → Fin m → ℝ) (l : Fin n → ℝ)
    (c cIn : Fin n → ℝ) (r : Fin m → ℝ) {F V : ℝ} (hF : 0 < F) (hV : 0 < V)
    (hnull : ∀ j, ∑ i, l i * S i j = 0)
    (hsteady : ∀ i, (F / V) * (cIn i - c i) + ∑ j, S i j * r j = 0) :
    ∑ i, l i * c i = ∑ i, l i * cIn i :=
  EarthScience.box_reactor_steady_elemental_conservation S l c cIn r hF hV hnull hsteady

/-- Conversion steady state: weighted totals are both `4`. -/
example :
    ∑ i : Fin 2, (1 : ℝ) * (if i = 0 then (2 : ℝ) else 2) =
      ∑ i : Fin 2, (1 : ℝ) * (if i = 0 then (3 : ℝ) else 1) := by
  have hnull : ∀ j : Fin 1, ∑ i : Fin 2, (1 : ℝ) * (if i = 0 then (-1 : ℝ) else 1) = 0 := by
    intro j
    norm_num [Fin.sum_univ_two]
  have hsteady : ∀ i : Fin 2, ((1 : ℝ) / 1) *
      ((if i = 0 then (3 : ℝ) else 1) - (if i = 0 then (2 : ℝ) else 2)) +
      ∑ j : Fin 1, (if i = 0 then (-1 : ℝ) else 1) * (1 : ℝ) = 0 := by
    intro i
    fin_cases i <;> norm_num [Fin.sum_univ_one]
  have h := EarthScience.box_reactor_steady_elemental_conservation
    (fun i _ => if i = 0 then (-1 : ℝ) else 1) (fun _ => (1 : ℝ))
    (fun i => if i = 0 then (2 : ℝ) else 2) (fun i => if i = 0 then (3 : ℝ) else 1)
    (fun _ => (1 : ℝ)) (by norm_num) (by norm_num) hnull hsteady
  exact h

/-- Boundary case: zero rate forces `c = cIn`, so totals agree. -/
example :
    ∑ i : Fin 2, (1 : ℝ) * (if i = 0 then (3 : ℝ) else 1) =
      ∑ i : Fin 2, (1 : ℝ) * (if i = 0 then (3 : ℝ) else 1) := by
  have hnull : ∀ j : Fin 1, ∑ i : Fin 2, (1 : ℝ) * (if i = 0 then (-1 : ℝ) else 1) = 0 := by
    intro j
    norm_num [Fin.sum_univ_two]
  have hsteady : ∀ i : Fin 2, ((1 : ℝ) / 1) *
      ((if i = 0 then (3 : ℝ) else 1) - (if i = 0 then (3 : ℝ) else 1)) +
      ∑ j : Fin 1, (if i = 0 then (-1 : ℝ) else 1) * (0 : ℝ) = 0 := by
    intro i
    fin_cases i <;> norm_num [Fin.sum_univ_one]
  have h := EarthScience.box_reactor_steady_elemental_conservation
    (fun i _ => if i = 0 then (-1 : ℝ) else 1) (fun _ => (1 : ℝ))
    (fun i => if i = 0 then (3 : ℝ) else 1) (fun i => if i = 0 then (3 : ℝ) else 1)
    (fun _ => (0 : ℝ)) (by norm_num) (by norm_num) hnull hsteady
  exact h
