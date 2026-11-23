/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RoulettePathMass
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

@[expose] public section

/-!
Boundary examples for the finite-level Russian-roulette path-mass identities:
immediate stop, never stop, rare stop, mass conservation, and two states.
-/

open RussianRoulette

-- One state, `q = 1`: immediate stop.
example : stoppedMass (fun _ : Fin 1 => (1 : ℝ))
    (stepKernel (fun _ : Fin 1 => (1 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 0 = 1 := by
  simp only [stoppedMass]
  refine (Fintype.sum_eq_single (fun _ => (0 : Fin 1)) ?_).trans ?_
  · intro x hx
    exfalso
    exact hx (Subsingleton.elim _ _)
  · simp [completedWeight, survivalWeight]

example : survivalMass
    (stepKernel (fun _ : Fin 1 => (1 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 1 = 0 := by
  simp only [survivalMass]
  refine (Fintype.sum_eq_single (fun _ => (0 : Fin 1)) ?_).trans ?_
  · intro x hx
    exfalso
    exact hx (Subsingleton.elim _ _)
  · simp [survivalWeight, stepKernel]

-- One state, `q = 0`: never stops; raw weights.
example : survivalMass
    (stepKernel (fun _ : Fin 1 => (0 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 1 = 1 := by
  simp only [survivalMass]
  refine (Fintype.sum_eq_single (fun _ => (0 : Fin 1)) ?_).trans ?_
  · intro x hx
    exfalso
    exact hx (Subsingleton.elim _ _)
  · simp [survivalWeight, stepKernel]

example : survivalMass
    (stepKernel (fun _ : Fin 1 => (0 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 2 = 1 := by
  simp only [survivalMass]
  refine (Fintype.sum_eq_single (fun _ => (0 : Fin 1)) ?_).trans ?_
  · intro x hx
    exfalso
    exact hx (Subsingleton.elim _ _)
  · simp [survivalWeight, stepKernel]

example : stoppedMass (fun _ : Fin 1 => (0 : ℝ))
    (stepKernel (fun _ : Fin 1 => (0 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 1 = 0 := by
  simp only [stoppedMass]
  refine (Fintype.sum_eq_single (fun _ => (0 : Fin 1)) ?_).trans ?_
  · intro x hx
    exfalso
    exact hx (Subsingleton.elim _ _)
  · simp [completedWeight, survivalWeight, stepKernel]

-- One state, `q = 1/100`: geometric survival weight and length-sum bound.
example : survivalMass
    (stepKernel (fun _ : Fin 1 => (1/100 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 2
    = (99/100 : ℝ)^2 := by
  simp only [survivalMass]
  refine (Fintype.sum_eq_single (fun _ => (0 : Fin 1)) ?_).trans ?_
  · intro x hx
    exfalso
    exact hx (Subsingleton.elim _ _)
  · norm_num [survivalWeight, stepKernel]

example : (∑ k ∈ Finset.range 2, survivalMass
    (stepKernel (fun _ : Fin 1 => (1/100 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 k)
    ≤ 100 := by
  have h := sum_survivalMass_le (fun _ : Fin 1 => (1/100 : ℝ))
    (fun _ _ : Fin 1 => (1 : ℝ)) (1/100) (by norm_num)
    (fun a => ⟨by norm_num, by norm_num⟩)
    (fun a b => zero_le_one) (fun a => by simp) 0 2
  calc (∑ k ∈ Finset.range 2, survivalMass
        (stepKernel (fun _ : Fin 1 => (1/100 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 k)
        ≤ 1 / ((1/100 : ℝ)) := h
    _ = 100 := by norm_num

-- One state, `q = 1/2`: mass conservation at `n = 2`.
example : ((∑ k ∈ Finset.range 2, stoppedMass (fun _ : Fin 1 => (1/2 : ℝ))
    (stepKernel (fun _ : Fin 1 => (1/2 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 k)
    + survivalMass
      (stepKernel (fun _ : Fin 1 => (1/2 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))) 0 2)
    = 1 := by
  apply sum_stoppedMass_add_survival
  intro j
  norm_num [stepKernel]

-- Two states with explicit survival-kernel values via `stepKernel` inputs.
example : survivalMass
    (stepKernel (fun _ : Fin 2 => (1/2 : ℝ)) (fun _ _ : Fin 2 => (1/2 : ℝ))) 0 1
    = 1/2 := by
  simp only [survivalMass]
  have hexp : ∀ f : (Fin 2 → Fin 2) → ℝ,
      ∑ x, f x = f ![0, 0] + f ![0, 1] + (f ![1, 0] + f ![1, 1]) := by
    intro f
    have h := (Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm f).symm
    rw [Fintype.sum_prod_type] at h
    simp only [Fin.sum_univ_two, finTwoArrowEquiv_symm_apply] at h
    exact h
  rw [hexp]
  norm_num [survivalWeight, stepKernel]

end
public section
