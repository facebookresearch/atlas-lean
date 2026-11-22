/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.MPC.FiniteHorizon
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set ControlTheory.MPC

-- Scalar box example: `f x u = x + u`, inputs in `[-1, 1]`, stage cost
-- `x² + u²`, terminal cost `x²`, `x₀ = 1`, horizon `1`, finite controls
-- `u : Fin 1 → ℝ`. The theorem's minimizer has `u 0 = -1/2` and cost
-- `3/2` (minimize `1 + u² + (1 + u)²`).
example : ∃ u : Fin 1 → ℝ, Feasible (fun x u : ℝ => x + u) 1 (Set.Icc (-1) 1)
      Set.univ Set.univ 1 u ∧
    Cost (fun x u : ℝ => x + u) (fun x u : ℝ => x ^ 2 + u ^ 2)
      (fun x : ℝ => x ^ 2) 1 1 u
      = 3 / 2 ∧ u 0 = -1 / 2 := by
  have hcost : ∀ v : Fin 1 → ℝ,
      Cost (fun x u : ℝ => x + u) (fun x u : ℝ => x ^ 2 + u ^ 2)
        (fun x : ℝ => x ^ 2) 1 1 v
        = 2 * (v 0 + 1 / 2) ^ 2 + 3 / 2 := by
    intro v
    simp [Cost, traj]
    ring
  have hwit : Feasible (fun x u : ℝ => x + u) 1 (Set.Icc (-1) 1) Set.univ
      Set.univ 1 (fun _ => -1 / 2) :=
    ⟨fun _ => by constructor <;> norm_num, fun _ _ => trivial, trivial⟩
  obtain ⟨u, hufeas, huopt⟩ := exists_optimal
    (f := fun x u : ℝ => x + u) (Us := Set.Icc (-1) 1) (Xs := Set.univ)
    (Xf := Set.univ) (ℓ := fun x u : ℝ => x ^ 2 + u ^ 2) (V := fun x : ℝ => x ^ 2)
    (by exact continuous_fst.add continuous_snd) isCompact_Icc isClosed_univ
    isClosed_univ
    (by exact (continuous_fst.pow 2).add (continuous_snd.pow 2))
    (continuous_id.pow 2) 1 1 ⟨fun _ => -1 / 2, hwit⟩
  have hle : Cost (fun x u : ℝ => x + u) (fun x u : ℝ => x ^ 2 + u ^ 2)
      (fun x : ℝ => x ^ 2) 1 1 u ≤ 3 / 2 := by
    have h := huopt (fun _ => -1 / 2) hwit
    simp only [hcost] at h
    rw [hcost]
    norm_num at h
    linarith
  have hge : 3 / 2 ≤ Cost (fun x u : ℝ => x + u) (fun x u : ℝ => x ^ 2 + u ^ 2)
      (fun x : ℝ => x ^ 2) 1 1 u := by
    rw [hcost]
    have := sq_nonneg (u 0 + 1 / 2)
    linarith
  have heq := le_antisymm hle hge
  refine ⟨u, hufeas, heq, ?_⟩
  have h2 : 2 * (u 0 + 1 / 2) ^ 2 = 0 := by
    have h3 := hcost u
    rw [heq] at h3
    linarith
  have h4 : u 0 + 1 / 2 = 0 := by
    have h5 : (u 0 + 1 / 2) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h5
  linarith

-- The standard-form reading at `N = 1`: a trajectory with `x₀ ∈ Xs` and
-- `x₁ ∈ Xf \ Xs` is feasible (the state constraint applies to `x₀`, the
-- terminal constraint to `x₁`).
example : Feasible (fun _ u : ℝ => u) 0 (Set.Icc (-1) 1) (Set.Iic 0)
    (Set.Ici 0) 1 (fun _ => 1) := by
  refine ⟨fun _ => by constructor <;> norm_num, ?_, ?_⟩
  · intro k hk
    interval_cases k
    show (0 : ℝ) ∈ Set.Iic (0 : ℝ)
    exact Set.mem_Iic.mpr le_rfl
  · show (1 : ℝ) ∈ Set.Ici (0 : ℝ)
    exact Set.mem_Ici.mpr zero_le_one

-- Horizon `0`: the cost collapses to the terminal cost at `x₀`, and
-- feasibility is exactly `x₀ ∈ Xf` (the input conditions are vacuous),
-- even when `Us` is empty.
example {X U : Type*} (f : X → U → X) (ℓ : X → U → ℝ) (V : X → ℝ)
    (x₀ : X) (u : Fin 0 → U) : Cost f ℓ V x₀ 0 u = V x₀ := by
  simp [Cost, traj]

example {X U : Type*} (f : X → U → X) (x₀ : X) (Xs Xf : Set X)
    (u : Fin 0 → U) :
    Feasible f x₀ ∅ Xs Xf 0 u ↔ x₀ ∈ Xf := by
  simp [Feasible, traj]

#print axioms exists_optimal
