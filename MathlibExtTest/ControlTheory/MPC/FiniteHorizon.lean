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


-- Shift and append at horizon `1`: dynamics `x + u`, input and state
-- constraints `[-1, 1]`, terminal set `{0}` with feedback `κ x = -x`.
-- From `x₀ = 0` use the feasible zero input `u = 0` as the input to
-- the shift-and-append construction below.
example : Feasible (fun x u : ℝ => x + u) 0 (Set.Icc (-1) 1)
    (Set.Icc (-1) 1) {0} 1 (fun _ => 0) := by
  refine ⟨fun _ => by constructor <;> norm_num, ?_, ?_⟩
  · intro k hk
    interval_cases k
    show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1
    constructor <;> norm_num
  · simp [traj]

-- The shifted sequence at horizon `1` is exactly the terminal feedback
-- at the terminal state.
example (κ : ℝ → ℝ) (u : Fin 1 → ℝ) :
    shiftAppend (fun x u : ℝ => x + u) 0 u κ = fun _ => κ (traj (fun x u : ℝ => x + u) 0 u 1 le_rfl) := by
  funext k
  have hk : k = 0 := by
    have : k.val = 0 := by omega
    exact Fin.ext this
  subst hk
  simp [shiftAppend]


-- Applying `feasible_shift`: the shifted sequence from the feasible
-- zero input is feasible at the successor state `0 + 0 = 0`, with
-- terminal feedback `κ x = -x` on the terminal set `{0}`.
example : Feasible (fun x u : ℝ => x + u) (0 + 0) (Set.Icc (-1) 1)
    (Set.Icc (-1) 1) {0} 1
    (shiftAppend (fun x u : ℝ => x + u) 0 (fun _ => 0) (fun x => -x)) := by
  have hsub : ({0} : Set ℝ) ⊆ Set.Icc (-1) 1 := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    constructor <;> norm_num
  have hκU : ∀ x ∈ ({0} : Set ℝ), (-x) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    simp
  have hκf : ∀ x ∈ ({0} : Set ℝ), x + (-x) ∈ ({0} : Set ℝ) := by
    intro x _
    simp
  have hfeas : Feasible (fun x u : ℝ => x + u) 0 (Set.Icc (-1) 1)
      (Set.Icc (-1) 1) {0} 1 (fun _ => 0) := by
    refine ⟨fun _ => by constructor <;> norm_num, ?_, ?_⟩
    · intro k hk
      interval_cases k
      show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1
      constructor <;> norm_num
    · simp [traj]
  exact feasible_shift (fun x u : ℝ => x + u) 0 (Set.Icc (-1) 1)
    (Set.Icc (-1) 1) ({0} : Set ℝ) le_rfl hsub (fun x => -x) hκU hκf
    (fun _ => 0) hfeas


-- Horizon `2` with nonconstant input: the first shifted entry is the
-- dropped-and-shifted second input, and the last entry is the appended
-- terminal feedback. Dynamics `x + u` over `ℤ`, `u = [1, 2]`,
-- `κ x = 10 * x + 7`: the trajectory is `0, 1, 3`, so the shifted
-- sequence is `[2, κ 3] = [2, 37]` and the shifted trajectory from
-- `x₁ = 1` reaches `3` and then `3 + 37 = 40`.
example : shiftAppend (fun x u : ℤ => x + u) 0
    (fun k => if k.val = 0 then 1 else 2) (fun x => 10 * x + 7) (0 : Fin 2) = 2 := by
  simp [shiftAppend, traj]

example : shiftAppend (fun x u : ℤ => x + u) 0
    (fun k => if k.val = 0 then 1 else 2) (fun x => 10 * x + 7) (1 : Fin 2) = 37 := by
  simp [shiftAppend, traj]

example : traj (fun x u : ℤ => x + u) (0 + 1)
    (shiftAppend (fun x u : ℤ => x + u) 0
      (fun k => if k.val = 0 then 1 else 2) (fun x => 10 * x + 7)) 2 le_rfl = 40 := by
  decide

-- Feasibility at horizon `2` transported by `feasible_shift` itself,
-- with the trivial (full) constraint sets.
example : Feasible (fun x u : ℝ => x + u) (0 + (1 : ℝ)) Set.univ Set.univ
    Set.univ 2 (shiftAppend (fun x u : ℝ => x + u) 0
      (fun k => if k.val = 0 then 1 else 2) (fun x => -x)) := by
  have hfeas : Feasible (fun x u : ℝ => x + u) 0 Set.univ Set.univ
      Set.univ 2 (fun k => if k.val = 0 then (1 : ℝ) else 2) :=
    ⟨fun _ => Set.mem_univ _, fun _ _ => Set.mem_univ _, Set.mem_univ _⟩
  exact feasible_shift (fun x u : ℝ => x + u) 0 Set.univ Set.univ Set.univ
    (by decide) (Set.Subset.refl _) (fun x => -x)
    (fun x _ => Set.mem_univ _) (fun x _ => Set.mem_univ _)
    (fun k => if k.val = 0 then (1 : ℝ) else 2) hfeas

#print axioms exists_optimal
