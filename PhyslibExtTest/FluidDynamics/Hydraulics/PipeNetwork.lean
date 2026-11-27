/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Hydraulics.PipeNetwork
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Passive pipe network checks

Concrete consumers of
`PhyslibExt.FluidDynamics.Hydraulics.PipeNetwork`: the focused
one-pipe state, parallel and antiparallel arcs, orientation
reversal, wrong-sign controls, and a negative-resistance control.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Focused and parallel networks
- B. Reversal and invalid controls

## iv. References

- `PhyslibExt.FluidDynamics.Hydraulics.PipeNetwork`
-/

open Matrix MathlibExt.Combinatorics.Graph.ArcNetwork
open FluidDynamics.Hydraulics.PipeNetwork

namespace PhyslibExtTest.FluidDynamics.Hydraulics.PipeNetwork

/-! ## A. Focused and parallel networks -/

/-- Focused state: one pipe `0 → 1`, `h = (2, 1)`, `r = q = 1`,
`d = (-1, 1)` is a passive pipe flow. -/
example : IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
    ![-1, 1] ![2, 1] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext x; fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ext x; fin_cases x;
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num
  · intro e; fin_cases e; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Focused head drop and dissipation are both `1`. -/
example : (![2, 1] : Fin 2 → ℝ) 0 - (![2, 1] : Fin 2 → ℝ) 1
    = (1 : ℝ) * 1 * |1| :=
  passivePipeFlow_head_drop (by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext x; fin_cases x <;>
        simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · ext x; fin_cases x;
        simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num
    · intro e; fin_cases e; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] :
    IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
      ![-1, 1] ![2, 1]) 0

example : -((![2, 1] : Fin 2 → ℝ) ⬝ᵥ ![-1, 1]) = 1 := by
  have hp : IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
      ![-1, 1] ![2, 1] := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext x; fin_cases x <;>
        simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · ext x; fin_cases x;
        simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num
    · intro e; fin_cases e; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [passivePipeFlow_dissipation hp]
  norm_num [Fin.sum_univ_one]

/-- Parallel arcs retain identity: `q = (1, 1 / 2)` with
`r = (1, 4)` satisfies the same node inflow and heads. -/
example : IsPassivePipeFlow (![0, 0] : Fin 2 → Fin 2) ![1, 1]
    ![1, 4] ![1, 1 / 2] ![-3 / 2, 3 / 2] ![2, 1] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext x; fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · ext x; fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · intro e; fin_cases e <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Collapsing the parallel flow onto one arc is rejected. -/
example : ¬ IsPassivePipeFlow (![0, 0] : Fin 2 → Fin 2) ![1, 1]
    ![1, 4] ![3 / 2, 0] ![-3 / 2, 3 / 2] ![2, 1] := by
  intro hp
  have h := passivePipeFlow_head_drop hp 1
  norm_num at h

/-- Antiparallel arcs with signed flows satisfy the predicate. -/
example : IsPassivePipeFlow (![0, 1] : Fin 2 → Fin 2) ![1, 0]
    ![1, 1] ![1, -1] ![-2, 2] ![2, 1] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext x; fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · ext x; fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · intro e; fin_cases e <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The antiparallel wrong-sign flow is rejected. -/
example : ¬ IsPassivePipeFlow (![0, 1] : Fin 2 → Fin 2) ![1, 0]
    ![1, 1] ![1, 1] ![-2, 2] ![2, 1] := by
  intro hp
  have h := passivePipeFlow_head_drop hp 1
  norm_num at h

/-! ## B. Reversal and invalid controls -/

/-- Orientation reversal of the focused state, with the signed flow flipped. -/
example : IsPassivePipeFlow (![1] : Fin 1 → Fin 2) ![0] ![1] (-![1])
    ![-1, 1] ![2, 1] :=
  passivePipeFlow_reverse (by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext x; fin_cases x <;>
        simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · ext x; fin_cases x;
        simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num
    · intro e; fin_cases e; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] :
    IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
      ![-1, 1] ![2, 1])

/-- Reversal without flipping the signed flow is rejected. -/
example : ¬ IsPassivePipeFlow (![1] : Fin 1 → Fin 2) ![0] ![1] ![1]
    ![-1, 1] ![2, 1] := by
  intro hp
  obtain ⟨hBq, -⟩ := hp.1
  have h := congrFun hBq 0
  simp [incidenceMatrix, Matrix.mulVec, dotProduct] at h
  norm_num at h

/-- Wrong-sign node inflow control for the focused state. -/
example : ¬ IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
    ![1, -1] ![2, 1] := by
  intro hp
  obtain ⟨hBq, -⟩ := hp.1
  have h := congrFun hBq 0
  simp [incidenceMatrix, Matrix.mulVec, dotProduct] at h
  norm_num at h

/-- Wrong-head control for the focused state. -/
example : ¬ IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
    ![-1, 1] ![1, 2] := by
  intro hp
  have h := passivePipeFlow_head_drop hp 0
  norm_num at h

/-- Negative resistance satisfies the pipe-flow equations but is
not passive, and its dissipation is negative. -/
example : IsPipeFlowEquations (![0] : Fin 1 → Fin 2) ![1] ![-1] ![1]
    ![-1, 1] ![1, 2] := by
  constructor <;> ext x <;> fin_cases x <;>
    simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num

example : ¬ IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![-1] ![1]
    ![-1, 1] ![1, 2] := by
  intro hp
  have h := hp.2 0
  norm_num [Matrix.cons_val_zero] at h

example : -((![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![-1, 1]) = -1 := by
  have hp : IsPipeFlowEquations (![0] : Fin 1 → Fin 2) ![1] ![-1] ![1]
      ![-1, 1] ![1, 2] := by
    constructor <;> ext x <;> fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num
  rw [pipeFlowEquations_dissipation hp]
  norm_num [Fin.sum_univ_one]

#print axioms FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_head_drop
#print axioms FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_dissipation
#print axioms FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_dissipation_nonneg
#print axioms FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_reverse
#print axioms FluidDynamics.Hydraulics.PipeNetwork.pipeFlowEquations_dissipation

/-- One pipe, demand from flow 2: the unique flow is 2, for
any heads compatible with the law. -/
example {q₂ : Fin 1 → ℝ} {h₁ h₂ : Fin 2 → ℝ}
    (hp₁ : IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1]
      ![2] (![-2, 2]) h₁)
    (hp₂ : IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1]
      q₂ (![-2, 2]) h₂) :
    q₂ = ![2] :=
  passivePipeFlow_flow_unique (by intro e; fin_cases e; norm_num)
    hp₂ hp₁

/-- Strict positivity is essential: with two parallel
zero-resistance arcs, `(1, -1)` and `(0, 0)` both satisfy the
passive equations at zero demand with constant heads. -/
example : IsPassivePipeFlow (![0, 0] : Fin 2 → Fin 2) ![1, 1]
      ![0, 0] ![1, -1] 0 0
    ∧ IsPassivePipeFlow (![0, 0] : Fin 2 → Fin 2) ![1, 1]
      ![0, 0] ![0, 0] 0 0
    ∧ (![1, -1] : Fin 2 → ℝ) ≠ ![0, 0] := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · funext v
    fin_cases v <;> simp [incidence_mulVec, Finset.sum_filter, Fin.sum_univ_two]
  · funext e
    fin_cases e <;>
      simp [Matrix.mulVec, dotProduct, incidenceMatrix,
        Fin.sum_univ_two]
  · intro e
    fin_cases e <;> norm_num
  · funext v
    fin_cases v <;> simp [incidence_mulVec, Finset.sum_filter, Fin.sum_univ_two]
  · funext e
    fin_cases e <;>
      simp [Matrix.mulVec, dotProduct, incidenceMatrix,
        Fin.sum_univ_two]
  · intro e
    fin_cases e <;> norm_num
  · simp

#print axioms
  FluidDynamics.Hydraulics.PipeNetwork.pipeFlowEquations_flow_unique
#print axioms
  FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_flow_unique

end PhyslibExtTest.FluidDynamics.Hydraulics.PipeNetwork
