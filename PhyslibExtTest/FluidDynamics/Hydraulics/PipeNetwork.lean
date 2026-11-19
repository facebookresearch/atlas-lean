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
  constructor <;> ext x <;> fin_cases x <;>
    simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- Focused head drop and dissipation are both `1`. -/
example : (![2, 1] : Fin 2 → ℝ) 0 - (![2, 1] : Fin 2 → ℝ) 1
    = (1 : ℝ) * 1 * |1| :=
  passivePipeFlow_head_drop (by
    constructor <;> ext x <;> fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num :
    IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
      ![-1, 1] ![2, 1]) 0

example : -((![2, 1] : Fin 2 → ℝ) ⬝ᵥ ![-1, 1]) = 1 := by
  have hp : IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
      ![-1, 1] ![2, 1] := by
    constructor <;> ext x <;> fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  rw [passivePipeFlow_dissipation hp]
  norm_num [Fin.sum_univ_one]

/-- Parallel arcs retain identity: `q = (1, 1 / 2)` with
`r = (1, 4)` satisfies the same node inflow and heads. -/
example : IsPassivePipeFlow (![0, 0] : Fin 2 → Fin 2) ![1, 1]
    ![1, 4] ![1, 1 / 2] ![-3 / 2, 3 / 2] ![2, 1] := by
  constructor <;> ext x <;> fin_cases x <;>
    simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- Collapsing the parallel flow onto one arc is rejected. -/
example : ¬ IsPassivePipeFlow (![0, 0] : Fin 2 → Fin 2) ![1, 1]
    ![1, 4] ![3 / 2, 0] ![-3 / 2, 3 / 2] ![2, 1] := by
  intro hp
  have h := passivePipeFlow_head_drop hp 1
  norm_num at h

/-- Antiparallel arcs with signed flows satisfy the predicate. -/
example : IsPassivePipeFlow (![0, 1] : Fin 2 → Fin 2) ![1, 0]
    ![1, 1] ![1, -1] ![-2, 2] ![2, 1] := by
  constructor <;> ext x <;> fin_cases x <;>
    simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

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
    constructor <;> ext x <;> fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num :
    IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
      ![-1, 1] ![2, 1])

/-- Reversal without flipping the signed flow is rejected. -/
example : ¬ IsPassivePipeFlow (![1] : Fin 1 → Fin 2) ![0] ![1] ![1]
    ![-1, 1] ![2, 1] := by
  intro hp
  have h := congrFun hp.1 0
  simp [incidenceMatrix, Matrix.mulVec, dotProduct] at h
  norm_num at h

/-- Wrong-sign node inflow control for the focused state. -/
example : ¬ IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
    ![1, -1] ![2, 1] := by
  intro hp
  have h := congrFun hp.1 0
  simp [incidenceMatrix, Matrix.mulVec, dotProduct] at h
  norm_num at h

/-- Wrong-head control for the focused state. -/
example : ¬ IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![1] ![1]
    ![-1, 1] ![1, 2] := by
  intro hp
  have h := passivePipeFlow_head_drop hp 0
  norm_num at h

/-- Negative resistance satisfies the predicate but gives negative
dissipation, so the nonnegativity hypothesis is necessary. -/
example : IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![-1] ![1]
    ![-1, 1] ![1, 2] := by
  constructor <;> ext x <;> fin_cases x <;>
    simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

example : -((![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![-1, 1]) = -1 := by
  have hp : IsPassivePipeFlow (![0] : Fin 1 → Fin 2) ![1] ![-1] ![1]
      ![-1, 1] ![1, 2] := by
    constructor <;> ext x <;> fin_cases x <;>
      simp [incidenceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  rw [passivePipeFlow_dissipation hp]
  norm_num [Fin.sum_univ_one]

#print axioms FluidDynamics.Hydraulics.PipeNetwork.incidenceMatrix_pairing
#print axioms FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_head_drop
#print axioms FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_dissipation
#print axioms FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_dissipation_nonneg
#print axioms FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_reverse

end PhyslibExtTest.FluidDynamics.Hydraulics.PipeNetwork
