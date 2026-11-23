/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Hydraulics.PipeNetworkHeads
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Anchored-head uniqueness checks

Concrete consumers of
`PhyslibExt.FluidDynamics.Hydraulics.PipeNetworkHeads` on
one- and two-node networks: anchored uniqueness with
positive and negative resistance, the shift family without
an anchor, a disconnected component, the single-node case,
a zero-resistance circulation, and the zero-weight graph.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Two-node anchored uniqueness
- B. Necessity controls

## iv. References

- `PhyslibExt.FluidDynamics.Hydraulics.PipeNetworkHeads`
-/

open Matrix
open MathlibExt.Combinatorics.Graph.ArcNetwork
open MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian
open FluidDynamics.Hydraulics.PipeNetwork

namespace PhyslibExtTest.FluidDynamics.Hydraulics.PipeNetworkHeads

/-- The one-arc two-node underlying graph is connected. -/
private lemma connected_two :
    (positiveArcGraph (![0] : Fin 1 → Fin 2) ![1] (fun _ => (1 : ℝ))).Connected := by
  have hadj : (positiveArcGraph (![0] : Fin 1 → Fin 2) ![1]
      (fun _ => (1 : ℝ))).Adj 0 1 := by
    rw [positiveArcGraph, SimpleGraph.fromRel_adj]
    exact ⟨by norm_num, Or.inl ⟨0, one_pos, rfl, rfl⟩⟩
  refine ⟨fun u v => ?_⟩
  fin_cases u <;> fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact hadj.reachable
  · exact hadj.symm.reachable
  · exact SimpleGraph.Reachable.refl _

/-- Solution builder on the one-arc network: any `r`, `q`,
and head pair with the drop `r * q * |q|` solves the
equations with demand `![-q, q]`. -/
private lemma solution_two (r q h0 h1 : ℝ) (hdrop : h0 - h1 = r * q * |q|) :
    IsPipeFlowEquations (![0] : Fin 1 → Fin 2) ![1] ![r] ![q] ![-q, q]
      ![h0, h1] := by
  refine ⟨?_, ?_⟩
  · funext v
    fin_cases v <;>
      simp [Matrix.mulVec, dotProduct, incidenceMatrix]
  · funext e
    fin_cases e
    simp only [Pi.neg_apply, incidenceMatrix_transpose_mulVec_apply]
    simp
    linarith

/-! ## A. Two-node anchored uniqueness -/

/-- Any second solution with the same demand and anchor
head `5` at node `0` is the anchored solution
(`q = 2`, `h = (5, 1)`, drop `4`). -/
example (q₂ : Fin 1 → ℝ) (h₂ : Fin 2 → ℝ)
    (hp₂ : IsPipeFlowEquations (![0] : Fin 1 → Fin 2) ![1] ![1] q₂ ![-2, 2] h₂)
    (hanchor : ![5, 1] 0 = h₂ 0) :
    q₂ = ![2] ∧ h₂ = ![5, 1] := by
  have hp₁ : IsPipeFlowEquations (![0] : Fin 1 → Fin 2) ![1] ![1] ![2] ![-2, 2]
      ![5, 1] := by
    have h := solution_two 1 2 5 1 (by norm_num)
    simpa using h
  have h := pipeFlowEquations_unique_of_anchor (r := (![1] : Fin 1 → ℝ))
    (q₁ := ![2]) (q₂ := q₂) (h₁ := ![5, 1]) (h₂ := h₂) (v₀ := 0)
    (fun e => by fin_cases e; norm_num) connected_two hp₁ hp₂ hanchor
  exact ⟨h.1.symm, h.2.symm⟩

/-- Negative resistance is admitted by head uniqueness from
equal flows: with `r = -3`, `q = 2`, the drop is `-12`. -/
example (h₂ : Fin 2 → ℝ)
    (hp₂ : IsPipeFlowEquations (![0] : Fin 1 → Fin 2) ![1] ![-3] ![2] ![-2, 2]
      h₂)
    (hanchor : ![0, 12] 0 = h₂ 0) :
    h₂ = ![0, 12] := by
  have hp₁ : IsPipeFlowEquations (![0] : Fin 1 → Fin 2) ![1] ![-3] ![2]
      ![-2, 2] ![0, 12] := by
    have h := solution_two (-3) 2 0 12 (by norm_num)
    simpa using h
  exact (pipeFlowEquations_head_eq_of_flow_eq (r := (![-3] : Fin 1 → ℝ))
    (h₁ := ![0, 12]) (h₂ := h₂) (v₀ := 0) connected_two hp₁ hp₂ rfl
    hanchor).symm

/-! ## B. Necessity controls -/

/-- Without an anchor the heads shift: `(5, 1)` and
`(9, 5)` both solve the same equations. -/
example : IsPipeFlowEquations (![0] : Fin 1 → Fin 2) ![1] ![1] ![2] ![-2, 2]
      ![5, 1] ∧
    IsPipeFlowEquations (![0] : Fin 1 → Fin 2) ![1] ![1] ![2] ![-2, 2]
      ![9, 5] ∧
    (![5, 1] : Fin 2 → ℝ) ≠ ![9, 5] := by
  refine ⟨?_, ?_, by norm_num [Matrix.cons_val_zero]⟩
  · simpa using solution_two 1 2 5 1 (by norm_num)
  · simpa using solution_two 1 2 9 5 (by norm_num)

/-- With no arcs, every head assignment solves the
equations with zero demand. -/
private lemma solution_empty {W : Type*} [Fintype W] [DecidableEq W]
    (h : W → ℝ) :
    IsPipeFlowEquations (Fin.elim0 : Fin 0 → W) Fin.elim0 (fun e => e.elim0)
      (fun e => e.elim0) 0 h := by
  refine ⟨?_, ?_⟩
  · funext v
    simp [Matrix.mulVec, dotProduct]
  · funext e
    exact e.elim0

/-- Disconnected component control: with no arcs, two
solutions can agree at the anchor node `0` and differ at
node `1`, so connectedness cannot be dropped. -/
example : IsPipeFlowEquations (Fin.elim0 : Fin 0 → Fin 2) Fin.elim0
      (fun e => e.elim0) (fun e => e.elim0) 0 ![3, 4] ∧
    IsPipeFlowEquations (Fin.elim0 : Fin 0 → Fin 2) Fin.elim0
      (fun e => e.elim0) (fun e => e.elim0) 0 ![3, 9] ∧
    (![3, 4] : Fin 2 → ℝ) 0 = ![3, 9] 0 ∧
    (![3, 4] : Fin 2 → ℝ) ≠ ![3, 9] :=
  ⟨solution_empty ![3, 4], solution_empty ![3, 9], rfl,
    by norm_num [Matrix.cons_val_one]⟩

/-- Single-node case: one node, no arcs; anchored heads
agree. -/
example (h₁ h₂ : Fin 1 → ℝ) (hanchor : h₁ 0 = h₂ 0) : h₁ = h₂ := by
  have hconn : (positiveArcGraph (Fin.elim0 : Fin 0 → Fin 1) Fin.elim0
      (fun _ => (1 : ℝ))).Connected := by
    refine ⟨fun u v => ?_⟩
    fin_cases u
    fin_cases v
    exact SimpleGraph.Reachable.refl _
  exact pipeFlowEquations_head_eq_of_flow_eq (r := fun e : Fin 0 => e.elim0)
    (q₁ := fun e : Fin 0 => e.elim0) (q₂ := fun e : Fin 0 => e.elim0)
    (h₁ := h₁) (h₂ := h₂) (v₀ := 0) hconn (solution_empty h₁)
    (solution_empty h₂) rfl hanchor

/-- Zero-resistance circulation: at `r = 0` on the
two-arc cycle, flows `(1, 1)` and `(3, 3)` both solve with
demand `0` and constant heads, so strict positivity cannot
be dropped from flow uniqueness. -/
example : IsPassivePipeFlow (![0, 1] : Fin 2 → Fin 2) ![1, 0] ![0, 0] ![1, 1] 0
      ![7, 7] ∧
    IsPassivePipeFlow (![0, 1] : Fin 2 → Fin 2) ![1, 0] ![0, 0] ![3, 3] 0
      ![7, 7] ∧
    (![1, 1] : Fin 2 → ℝ) ≠ ![3, 3] := by
  have hcirc : ∀ c : ℝ,
      IsPipeFlowEquations (![0, 1] : Fin 2 → Fin 2) ![1, 0] ![0, 0] ![c, c] 0
        ![7, 7] := by
    intro c
    refine ⟨?_, ?_⟩ <;> funext x <;> fin_cases x <;>
      norm_num [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        incidenceMatrix, Fin.sum_univ_two]
  exact ⟨⟨hcirc 1, fun e => by fin_cases e <;> norm_num⟩,
    ⟨hcirc 3, fun e => by fin_cases e <;> norm_num⟩,
    by norm_num [Matrix.cons_val_zero]⟩

/-- Zero-weight graph control: with weight `0` the arc
gives no adjacency, unlike the weight-one graph. -/
example : ¬ (positiveArcGraph (![0] : Fin 1 → Fin 2) ![1]
    (fun _ => (0 : ℝ))).Adj 0 1 := by
  rw [positiveArcGraph, SimpleGraph.fromRel_adj]
  rintro ⟨-, ⟨e, he, -, -⟩ | ⟨e, he, -, -⟩⟩ <;> simp at he

#print axioms
  FluidDynamics.Hydraulics.PipeNetwork.pipeFlowEquations_head_eq_of_flow_eq
#print axioms
  FluidDynamics.Hydraulics.PipeNetwork.pipeFlowEquations_unique_of_anchor
#print axioms
  FluidDynamics.Hydraulics.PipeNetwork.passivePipeFlow_unique_of_anchor
#print axioms
  MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian.positiveArcGraph_eq_of_pos

end PhyslibExtTest.FluidDynamics.Hydraulics.PipeNetworkHeads
