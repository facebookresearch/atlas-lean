/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Passive pipe networks on an arc incidence matrix

## i. Overview

A finite pipe network is kept as an arc table: nodes `V`, arcs `E`, and
`tail, head : E → V`, so parallel and antiparallel pipes retain distinct
identities. With the canonical incidence matrix
`B = MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix`, the pipe-flow equations are `B *ᵥ q = d` and
`-Bᵀ *ᵥ h = fun e => r e * q e * |q e|`, and a passive pipe flow is
those equations together with nonnegative resistances.

Signs and units are documented hypotheses, not type-checked dimensions
(`WithDim` is not used): `h` is piezometric head (length), `q` is
volumetric flow (length^3/time) in the tail-to-head direction, `r` has
units time^2/length^5 so `r q |q|` is a head, and `d = B *ᵥ q` is net
arc inflow, positive at consumers and negative at sources. Resistance
coefficients are unconstrained in the equation relation
`IsPipeFlowEquations`; passivity (`IsPassivePipeFlow`) adds
nonnegative resistances, under which dissipation is nonnegative. No existence theorem, pump,
valve, cavitation, or positive-flow admission claim is included.

## ii. Key results

- `FluidDynamics.Hydraulics.PipeNetwork.IsPipeFlowEquations`: the
  pipe-flow equations on the canonical incidence matrix, with
  unconstrained resistances.
- `FluidDynamics.Hydraulics.PipeNetwork.IsPassivePipeFlow`: the
  passive refinement, adding nonnegative resistances.
- `FluidDynamics.Hydraulics.PipeNetwork.pipeFlowEquations_head_drop`: the
  arc head drop is `r e * q e * |q e|`.
- `FluidDynamics.Hydraulics.PipeNetwork.pipeFlowEquations_dissipation` and
  `pipeFlowEquations_dissipation_nonneg`: the dissipation pairing and its
  sign; for a passive flow the sign needs no extra hypothesis.
- `FluidDynamics.Hydraulics.PipeNetwork.pipeFlowEquations_reverse`:
  reversing all orientations and signed flows preserves the predicate.

## iii. Table of contents

- A. Pipe-flow equations, head drop, dissipation, and reversal
- B. Passive refinement

## iv. References

- `MathlibExt.Combinatorics.Graph.ArcNetwork` for the canonical signed
  incidence matrix and its flow interpretation.
- Standard network hydraulics: node continuity `B q = d` and the
  quadratic passive head-loss law `h_tail - h_head = r q |q|`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FluidDynamics.Hydraulics.PipeNetwork

open Matrix MathlibExt.Combinatorics.Graph.ArcNetwork

/-! ## A. Pipe-flow equations, head drop, dissipation, and reversal -/

/-- Pipe-flow equations on a fixed finite arc topology.
Arc IDs are retained, including parallel pipes. The first
equation says `B *ᵥ q = d`, where `d` is net inflow at nodes.
The second says the head drop from tail to head on each arc is
the quadratic passive law `r e * q e * |q e|`, written in
incidence form as `-Bᵀ *ᵥ h`. No existence, pump, valve,
cavitation, or positive-flow admission claim is included. Resistance
coefficients are unconstrained in this equation relation, so a
negative resistance (an active element) can satisfy it; passivity
is the refinement `IsPassivePipeFlow` below. -/
def IsPipeFlowEquations {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) (r q : E → ℝ) (d h : V → ℝ) : Prop :=
  (incidenceMatrix tail head).mulVec q = d ∧
    -(((incidenceMatrix tail head)ᵀ).mulVec h)
      = fun e => r e * q e * |q e|

/-- Canonical incidence pairing: pairing node heads with
`B *ᵥ q` is pairing `Bᵀ *ᵥ h` with arc flows. -/
private theorem incidenceMatrix_pairing {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) (q : E → ℝ) (h : V → ℝ) :
    h ⬝ᵥ ((incidenceMatrix tail head).mulVec q)
      = (((incidenceMatrix tail head)ᵀ).mulVec h) ⬝ᵥ q := by
  rw [dotProduct_comm (((incidenceMatrix tail head)ᵀ).mulVec h) q]
  exact (Matrix.dotProduct_transpose_mulVec _ _ _).symm

/-- Head-drop form of the pipe law: on every arc, the
tail head minus the head head value is `r e * q e * |q e|`. -/
theorem pipeFlowEquations_head_drop {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ}
    (hp : IsPipeFlowEquations tail head r q d h) (e : E) :
    h (tail e) - h (head e) = r e * q e * |q e| := by
  obtain ⟨hBq, hBh⟩ := hp
  have h2 := congrFun hBh e
  simp only [Pi.neg_apply] at h2
  have hBT : (((incidenceMatrix tail head)ᵀ).mulVec h) e
      = h (head e) - h (tail e) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incidenceMatrix]
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Fintype.sum_ite_eq, Fintype.sum_ite_eq]
  rw [hBT] at h2
  linarith

/-- Dissipation pairing for the pipe-flow equations: the negative
head-demand pairing is the sum of the arc dissipation terms. -/
theorem pipeFlowEquations_dissipation {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ}
    (hp : IsPipeFlowEquations tail head r q d h) :
    - (h ⬝ᵥ d) = ∑ e, r e * (q e) ^ 2 * |q e| := by
  obtain ⟨hBq, hBh⟩ := hp
  have hpair : h ⬝ᵥ d = (((incidenceMatrix tail head)ᵀ).mulVec h) ⬝ᵥ q := by
    rw [← hBq]
    exact incidenceMatrix_pairing tail head q h
  have hneg : (-(((incidenceMatrix tail head)ᵀ).mulVec h)) ⬝ᵥ q
      = ∑ e, r e * (q e) ^ 2 * |q e| := by
    rw [hBh]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hpair, ← neg_dotProduct]
  exact hneg

/-- With nonnegative resistance coefficients, the dissipation
pairing of the pipe-flow equations is nonnegative. -/
theorem pipeFlowEquations_dissipation_nonneg {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ}
    (hp : IsPipeFlowEquations tail head r q d h)
    (hr : ∀ e, 0 ≤ r e) :
    0 ≤ - (h ⬝ᵥ d) := by
  rw [pipeFlowEquations_dissipation hp]
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (mul_nonneg (hr e) (sq_nonneg _)) (abs_nonneg _)

/-- Reversing every arc orientation and reversing the signed
arc flows preserves the pipe-flow equations with same node
inflow and heads. -/
theorem pipeFlowEquations_reverse {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ}
    (hp : IsPipeFlowEquations tail head r q d h) :
    IsPipeFlowEquations head tail r (-q) d h := by
  obtain ⟨hBq, hBh⟩ := hp
  have hBneg : incidenceMatrix head tail = -(incidenceMatrix tail head) := by
    funext v e
    simp only [incidenceMatrix, Matrix.neg_apply]
    ring
  constructor
  · rw [hBneg, Matrix.neg_mulVec_neg]
    exact hBq
  · rw [hBneg, Matrix.transpose_neg, Matrix.neg_mulVec, neg_neg]
    funext e
    have h2 := congrFun hBh e
    simp only [Pi.neg_apply] at h2
    simp only [Pi.neg_apply, abs_neg]
    have hrw : r e * (-(q e)) * |q e| = -(r e * q e * |q e|) := by ring
    rw [hrw]
    linarith

/-! ## B. Passive refinement -/

/-- A passive pipe flow: the pipe-flow equations together with
nonnegative resistance coefficients. A negative resistance would
supply energy rather than dissipate it, so it is not passive. -/
def IsPassivePipeFlow {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) (r q : E → ℝ) (d h : V → ℝ) : Prop :=
  IsPipeFlowEquations tail head r q d h ∧ ∀ e, 0 ≤ r e

/-- Head-drop form of the passive-pipe law. -/
theorem passivePipeFlow_head_drop {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ}
    (hp : IsPassivePipeFlow tail head r q d h) (e : E) :
    h (tail e) - h (head e) = r e * q e * |q e| :=
  pipeFlowEquations_head_drop hp.1 e

/-- Dissipation pairing for a passive pipe flow. -/
theorem passivePipeFlow_dissipation {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ}
    (hp : IsPassivePipeFlow tail head r q d h) :
    - (h ⬝ᵥ d) = ∑ e, r e * (q e) ^ 2 * |q e| :=
  pipeFlowEquations_dissipation hp.1

/-- The dissipation pairing of a passive pipe flow is
nonnegative. -/
theorem passivePipeFlow_dissipation_nonneg {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ}
    (hp : IsPassivePipeFlow tail head r q d h) :
    0 ≤ - (h ⬝ᵥ d) :=
  pipeFlowEquations_dissipation_nonneg hp.1 hp.2

/-- Reversing every arc orientation and reversing the signed arc
flows preserves passivity, with the same node inflow and heads. -/
theorem passivePipeFlow_reverse {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ}
    (hp : IsPassivePipeFlow tail head r q d h) :
    IsPassivePipeFlow head tail r (-q) d h :=
  ⟨pipeFlowEquations_reverse hp.1, hp.2⟩

end FluidDynamics.Hydraulics.PipeNetwork
