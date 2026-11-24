/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.Hydraulics.PipeNetwork
public import MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Anchored-head uniqueness for pipe-flow networks

## i. Overview

Head uniqueness for the pipe-flow equations of
`PhyslibExt.FluidDynamics.Hydraulics.PipeNetwork` on the
same arc table (nodes `V`, arcs `E`, `tail head : E → V`,
parallel and antiparallel pipes distinct). Connectivity is
connectivity of the underlying undirected network, every
arc counted with weight one (orientation ignored, loops
dropped): `(positiveArcGraph tail head (fun _ => 1)).Connected`.
On a connected network, equal edge flows and one common
head value force equal heads at every node, with no sign
condition on the resistances; the demands are not assumed
equal, but equal flows force them equal since `d = B *ᵥ q`.
With strictly positive resistances and a common demand,
flows and heads are unique once one head is fixed, in
equation and passive form. Existence of solutions is not
claimed.

## ii. Key results

- `FluidDynamics.Hydraulics.PipeNetwork.pipeFlowEquations_head_eq_of_flow_eq`:
  anchored-head uniqueness from equal flows.
- `pipeFlowEquations_unique_of_anchor` and
  `passivePipeFlow_unique_of_anchor`: full anchored
  uniqueness of flows and heads.
- The weighted-graph identity at strictly positive weights
  is the generic
  `MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian.positiveArcGraph_eq_of_pos`.

## iii. Table of contents

- A. Anchored-head uniqueness

## iv. References

- `PhyslibExt.FluidDynamics.Hydraulics.PipeNetwork` for the
  pipe-flow equations and flow uniqueness.
- `MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian` for
  the positive arc graph and the zero-energy potential
  principle.
-/

@[expose] public section

open Matrix
open MathlibExt.Combinatorics.Graph.ArcNetwork
open MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian

namespace FluidDynamics.Hydraulics.PipeNetwork

/-! ## A. Anchored-head uniqueness -/

/-- Conditional form of anchored-head uniqueness, given the
canonical head-drop and zero-energy statements. -/
private theorem pipeFlowEquations_head_eq_of_flow_eq_of
    {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E]
    (hdrop : ∀ {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ},
      IsPipeFlowEquations tail head r q d h → ∀ (e : E),
        h (tail e) - h (head e) = r e * q e * |q e|)
    (henergy : ∀ (tail head : E → V) (w : E → ℝ), (∀ e, 0 ≤ w e) →
      ∀ (x : V → ℝ), ∑ e, w e * (x (head e) - x (tail e)) ^ 2 = 0 → ∀ {u v : V},
        (positiveArcGraph tail head w).Reachable u v → x u = x v)
    {tail head : E → V} {r q₁ q₂ : E → ℝ} {d₁ d₂ h₁ h₂ : V → ℝ} {v₀ : V}
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (hp₁ : IsPipeFlowEquations tail head r q₁ d₁ h₁)
    (hp₂ : IsPipeFlowEquations tail head r q₂ d₂ h₂)
    (hq : q₁ = q₂) (hanchor : h₁ v₀ = h₂ v₀) :
    h₁ = h₂ := by
  have hhead : ∀ e : E, h₁ (tail e) - h₁ (head e) = h₂ (tail e) - h₂ (head e) := by
    intro e
    have d1 := hdrop hp₁ e
    have d2 := hdrop hp₂ e
    have hq' : r e * q₁ e * |q₁ e| = r e * q₂ e * |q₂ e| := by rw [hq]
    calc h₁ (tail e) - h₁ (head e) = r e * q₁ e * |q₁ e| := d1
      _ = r e * q₂ e * |q₂ e| := hq'
      _ = h₂ (tail e) - h₂ (head e) := d2.symm
  have hw : ∀ e : E, 0 ≤ (fun _ => (1 : ℝ)) e := fun e => zero_le_one
  have hdiff : ∀ e : E,
      (h₁ (head e) - h₂ (head e)) - (h₁ (tail e) - h₂ (tail e)) = 0 := by
    intro e
    have h := hhead e
    linarith
  have hsum : ∑ e, (fun _ => (1 : ℝ)) e
      * ((h₁ (head e) - h₂ (head e)) - (h₁ (tail e) - h₂ (tail e))) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    simp [hdiff e]
  have hreach : ∀ v : V, h₁ v₀ - h₂ v₀ = h₁ v - h₂ v := by
    intro v
    have hrch : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Reachable v₀ v :=
      hconn v₀ v
    have hx := henergy tail head (fun _ => (1 : ℝ)) hw (fun v => h₁ v - h₂ v)
      hsum hrch
    simpa using hx
  funext v
  have hv := hreach v
  rw [hanchor] at hv
  linarith

/-- Anchored-head uniqueness: if the underlying undirected
pipe graph (every arc, orientation ignored, loops dropped)
is connected, two solutions of the pipe-flow equations
with the same resistances, equal edge flows and a common
head at `v₀` have equal heads at every node. No sign
condition on `r` is needed. -/
theorem pipeFlowEquations_head_eq_of_flow_eq {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q₁ q₂ : E → ℝ} {d₁ d₂ h₁ h₂ : V → ℝ} {v₀ : V}
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (hp₁ : IsPipeFlowEquations tail head r q₁ d₁ h₁)
    (hp₂ : IsPipeFlowEquations tail head r q₂ d₂ h₂)
    (hq : q₁ = q₂) (hanchor : h₁ v₀ = h₂ v₀) :
    h₁ = h₂ :=
  pipeFlowEquations_head_eq_of_flow_eq_of
    (fun hp e => pipeFlowEquations_head_drop hp e)
    (fun tail head w hw x h0 {_u _v} huv =>
      eq_of_energy_eq_zero tail head w hw x h0 huv)
    hconn hp₁ hp₂ hq hanchor

/-- Conditional form of full anchored uniqueness, given the
canonical head-drop, zero-energy, and flow-uniqueness
statements. -/
private theorem pipeFlowEquations_unique_of_anchor_of
    {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E]
    (hdrop : ∀ {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ},
      IsPipeFlowEquations tail head r q d h → ∀ (e : E),
        h (tail e) - h (head e) = r e * q e * |q e|)
    (henergy : ∀ (tail head : E → V) (w : E → ℝ), (∀ e, 0 ≤ w e) →
      ∀ (x : V → ℝ), ∑ e, w e * (x (head e) - x (tail e)) ^ 2 = 0 → ∀ {u v : V},
        (positiveArcGraph tail head w).Reachable u v → x u = x v)
    (hflow : ∀ {tail head : E → V} {r q₁ q₂ : E → ℝ} {d h₁ h₂ : V → ℝ},
      (∀ e, 0 < r e) →
      IsPipeFlowEquations tail head r q₁ d h₁ →
      IsPipeFlowEquations tail head r q₂ d h₂ →
      q₁ = q₂)
    {tail head : E → V} {r q₁ q₂ : E → ℝ} {d h₁ h₂ : V → ℝ} {v₀ : V}
    (hr : ∀ e, 0 < r e)
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (hp₁ : IsPipeFlowEquations tail head r q₁ d h₁)
    (hp₂ : IsPipeFlowEquations tail head r q₂ d h₂)
    (hanchor : h₁ v₀ = h₂ v₀) :
    q₁ = q₂ ∧ h₁ = h₂ := by
  have hq : q₁ = q₂ := hflow hr hp₁ hp₂
  exact ⟨hq, pipeFlowEquations_head_eq_of_flow_eq_of hdrop henergy hconn hp₁ hp₂
    hq hanchor⟩

/-- Full anchored uniqueness for strictly positive
resistances and a common demand, consuming
`pipeFlowEquations_flow_unique`. -/
theorem pipeFlowEquations_unique_of_anchor {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q₁ q₂ : E → ℝ} {d h₁ h₂ : V → ℝ} {v₀ : V}
    (hr : ∀ e, 0 < r e)
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (hp₁ : IsPipeFlowEquations tail head r q₁ d h₁)
    (hp₂ : IsPipeFlowEquations tail head r q₂ d h₂)
    (hanchor : h₁ v₀ = h₂ v₀) :
    q₁ = q₂ ∧ h₁ = h₂ :=
  pipeFlowEquations_unique_of_anchor_of
    (fun hp e => pipeFlowEquations_head_drop hp e)
    (fun tail head w hw x h0 {_u _v} huv =>
      eq_of_energy_eq_zero tail head w hw x h0 huv)
    (fun hr hp₁ hp₂ => pipeFlowEquations_flow_unique hr hp₁ hp₂)
    hr hconn hp₁ hp₂ hanchor

/-- Conditional form of passive anchored uniqueness, given
the canonical head-drop, zero-energy, and passive
flow-uniqueness statements. -/
private theorem passivePipeFlow_unique_of_anchor_of
    {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E]
    (hdrop : ∀ {tail head : E → V} {r q : E → ℝ} {d h : V → ℝ},
      IsPipeFlowEquations tail head r q d h → ∀ (e : E),
        h (tail e) - h (head e) = r e * q e * |q e|)
    (henergy : ∀ (tail head : E → V) (w : E → ℝ), (∀ e, 0 ≤ w e) →
      ∀ (x : V → ℝ), ∑ e, w e * (x (head e) - x (tail e)) ^ 2 = 0 → ∀ {u v : V},
        (positiveArcGraph tail head w).Reachable u v → x u = x v)
    (hpflow : ∀ {tail head : E → V} {r q₁ q₂ : E → ℝ} {d h₁ h₂ : V → ℝ},
      (∀ e, 0 < r e) →
      IsPassivePipeFlow tail head r q₁ d h₁ →
      IsPassivePipeFlow tail head r q₂ d h₂ →
      q₁ = q₂)
    {tail head : E → V} {r q₁ q₂ : E → ℝ} {d h₁ h₂ : V → ℝ} {v₀ : V}
    (hr : ∀ e, 0 < r e)
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (hp₁ : IsPassivePipeFlow tail head r q₁ d h₁)
    (hp₂ : IsPassivePipeFlow tail head r q₂ d h₂)
    (hanchor : h₁ v₀ = h₂ v₀) :
    q₁ = q₂ ∧ h₁ = h₂ := by
  have hq : q₁ = q₂ := hpflow hr hp₁ hp₂
  exact ⟨hq, pipeFlowEquations_head_eq_of_flow_eq_of hdrop henergy hconn hp₁.1
    hp₂.1 hq hanchor⟩

/-- Passive form of full anchored uniqueness. -/
theorem passivePipeFlow_unique_of_anchor {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    {tail head : E → V} {r q₁ q₂ : E → ℝ} {d h₁ h₂ : V → ℝ} {v₀ : V}
    (hr : ∀ e, 0 < r e)
    (hconn : (positiveArcGraph tail head (fun _ => (1 : ℝ))).Connected)
    (hp₁ : IsPassivePipeFlow tail head r q₁ d h₁)
    (hp₂ : IsPassivePipeFlow tail head r q₂ d h₂)
    (hanchor : h₁ v₀ = h₂ v₀) :
    q₁ = q₂ ∧ h₁ = h₂ :=
  passivePipeFlow_unique_of_anchor_of
    (fun hp e => pipeFlowEquations_head_drop hp e)
    (fun tail head w hw x h0 {_u _v} huv =>
      eq_of_energy_eq_zero tail head w hw x h0 huv)
    (fun hr hp₁ hp₂ => passivePipeFlow_flow_unique hr hp₁ hp₂)
    hr hconn hp₁ hp₂ hanchor

end FluidDynamics.Hydraulics.PipeNetwork
