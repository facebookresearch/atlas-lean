/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: ported the source factored tensor-network foundations, named the
shared API, and made finite label alphabets explicit so label types need not be finite.
-/
module

public import MathlibExt.Data.Fintype.PiFinsetOn
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Integer-valued factored tensor networks

This first tensor-network module defines finite edge labelings, integer-valued instances,
factored networks, their values and capacity bounds. It does not include padding, contraction,
merging, conversion between presentations, or complexity claims.

Adapted from `eth/proof/networks/Groundwork/Net/Defs.lean` and the symmetry lemmas in
`eth/proof/networks/Groundwork/Net/Net.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork

open Finset

variable {J σ τ A : Type*}

/-- Pairs `(a, b)` with `a < b`, representing unordered pairs once. -/
def orderedPairs (J : Type*) [Fintype J] [LinearOrder J] : Finset (J × J) :=
  univ.filter fun p => p.1 < p.2

/-- Membership in `orderedPairs` is strict ordering of the two coordinates. -/
@[simp] theorem mem_orderedPairs [Fintype J] [LinearOrder J] (p : J × J) :
    p ∈ orderedPairs J ↔ p.1 < p.2 := by
  simp [orderedPairs]

/-- The ordered representative `(min a b, max a b)` of the pair `{a, b}`. -/
def pairIndex [LinearOrder J] (a b : J) : J × J :=
  (min a b, max a b)

/-- Complete-graph edge labelings, free on `orderedPairs` and default elsewhere. -/
def edgeLabelings (J : Type*) [Fintype J] [LinearOrder J]
    (labels : Finset A) (default : A) : Finset (J × J → A) :=
  Fintype.piFinsetOn (fun p : J × J => p.1 < p.2) (fun _ => labels) default

/-- A labeling belongs to `edgeLabelings` exactly when active edges use allowed labels and all
other coordinates contain the default. -/
@[simp] theorem mem_edgeLabelings [Fintype J] [LinearOrder J]
    (labels : Finset A) (default : A) (labeling : J × J → A) :
    labeling ∈ edgeLabelings J labels default ↔
      ∀ p, (p.1 < p.2 → labeling p ∈ labels) ∧ (¬p.1 < p.2 → labeling p = default) := by
  simp [edgeLabelings]

/-- Labels incident to `v`, indexed by the other endpoint. -/
def incidentLabels [LinearOrder J] (labeling : J × J → A) (v : J) : J → A :=
  fun w => labeling (pairIndex v w)

/-- An integer-valued local tensor at each vertex. -/
abbrev Instance (J A : Type*) := J → (J → A) → ℤ

namespace Instance

/-- The sum, over complete-graph edge labelings, of the product of local tensors. -/
def value [Fintype J] [LinearOrder J] (labels : Finset A) (default : A)
    (R : Instance J A) : ℤ :=
  ∑ labeling ∈ edgeLabelings J labels default,
    ∏ v, R v (incidentLabels labeling v)

end Instance

/-- An integer-valued factored tensor network.

Only `Θ a b` with `a < b` supplies labels. The factors `f a b` and `f b a` are the two
sides of the same interaction. Capacities `c` are metadata used by `totalCapacity`, `Shaped`,
and `Sized`; `value` does not read them. -/
structure Factored (J σ τ : Type*) where
  /-- The finite set of states allowed at each vertex. -/
  S : J → Finset σ
  /-- The integer weight of a state at a vertex. -/
  W : J → σ → ℤ
  /-- The finite label set stored in increasing vertex order. -/
  Θ : J → J → Finset τ
  /-- The factor contributed on one vertex's side of an edge label. -/
  f : J → J → σ → τ → ℤ
  /-- The directed capacity table; the bare structure does not require symmetry. -/
  c : J → J → ℕ

namespace Factored

/-- The label set of an unordered vertex pair. -/
def labelSet [LinearOrder J] (N : Factored J σ τ) (a b : J) : Finset τ :=
  N.Θ (min a b) (max a b)

/-- The label set is independent of endpoint order. -/
theorem labelSet_comm [LinearOrder J] (N : Factored J σ τ) (a b : J) :
    N.labelSet a b = N.labelSet b a := by
  simp [labelSet, min_comm, max_comm]

/-- The interaction of two states, summed over their shared edge labels. -/
def interaction [LinearOrder J] (N : Factored J σ τ)
    (a b : J) (z z' : σ) : ℤ :=
  ∑ θ ∈ N.labelSet a b, N.f a b z θ * N.f b a z' θ

/-- Reading an interaction from the other endpoint swaps its states. -/
theorem interaction_comm [LinearOrder J] (N : Factored J σ τ)
    (a b : J) (z z' : σ) :
    N.interaction a b z z' = N.interaction b a z' z := by
  unfold interaction
  rw [labelSet_comm]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The network value: sum over states of vertex weights times all pair interactions. -/
def value [Fintype J] [LinearOrder J] (N : Factored J σ τ) : ℤ :=
  ∑ z ∈ Fintype.piFinset N.S,
    (∏ a, N.W a (z a)) *
      ∏ p ∈ orderedPairs J, N.interaction p.1 p.2 (z p.1) (z p.2)

/-- The directed total capacity `Σ_{a ≠ b} c a b`; both orientations are counted. -/
def totalCapacity [Fintype J] [DecidableEq J] (N : Factored J σ τ) : ℕ :=
  ∑ a, ∑ b ∈ univ.erase a, N.c a b

/-- A network of shape parameter `P`: at most `2 ^ P` states per vertex, symmetric
capacities summing to at most `P` at each vertex, and at most `2 ^ c` labels per edge. -/
structure Shaped [Fintype J] [LinearOrder J]
    (N : Factored J σ τ) (P : ℕ) : Prop where
  card_S : ∀ a, (N.S a).card ≤ 2 ^ P
  c_symm : ∀ a b, N.c a b = N.c b a
  sum_c : ∀ a, ∑ b ∈ univ.erase a, N.c a b ≤ P
  card_labelSet : ∀ a b, a ≠ b → (N.labelSet a b).card ≤ 2 ^ N.c a b

/-- A shaped network whose weights, factors and off-diagonal interactions are bounded by
`2 ^ B` in absolute value. -/
structure Sized [Fintype J] [LinearOrder J]
    (N : Factored J σ τ) (P B : ℕ) : Prop extends Shaped N P where
  abs_W : ∀ a z, |N.W a z| ≤ 2 ^ B
  abs_f : ∀ a b z θ, |N.f a b z θ| ≤ 2 ^ B
  abs_interaction : ∀ a b z z', a ≠ b → |N.interaction a b z z'| ≤ 2 ^ B

end Factored

end TensorNetwork
