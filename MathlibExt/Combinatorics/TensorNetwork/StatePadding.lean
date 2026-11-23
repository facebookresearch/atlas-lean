/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
generalize state padding to finite ordered vertex types and distinct state carriers,
retain arbitrary pair kernels, and specialize to factored networks.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.Basic

/-! # State padding preserves tensor-network values

Adapted from `eth/proof/networks/Coding/Padding.lean` and `Coding/Defs.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

The generic sum theorem retains the independent pair kernels of the source's raw network.
Padding is injective only on allowed states; extra target states contribute zero through their
vertex weights. The factored protocol also records the source's factor and capacity clauses.
-/

@[expose] public section

namespace TensorNetwork

open Finset

variable {J σ₀ σ₁ τ : Type*}

/-- Padding the finite state sets preserves the full sum of vertex weights and arbitrary pair
kernels. No factorization, finiteness of the state carriers, or global injectivity is required. -/
theorem sum_statePadding [Fintype J] [LinearOrder J]
    (S₀ : J → Finset σ₀) (S₁ : J → Finset σ₁)
    (W₀ : J → σ₀ → ℤ) (W₁ : J → σ₁ → ℤ)
    (K₀ : J → J → σ₀ → σ₀ → ℤ) (K₁ : J → J → σ₁ → σ₁ → ℤ)
    (pad : J → σ₀ → σ₁)
    (maps : ∀ a, ∀ z ∈ S₀ a, pad a z ∈ S₁ a)
    (inj : ∀ a, ∀ z ∈ S₀ a, ∀ z' ∈ S₀ a, pad a z = pad a z' → z = z')
    (off : ∀ a, ∀ y ∈ S₁ a, (∀ z ∈ S₀ a, pad a z ≠ y) → W₁ a y = 0)
    (weights : ∀ a, ∀ z ∈ S₀ a, W₁ a (pad a z) = W₀ a z)
    (kernels : ∀ a b, a ≠ b → ∀ z ∈ S₀ a, ∀ z' ∈ S₀ b,
      K₁ a b (pad a z) (pad b z') = K₀ a b z z') :
    (∑ y ∈ Fintype.piFinset S₁, (∏ a, W₁ a (y a)) *
      ∏ p ∈ orderedPairs J, K₁ p.1 p.2 (y p.1) (y p.2)) =
    ∑ z ∈ Fintype.piFinset S₀, (∏ a, W₀ a (z a)) *
      ∏ p ∈ orderedPairs J, K₀ p.1 p.2 (z p.1) (z p.2) := by
  classical
  have hinj : Set.InjOn (fun (z : J → σ₀) a => pad a (z a)) (Fintype.piFinset S₀) := by
    intro z hz z' hz' e
    funext a
    exact inj a _ (Fintype.mem_piFinset.1 hz a) _
      (Fintype.mem_piFinset.1 hz' a) (congrFun e a)
  have hsub : (Fintype.piFinset S₀).image (fun z a => pad a (z a)) ⊆
      Fintype.piFinset S₁ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    exact Fintype.mem_piFinset.2 fun a => maps a _ (Fintype.mem_piFinset.1 hz a)
  rw [← Finset.sum_subset hsub, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := Fintype.mem_piFinset.1 hz
    congr 1
    · exact Finset.prod_congr rfl fun a _ => weights a _ (hz' a)
    · exact Finset.prod_congr rfl fun p hp =>
        kernels p.1 p.2 (ne_of_lt ((mem_orderedPairs p).1 hp)) _ (hz' _) _ (hz' _)
  · intro y hy hny
    obtain ⟨a, ha⟩ : ∃ a, ∀ z ∈ S₀ a, pad a z ≠ y a := by
      by_contra hcon
      push Not at hcon
      choose z hz hzy using hcon
      exact hny (Finset.mem_image.2 ⟨z, Fintype.mem_piFinset.2 hz, funext hzy⟩)
    rw [Finset.prod_eq_zero (Finset.mem_univ a)
      (off a _ (Fintype.mem_piFinset.1 hy a) ha), zero_mul]

namespace Factored

/-- The source's local padding protocol for factored networks. The factor clause is retained
on source states and source labels, even though value preservation uses the interaction clause.
Only capacities between distinct vertices must agree. -/
structure StatePadding [LinearOrder J]
    (N₀ : Factored J σ₀ τ) (N₁ : Factored J σ₁ τ) (pad : J → σ₀ → σ₁) : Prop where
  /-- Allowed source states map to allowed target states. -/
  maps : ∀ a, ∀ z ∈ N₀.S a, pad a z ∈ N₁.S a
  /-- Padding is injective on the allowed states of each vertex. -/
  inj : ∀ a, ∀ z ∈ N₀.S a, ∀ z' ∈ N₀.S a, pad a z = pad a z' → z = z'
  /-- Target states outside the padding image have zero vertex weight. -/
  off : ∀ a, ∀ y ∈ N₁.S a, (∀ z ∈ N₀.S a, pad a z ≠ y) → N₁.W a y = 0
  /-- Vertex weights agree on padded source states. -/
  W : ∀ a, ∀ z ∈ N₀.S a, N₁.W a (pad a z) = N₀.W a z
  /-- Pair interactions agree on padded source states at distinct vertices. -/
  interaction : ∀ a b, a ≠ b → ∀ z ∈ N₀.S a, ∀ z' ∈ N₀.S b,
    N₁.interaction a b (pad a z) (pad b z') = N₀.interaction a b z z'
  /-- Directed capacities agree off the diagonal. -/
  c : ∀ a b, a ≠ b → N₁.c a b = N₀.c a b
  /-- Directed factors agree on source states and source labels. -/
  f : ∀ a b, a ≠ b → ∀ z ∈ N₀.S a, ∀ θ ∈ N₀.labelSet a b,
    N₁.f a b (pad a z) θ = N₀.f a b z θ

/-- A local state-padding certificate preserves both network value and directed total capacity. -/
theorem StatePadding.value_totalCapacity [Fintype J] [LinearOrder J]
    {N₀ : Factored J σ₀ τ} {N₁ : Factored J σ₁ τ} {pad : J → σ₀ → σ₁}
    (h : StatePadding N₀ N₁ pad) :
    N₁.value = N₀.value ∧ N₁.totalCapacity = N₀.totalCapacity := by
  constructor
  · exact sum_statePadding N₀.S N₁.S N₀.W N₁.W N₀.interaction N₁.interaction pad
      h.maps h.inj h.off h.W h.interaction
  · unfold totalCapacity
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
      h.c a b (Finset.ne_of_mem_erase hb).symm

end Factored

end TensorNetwork
