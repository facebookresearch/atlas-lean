/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Strict local extrema

`IsStrictLocalMin` and `IsStrictLocalMax` strengthen Mathlib's local extrema
to strict inequalities on a punctured neighborhood. They use an arbitrary
topological domain and a codomain with a strict order. The bridge lemmas
recover Mathlib's non-strict extrema, and negation exchanges minima and maxima.
-/

@[expose] public section

open Filter Topology

/-- `IsStrictLocalMin f a` states that `f` has a strict local minimum at
`a`: `f a < f x` for all `x` sufficiently close to, but distinct from,
`a`. This is Mathlib's `IsLocalMin` with the inequality strengthened to
strict and the point `a` itself excluded. -/
def IsStrictLocalMin {α : Type*} {β : Type*} [TopologicalSpace α] [LT β]
    (f : α → β) (a : α) : Prop :=
  ∀ᶠ x in 𝓝[≠] a, f a < f x

/-- `IsStrictLocalMax f a` states that `f` has a strict local maximum at
`a`: `f x < f a` for all `x` sufficiently close to, but distinct from,
`a`. -/
def IsStrictLocalMax {α : Type*} {β : Type*} [TopologicalSpace α] [LT β]
    (f : α → β) (a : α) : Prop :=
  ∀ᶠ x in 𝓝[≠] a, f x < f a

/-- A strict local minimum is a local minimum in Mathlib's (non-strict)
sense. -/
theorem IsStrictLocalMin.isLocalMin {α : Type*} {β : Type*}
    [TopologicalSpace α] [Preorder β] {f : α → β} {a : α}
    (h : IsStrictLocalMin f a) : IsLocalMin f a := by
  show ∀ᶠ x in 𝓝 a, f a ≤ f x
  rw [← nhdsNE_sup_pure a, eventually_sup]
  exact ⟨h.mono fun x hx => hx.le, eventually_pure.mpr le_rfl⟩

/-- A strict local maximum is a local maximum in Mathlib's (non-strict)
sense. -/
theorem IsStrictLocalMax.isLocalMax {α : Type*} {β : Type*}
    [TopologicalSpace α] [Preorder β] {f : α → β} {a : α}
    (h : IsStrictLocalMax f a) : IsLocalMax f a := by
  show ∀ᶠ x in 𝓝 a, f x ≤ f a
  rw [← nhdsNE_sup_pure a, eventually_sup]
  exact ⟨h.mono fun x hx => hx.le, eventually_pure.mpr le_rfl⟩

/-- Negation turns a strict local minimum into a strict local maximum. -/
theorem IsStrictLocalMin.neg {α : Type*} {β : Type*} [TopologicalSpace α]
    [AddGroup β] [LT β] [AddLeftStrictMono β] [AddRightStrictMono β]
    {f : α → β} {a : α} (h : IsStrictLocalMin f a) :
    IsStrictLocalMax (fun x => -f x) a :=
  h.mono fun _ hx => neg_lt_neg_iff.mpr hx

/-- Negation turns a strict local maximum into a strict local minimum. -/
theorem IsStrictLocalMax.neg {α : Type*} {β : Type*} [TopologicalSpace α]
    [AddGroup β] [LT β] [AddLeftStrictMono β] [AddRightStrictMono β]
    {f : α → β} {a : α} (h : IsStrictLocalMax f a) :
    IsStrictLocalMin (fun x => -f x) a :=
  h.mono fun _ hx => neg_lt_neg_iff.mpr hx
