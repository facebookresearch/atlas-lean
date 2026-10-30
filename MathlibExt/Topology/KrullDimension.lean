/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.lean` and
`P2M/Sol/S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible

/-!
# Krull dimension of a proper closed subset

A proper closed subset of an irreducible set has Krull dimension at least
one less: push the irreducible closed subsets of the subset forward into
the ambient set, where they sit strictly below the top element.
-/

@[expose] public section

open Set Order TopologicalSpace Topology

universe u

namespace KrullDimAux

variable {X : Type u} [TopologicalSpace X] {Y Z : Set X}

private def topIC (hZ : IsIrreducible Z) : IrreducibleCloseds Z where
  carrier := univ
  isIrreducible' := by
    have : IrreducibleSpace Z := Subtype.irreducibleSpace hZ
    exact IrreducibleSpace.isIrreducible_univ Z
  isClosed' := isClosed_univ

private def push (hYZ : Y ⊆ Z) : IrreducibleCloseds Y → IrreducibleCloseds Z :=
  IrreducibleCloseds.map (inclusion hYZ) (continuous_inclusion hYZ)

private theorem push_strictMono (hYZ : Y ⊆ Z) : StrictMono (push (X := X) hYZ) :=
  IrreducibleCloseds.map_strictMono_of_isInducing (IsEmbedding.inclusion hYZ).isInducing

private theorem coe_push_subset (hYZ : Y ⊆ Z) (hY : IsClosed Y) (s : IrreducibleCloseds Y) :
    ((push hYZ s : IrreducibleCloseds Z) : Set Z) ⊆ (Subtype.val ⁻¹' Y : Set Z) := by
  change closure (inclusion hYZ '' (s : Set Y)) ⊆ _
  refine closure_minimal ?_ (hY.preimage continuous_subtype_val)
  rintro _ ⟨y, _, rfl⟩
  exact y.2

private theorem push_lt_top (hZ : IsIrreducible Z) (hYZ : Y ⊆ Z) (hY : IsClosed Y)
    (hne : Y ≠ Z) (s : IrreducibleCloseds Y) : push hYZ s < topIC hZ := by
  refine lt_of_le_of_ne (fun _ _ => trivial) fun h => hne ?_
  refine subset_antisymm hYZ fun z hz => ?_
  have hmem : (⟨z, hz⟩ : Z) ∈ ((push hYZ s : IrreducibleCloseds Z) : Set Z) := by
    rw [h]; trivial
  exact coe_push_subset hYZ hY s hmem

private theorem main (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z := by
  unfold topologicalKrullDim
  cases isEmpty_or_nonempty (IrreducibleCloseds Y) with
  | inl h =>
    rw [krullDim_eq_bot]
    exact bot_le
  | inr h =>
    rw [← krullDim_WithTop]
    let g : WithTop (IrreducibleCloseds Y) → IrreducibleCloseds Z :=
      fun a => WithTop.recTopCoe (topIC hZ) (fun s => push hYZ s) a
    refine krullDim_le_of_strictMono g fun a b hab => ?_
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe s =>
      induction b using WithTop.recTopCoe with
      | top => exact push_lt_top hZ hYZ hY hne s
      | coe t => exact push_strictMono hYZ (WithTop.coe_lt_coe.mp hab)

end KrullDimAux

/-- A proper closed subset of an irreducible set has Krull dimension at
least one less than the ambient set. -/
theorem IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z :=
  KrullDimAux.main hZ hY hYZ hne
