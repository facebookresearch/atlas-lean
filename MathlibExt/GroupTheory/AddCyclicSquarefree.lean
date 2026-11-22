/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsAddCyclic_of_squarefree_natCard.lean` and
`P2M/Sol/S_IsAddCyclic_of_squarefree_natCard.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Additive cyclicity from squarefree cardinality

An additive commutative group whose cardinality is squarefree is additively
cyclic: transfer to the multiplicative group, which is then a Z-group, and a
Z-group whose exponent equals its cardinality is cyclic.
-/

@[expose] public section

/-- An additive commutative group of squarefree cardinality is additively
cyclic. -/
theorem IsAddCyclic.of_squarefree_natCard {A : Type*} [AddCommGroup A]
    (hA : Squarefree (Nat.card A)) : IsAddCyclic A := by
  have : Finite A := Nat.finite_of_card_ne_zero hA.ne_zero
  rw [← isCyclic_multiplicative_iff]
  have hM : Squarefree (Nat.card (Multiplicative A)) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  have : IsZGroup (Multiplicative A) := IsZGroup.of_squarefree hM
  exact IsCyclic.of_exponent_eq_card (IsZGroup.exponent_eq_card (Multiplicative A))
