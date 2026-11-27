/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FiniteStateIrreducibleGenerators
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Set.Finite.Basic

/-! # Tests for finite-state automorphisms of the binary rooted tree -/

namespace MathlibExtTest.FiniteStateIrreducibleGenerators

open MathlibExt.GroupTheory.FiniteStateIrreducibleGeneratorsKourovka16Problem86Wanted

private def flipLetters : Equiv.Perm (List (Fin 2)) :=
  Equiv.listEquivOfEquiv (Equiv.swap 0 1)

-- Flipping every letter has the same section at every vertex, including the root.
private theorem flip_section (v : List (Fin 2)) : treeSection flipLetters v = flipLetters := by
  funext w
  simp [treeSection, flipLetters, Equiv.listEquivOfEquiv]

example : flipLetters ∈ finiteStateAutomorphisms 2 := by
  apply Subgroup.subset_closure
  constructor
  · intro v w
    exact ⟨flipLetters w, by simp [flipLetters, Equiv.listEquivOfEquiv], List.map_append⟩
  · apply (Set.finite_singleton (⇑flipLetters)).subset
    rintro _ ⟨v, rfl⟩
    exact flip_section v

-- Exchanging the root with its child violates prefix preservation.
example : ¬ IsTreeAutomorphism (Equiv.swap ([] : List (Fin 2)) [0]) := by
  intro h
  obtain ⟨u, _, hu⟩ := h [] [0]
  simp at hu

-- At the smallest allowed arity, removing any one member loses generation.
example : ∃ S : Set (finiteStateAutomorphisms 2), Subgroup.closure S = ⊤ ∧
    ∀ g ∈ S, Subgroup.closure (S \ {g}) ≠ ⊤ := by
  obtain ⟨S, hgen, hmin⟩ := finiteStateAutomorphismsIrreducibleGenerators_holds 2 le_rfl
  refine ⟨S, hgen, fun g hg => hmin _ ⟨Set.sdiff_subset, fun h => ?_⟩⟩
  exact (h hg).2 rfl

end MathlibExtTest.FiniteStateIrreducibleGenerators
