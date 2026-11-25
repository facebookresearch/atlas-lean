/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ScottishBook142
import Mathlib.Algebra.Group.PUnit

/-! # Tests for `MathlibExt.GroupTheory.ScottishBook142` -/

namespace MathlibExtTest.GroupTheory.ScottishBook142

open MathlibExt.GroupTheory.ScottishBook142Wanted

-- The trivial group is the full automorphism group of the empty relation on one point.
example : IsAutomorphismGroupOf PUnit PUnit (∅ : Set (PUnit × PUnit)) := by
  refine ⟨fun _ ↦ 1, fun _ _ _ ↦ Subsingleton.elim _ _, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro f _
    exact ⟨PUnit.unit, Equiv.ext fun _ ↦ Subsingleton.elim _ _⟩

-- On two points the empty relation also admits a swap, so the trivial action is not full.
example : ¬ IsAutomorphismGroupOf PUnit Bool (∅ : Set (Bool × Bool)) := by
  rintro ⟨φ, _, _, _, hfull⟩
  obtain ⟨x, hx⟩ := hfull 1 (by simp)
  obtain ⟨y, hy⟩ := hfull (Equiv.swap false true) (by simp)
  rw [Subsingleton.elim y x, hx] at hy
  have h := congrArg (fun f : Equiv.Perm Bool ↦ f false) hy
  simp at h

-- The existence theorem applies to a noncommutative group.
example : ∃ (Z : Type) (X : Set (Z × Z)), IsAutomorphismGroupOf (Equiv.Perm (Fin 3)) Z X :=
  everyGroupIsAutomorphismGroupOfBinaryRelation (Equiv.Perm (Fin 3))

-- The relation is available in the same universe for a group above `Type 0`.
example : ∃ (Z : Type 1) (X : Set (Z × Z)), IsAutomorphismGroupOf PUnit.{2} Z X :=
  everyGroupIsAutomorphismGroupOfBinaryRelation PUnit.{2}

end MathlibExtTest.GroupTheory.ScottishBook142
