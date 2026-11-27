/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.MonotonicSemilattice
import Mathlib.Order.Lattice

namespace Cslib.Distributed

private abbrev ExampleObject := StateBasedReplicatedObject ℕ Unit (fun _ => Bool) Unit

private def exampleObject : ExampleObject where
  initial := 1
  query := fun _ s => (decide (s = 3), if s = 1 then 2 else s)
  update := fun _ s => if s = 1 then 3 else s
  merge := (· ⊔ ·)

example : exampleObject.IsMonotonicSemilattice := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro _ s
    by_cases hs : s = 1
    · subst s
      change (1 : ℕ) ≤ 3
      decide
    · simp [exampleObject, hs]
  · intro _ s _
    by_cases hs : s = 1
    · subst s
      change decide ((2 : ℕ) = 3) = decide ((1 : ℕ) = 3)
      decide
    · simp [exampleObject, hs]

-- Initial state need not be bottom, and a query may change the actual state.
example : exampleObject.initial ≠ 0 := by decide
example : (exampleObject.query () 1).2 ≠ 1 := by decide

-- The update raises 1 to 3 and fixes 2, so it is not monotone.
example : ¬ Monotone (exampleObject.update ()) := by
  intro h
  have h32 : (3 : ℕ) ≤ 2 := h (show (1 : ℕ) ≤ 2 by decide)
  exact (by decide : ¬ (3 : ℕ) ≤ 2) h32

private def visibleQueryChange : ExampleObject :=
  { exampleObject with query := fun _ s => (decide (s = 3), if s = 1 then 3 else s) }

example : ¬ visibleQueryChange.IsMonotonicSemilattice := by
  intro h
  have bad : (true : Bool) = false := h.2.2 () 1 ()
  cases bad

private def decreasingUpdate : ExampleObject :=
  { exampleObject with update := fun _ _ => 0 }

example : ¬ decreasingUpdate.IsMonotonicSemilattice := by
  intro h
  exact (by decide : ¬ (1 : ℕ) ≤ 0) (h.2.1 () 1)

private def projectionMerge : ExampleObject :=
  { exampleObject with merge := fun _ t => t }

example : ¬ projectionMerge.IsMonotonicSemilattice := by
  intro h
  exact (by decide : (0 : ℕ) ≠ (1 ⊔ 0)) (h.1 1 0)

end Cslib.Distributed
