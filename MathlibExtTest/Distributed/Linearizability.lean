/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.Linearizability

@[expose] public section

/-- Boundary check specification: every sequence is legal. -/
private def specAll : SeqSpec := fun _ _ => True

/-- Boundary check: a one-operation history on object 1 (with
a valid interval) is linearizable, so its projection to
object 1 is too. -/
example : Linearizable specAll (proj [⟨1, 5, 6, 7, 0, 1⟩] 1) := by
  apply linearizable_project specAll (fun _ => trivial)
  refine ⟨[⟨1, 5, 6, 7, 0, 1⟩], List.Perm.refl _, ?_, fun _ => trivial⟩
  intro a ha b hb h
  simp at ha hb
  subst ha
  subst hb
  exact absurd h (by decide)
