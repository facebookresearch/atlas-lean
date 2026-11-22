/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Translation.TM0Restrict

@[expose] public section

/-!
# Tests for restricting a single-tape machine to its support
-/

set_option autoImplicit false

open Turing MetaMathlibExt.TM0Restrict

namespace MathlibExtTest.Computability.TuringMachine.Translation.TM0Restrict

/-- A two-state machine on `ℕ` states that only ever visits state `0`. -/
def M : TM0.Machine Bool ℕ := fun q a ↦ if q = 0 then some (0, .write (!a)) else none

theorem supports : TM0.Supports M {0} :=
  ⟨rfl, fun {q a q' s} h hq ↦ by
    rw [Set.mem_singleton_iff] at hq ⊢
    subst hq
    simp only [M, ↓reduceIte, Option.mem_def, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm⟩

instance : Inhabited ({0} : Set ℕ) := ⟨⟨0, rfl⟩⟩

/-- The restriction evaluates like the original machine. -/
example (l : List Bool) : TM0.eval (restrict supports) l = TM0.eval M l :=
  eval_restrict supports rfl l

end MathlibExtTest.Computability.TuringMachine.Translation.TM0Restrict
