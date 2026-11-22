/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.TM0Halting

@[expose] public section

/-!
# Tests for the single-tape halting problem
-/

set_option autoImplicit false

open Turing Cslib.Decidability

namespace CSLibExtTest.Computability.Decidability.TM0Halting

/-- The single-tape machine with no transitions halts on every input. -/
example (l : List Bool) : TM0HaltsOn (fun (_ : Unit) (_ : Bool) ↦ none) l :=
  Part.dom_iff_mem.mpr ⟨_, Part.mem_map _
    (StateTransition.mem_eval.2 ⟨Relation.ReflTransGen.refl, rfl⟩)⟩

/-- A machine that keeps writing the symbol it reads never halts. -/
example (l : List Bool) :
    ¬TM0HaltsOn (fun (_ : Unit) (a : Bool) ↦ some ((), TM0.Stmt.write a)) l := by
  intro h
  obtain ⟨_, hb⟩ := Part.dom_iff_mem.mp h
  obtain ⟨c, hc, -⟩ := (Part.mem_map_iff _).mp hb
  have hstop := (StateTransition.mem_eval.1 hc).2
  simp [TM0.step] at hstop

/-- The undecidable single-tape halting problem, as stated. -/
example : ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ) (_ : Fintype Γ) (_ : DecidableEq Γ)
    (_ : Primcodable Γ) (M : TM0.Machine Γ Λ) (S : Finset Λ),
    TM0.Supports M ↑S ∧ ¬TM2Decidable (TM0HaltsOn M) :=
  exists_not_tm2Decidable_tm0HaltsOn

end CSLibExtTest.Computability.Decidability.TM0Halting
