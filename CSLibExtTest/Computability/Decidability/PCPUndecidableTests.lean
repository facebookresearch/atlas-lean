/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.PCPUndecidable

@[expose] public section

/-!
# Tests for the undecidability of PCP

The simulation on concrete one-state machines, and the main statements.
-/

set_option autoImplicit false

open Turing Cslib.Decidability Cslib.Decidability.Rewriting Cslib.Decidability.TMRewriting

namespace CSLibExtTest.Computability.Decidability.PCPUndecidable

/-- The machine with no transitions halts on every input, so every start word rewrites to the
halting word. -/
example (l : List Bool) :
    Derives (rules (fun (_ : Unit) (_ : Bool) ↦ none)) (initWord l) haltWord :=
  (tm0HaltsOn_iff_derives _ l).mp <| Part.dom_iff_mem.mpr
    ⟨_, Part.mem_map _ (StateTransition.mem_eval.2 ⟨Relation.ReflTransGen.refl, rfl⟩)⟩

/-- A machine that keeps rewriting the symbol it reads never halts, so its start words never
rewrite to the halting word. -/
example (l : List Bool) :
    ¬Derives (rules (fun (_ : Unit) (a : Bool) ↦ some ((), TM0.Stmt.write a))) (initWord l)
      haltWord := by
  intro hd
  have h := (tm0HaltsOn_iff_derives _ l).mpr hd
  obtain ⟨_, hb⟩ := Part.dom_iff_mem.mp h
  obtain ⟨c, hc, -⟩ := (Part.mem_map_iff _).mp hb
  have hstop := (StateTransition.mem_eval.1 hc).2
  simp [TM0.step] at hstop

/-- The start word of `[true, false]` spells the initial configuration. -/
example : (initWord [true, false] : List (TMSym Bool Unit)) =
    [.lend, .state (), .tape true, .tape false, .rend] := rfl

/-- The three undecidability statements. -/
example : ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α),
    ¬TM2Decidable fun I : List (Rule α) × List α × List α ↦ NonemptyRules I.1 ∧ SR I :=
  exists_not_tm2Decidable_sr

example : ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α),
    ¬TM2Decidable fun P : List (Post.Domino α) ↦ Post.NonemptyWords P ∧ Post.MPCP P :=
  exists_not_tm2Decidable_mpcp

example : ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α), ¬TM2Decidable (Post.PCP (α := α)) :=
  exists_not_tm2Decidable_pcp

/-- A fixed finite Thue system has an undecidable word problem, and so does the uniform
problem. -/
example : ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α) (R : List (Rule α)),
    ¬TM2Decidable fun p : List α × List α ↦ Relation.EqvGen (Step R) p.1 p.2 :=
  exists_not_tm2Decidable_eqvGen

example : ∃ (α : Type) (_ : Fintype α) (_ : Primcodable α), ¬TM2Decidable (ThueWP (α := α)) :=
  exists_not_tm2Decidable_thueWP

/-- The rewrites from words with one control symbol are confluent. -/
example : Relation.Confluent (CtlStep (fun (_ : Unit) (_ : Bool) ↦ none)) := confluent_ctlStep

/-- The machine with no transitions: its start words are Thue-equivalent to the halting word. -/
example (l : List Bool) :
    Relation.EqvGen (Step (rules (fun (_ : Unit) (_ : Bool) ↦ none))) (initWord l) haltWord :=
  (tm0HaltsOn_iff_eqvGen l).mp <| Part.dom_iff_mem.mpr
    ⟨_, Part.mem_map _ (StateTransition.mem_eval.2 ⟨Relation.ReflTransGen.refl, rfl⟩)⟩

/-- A never-halting machine: even the symmetric closure does not connect its start words to the
halting word. -/
example (l : List Bool) :
    ¬Relation.EqvGen (Step (rules (fun (_ : Unit) (a : Bool) ↦ some ((), TM0.Stmt.write a))))
      (initWord l) haltWord := by
  intro hd
  have h := (tm0HaltsOn_iff_eqvGen l).mpr hd
  obtain ⟨_, hb⟩ := Part.dom_iff_mem.mp h
  obtain ⟨c, hc, -⟩ := (Part.mem_map_iff _).mp hb
  have hstop := (StateTransition.mem_eval.1 hc).2
  simp [TM0.step] at hstop

/-- A word with one control symbol has exactly one, and `⊢ H ⊣` rewrites to nothing. -/
example : ctlCount ([TMSym.lend, .state (), .tape true, .rend] : List (TMSym Bool Unit)) = 1 :=
  rfl

example (w : List (TMSym Bool Unit)) :
    ¬Step (rules (fun (_ : Unit) (_ : Bool) ↦ none)) haltWord w :=
  not_step_haltWord w

end CSLibExtTest.Computability.Decidability.PCPUndecidable
