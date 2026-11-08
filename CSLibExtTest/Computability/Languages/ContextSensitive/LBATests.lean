/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextSensitive.LBA

/-!
# Tests for the linear bounded automaton API

A concrete two-state LBA over `Bool` that accepts `[true]` in one step,
with the grammar of the LBA deriving `[true]`, plus the boundary
regression: a boundary-sensitive LBA accepting exactly `[true]` and
rejecting `[true, false]`.
-/

public section

set_option autoImplicit false

namespace Cslib.Language.LBATests

open Cslib.Language.LinearBoundedAutomaton

/-- The two-state LBA over `Bool` that accepts `[true]`: from the initial
state `false`, reading `true`, it moves to the accepting state `true` and
stays. This machine ignores the boundary tag. -/
def boolLBA : LinearBoundedAutomaton Bool Bool where
  q₀ := false
  qAcc := true
  delta := fun q read _ ↦
    if q = false ∧ read = some true then {(true, some true, LBAMove.stay)} else ∅

/-- The LBA accepts `[true]` in one step. -/
theorem boolLBA_accepts_true : boolLBA.Accepts [true] := by
  refine ⟨⟨true, [some true], 0⟩, ?_, rfl⟩
  refine Relation.ReflTransGen.single ?_
  exact ⟨true, some true, LBAMove.stay, by simp [boolLBA, LinearBoundedAutomaton.initCfg],
    rfl, by simp [LBAMove.legal, LinearBoundedAutomaton.initCfg]⟩

/-- A left move from an out-of-bounds head is illegal, even though the
head is positive: legality also requires the source head to be on the
tape. Regression test: `LBAMove.legal .left 2 1` used to hold. -/
theorem left_legal_rejects_out_of_bounds : ¬ LBAMove.left.legal 2 1 := by
  intro h
  obtain ⟨-, h2⟩ := h
  omega

/-- A left move from an in-bounds head is legal. -/
theorem left_legal_accepts_in_bounds : LBAMove.left.legal 1 2 :=
  ⟨by omega, by omega⟩

/-- No step leaves a configuration whose head is off the tape: every
move is illegal from head `2` on a one-cell tape, whatever the
transition function offers. -/
theorem step_rejects_out_of_bounds_head (c' : LBAConfig Bool Bool) :
    ¬ boolLBA.Step ⟨false, [some true], 2⟩ c' := by
  intro h
  obtain ⟨_, _, mv, -, -, hlegal⟩ := h
  cases mv <;> simp [LBAMove.legal] at hlegal

/-- The context-sensitive grammar with the sole rule `S → true`: it
generates exactly `[true]`. -/
def trueOnlyGrammar : CSGrammar Bool Unit where
  rules := [([.nonterminal ()], [.terminal true])]
  initial := ()

/-- The `[true]`-only grammar is context-sensitive: its sole production
has a nonterminal on the left and does not shrink. -/
theorem trueOnlyGrammar_contextSensitive : IsContextSensitive trueOnlyGrammar := by
  intro r hr
  simp only [trueOnlyGrammar, List.mem_singleton] at hr
  obtain rfl := hr
  simp [Symbol.isNonterminal]

/-- The LBA that accepts exactly `[true]`: from the initial state, reading
`true` on a one-cell tape (boundary `both`), it moves to the accepting
state and stays; every other state/symbol/boundary combination has no
transition. A boundary-blind machine could not do this: every accepting
run on `w` would replay on every `w ++ v`. -/
def trueOnlyLBA : LinearBoundedAutomaton Bool Bool where
  q₀ := false
  qAcc := true
  delta := fun q read bnd ↦
    if q = false ∧ read = some true ∧ bnd = .both then
      {(true, some true, LBAMove.stay)}
    else ∅

/-- The boundary-sensitive LBA accepts `[true]` in one step. -/
theorem trueOnlyLBA_accepts_true : trueOnlyLBA.Accepts [true] := by
  refine ⟨⟨true, [some true], 0⟩, ?_, rfl⟩
  refine Relation.ReflTransGen.single ?_
  exact ⟨true, some true, LBAMove.stay,
    by simp [trueOnlyLBA, LinearBoundedAutomaton.initCfg, LBABoundary.ofHead],
    rfl, by simp [LBAMove.legal, LinearBoundedAutomaton.initCfg]⟩

/-- The boundary-sensitive LBA rejects `[true, false]`: the initial
configuration has boundary `left`, not `both`, so its transition set is
empty and no run leaves the initial configuration, whose state is not
accepting. This is the regression test for boundary blindness: a machine
that cannot observe the boundary would accept `[true, false]` whenever it
accepts `[true]`. -/
theorem trueOnlyLBA_rejects_true_false : ¬ trueOnlyLBA.Accepts [true, false] := by
  rintro ⟨c, hrun, hstate⟩
  have hEq : c = trueOnlyLBA.initCfg [true, false] := by
    clear hstate
    induction hrun with
    | refl => rfl
    | tail _ hstep ih =>
      exfalso
      rw [ih] at hstep
      obtain ⟨_, _, _, hmem, _, _⟩ := hstep
      simp [trueOnlyLBA, LinearBoundedAutomaton.initCfg, LBABoundary.ofHead] at hmem
  rw [hEq] at hstate
  simp [trueOnlyLBA, LinearBoundedAutomaton.initCfg] at hstate

/-- The grammar of the LBA derives `[true]`. -/
theorem boolLBA_grammar_derives_true :
    [true] ∈ Cslib.Language.language boolLBA.lbaGrammar :=
  Cslib.Language.LinearBoundedAutomaton.lba_accepts_implies_grammar_derives
    (by simp) boolLBA_accepts_true

#print axioms Cslib.Language.LinearBoundedAutomaton.lba_accepts_implies_grammar_derives
#print axioms Cslib.Language.LinearBoundedAutomaton.lbaGrammar_contextSensitive

end Cslib.Language.LBATests
