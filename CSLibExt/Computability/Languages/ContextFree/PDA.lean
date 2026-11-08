/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.PDA.Basic
public import CSLibExt.Computability.Languages.ContextFree.Yields
public import Mathlib.Data.Finset.Union

/-!
# From context-free grammars to pushdown automata

The one-state PDA whose stack is a sentential form: popping a nonterminal
by an `ε`-transition pushes a production output, and popping a terminal
consumes the matching input letter. Its empty-stack computations from a
stack `u` on input `w` are exactly the `Yields` derivations of `w` from
`u`, so it accepts the grammar's language.

## Main results

* `Cslib.Language.ContextFreeGrammar.cfgPDA_accepts`: the simulating PDA accepts exactly the
  grammar's language.
* `Cslib.Language.ContextFreeGrammar.cfgPDA_finitelySupported`: the simulating PDA has finite
  support, as a standard pushdown automaton must.
* `Cslib.Language.IsContextFree.exists_pda_accepts`: every context-free
  language is accepted by some PDA.
* `Cslib.Language.IsContextFree.exists_finitely_supported_pda_accepts`: every context-free
  language is accepted by some finitely supported PDA.
-/

@[expose] public section

namespace Cslib.Language

open Automata

attribute [local instance] Classical.propDecidable

variable {T : Type*} {g : ContextFreeGrammar T}

/-- Transitions of the sentential-form PDA: expand a nonterminal by one of
its productions on `ε`, or consume a matching terminal letter. -/
noncomputable def cfgStep (g : ContextFreeGrammar T) :
    Unit → Option T → Symbol T g.NT → Finset (Unit × List (Symbol T g.NT))
  | _, none, .nonterminal A =>
      (g.rules.filter fun r => r.input = A).image fun r => ((), r.output)
  | _, some a, .terminal b => if a = b then {((), [])} else ∅
  | _, some _, .nonterminal _ => ∅
  | _, none, .terminal _ => ∅

/-- The one-state PDA simulating derivations of `g` on its stack. -/
noncomputable def cfgPDA (g : ContextFreeGrammar T) :
    PDA T Unit (Symbol T g.NT) where
  step := cfgStep g
  start := ()
  startStack := .nonterminal g.initial

private theorem mem_cfgStep_nonterminal {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    ((), r.output) ∈ cfgStep g () none (.nonterminal r.input) :=
  Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩, rfl⟩

private theorem mem_cfgStep_terminal (a : T) :
    ((), []) ∈ cfgStep g () (some a) (.terminal (N := g.NT) a) := by
  simp [cfgStep]

/-- Every yield is an emptying PDA computation from the corresponding
stack. -/
private theorem derives_cfgPDA_of_yields {u : List (Symbol T g.NT)} {w : List T}
    (h : Yields g u w) :
    (cfgPDA g).Derives ⟨(), w, u⟩ ⟨(), [], []⟩ := by
  induction h with
  | nil => rfl
  | terminal a _ ih =>
    exact Relation.ReflTransGen.head
      (PDA.Step.consume (M := cfgPDA g) (mem_cfgStep_terminal a)) ih
  | nonterminal hr _ _ ihout ihrest =>
    rename_i r₀ u₀ w₁ w₂ hout hrest
    have hstep : (cfgPDA g).Step
        (⟨(), w₁ ++ w₂, Symbol.nonterminal r₀.input :: u₀⟩ :
          PDA.Config T Unit (Symbol T g.NT))
        ⟨(), w₁ ++ w₂, r₀.output ++ u₀⟩ :=
      PDA.Step.epsilon (M := cfgPDA g) (mem_cfgStep_nonterminal hr)
    have hmid : (cfgPDA g).Derives ⟨(), w₁ ++ w₂, r₀.output ++ u₀⟩ ⟨(), w₂, u₀⟩ := by
      have h := ihout.append_input_stack w₂ u₀
      simpa using h
    exact ((Relation.ReflTransGen.single hstep).trans hmid).trans ihrest

/-- Backward simulation: if the end configuration's stack yields its
remaining input, so does the start configuration's stack. -/
private theorem yields_of_derives_cfgPDA_aux :
    ∀ {c c' : PDA.Config T Unit (Symbol T g.NT)},
      (cfgPDA g).Derives c c' → Yields g c'.stack c'.input → Yields g c.stack c.input := by
  intro c c' h
  induction h with
  | refl => exact fun hy => hy
  | tail _ hstep ih =>
    intro hy
    apply ih
    cases hstep with
    | @epsilon q q' w γ s pushed hmem =>
      cases γ with
      | terminal b =>
        exfalso
        have hmem' : (q', pushed) ∈ cfgStep g q none (Symbol.terminal (N := g.NT) b) :=
          hmem
        simp [cfgStep] at hmem'
      | nonterminal A =>
        have hmem' : (q', pushed) ∈ cfgStep g q none (Symbol.nonterminal (T := T) A) :=
          hmem
        obtain ⟨r, hr, hrfl⟩ := Finset.mem_image.mp hmem'
        have hrA : r.input = A := (Finset.mem_filter.mp hr).2
        have hpushed : pushed = r.output := by
          have h2 : ((), r.output) = (q', pushed) := hrfl
          exact (Prod.mk.injEq ..).mp h2.symm |>.2
        subst hrA
        subst hpushed
        obtain ⟨w₁, w₂, rfl, hout, hrest⟩ := Yields.append_inv hy
        exact Yields.nonterminal (Finset.mem_filter.mp hr).1 hout hrest
    | @consume q q' a w γ s pushed hmem =>
      cases γ with
      | nonterminal A =>
        exfalso
        have hmem' : (q', pushed) ∈
            cfgStep g q (some a) (Symbol.nonterminal (T := T) A) := hmem
        simp [cfgStep] at hmem'
      | terminal b =>
        have hmem' : (q', pushed) ∈ cfgStep g q (some a) (Symbol.terminal (N := g.NT) b) :=
          hmem
        simp only [cfgStep] at hmem'
        split at hmem'
        swap
        · simp at hmem'
        rename_i hab
        subst hab
        have hpushed : pushed = [] := by
          have h2 : (q', pushed) ∈ ({((), [])} : Finset (Unit × List (Symbol T g.NT))) :=
            hmem'
          exact (Prod.mk.injEq ..).mp (Finset.mem_singleton.mp h2) |>.2
        subst hpushed
        simpa using Yields.terminal a hy

/-- Every emptying PDA computation is a yield. -/
private theorem yields_of_derives_cfgPDA {u : List (Symbol T g.NT)} {w : List T}
    (h : (cfgPDA g).Derives ⟨(), w, u⟩ ⟨(), [], []⟩) : Yields g u w :=
  yields_of_derives_cfgPDA_aux h Yields.nil

/-- The simulating PDA accepts exactly the grammar's language. -/
theorem ContextFreeGrammar.cfgPDA_accepts (g : ContextFreeGrammar T) :
    (cfgPDA g).accepts = g.language := by
  ext w
  constructor
  · rintro ⟨q, h⟩
    cases q
    exact mem_language_iff_yields.mpr (yields_of_derives_cfgPDA h)
  · intro hw
    exact ⟨(), derives_cfgPDA_of_yields (mem_language_iff_yields.mp hw)⟩

/-- Every context-free language is accepted by empty stack by a one-state
pushdown automaton whose stack alphabet is the grammar's symbols. -/
theorem IsContextFree.exists_pda_accepts {L : Language T} (hL : L.IsContextFree) :
    ∃ (g : ContextFreeGrammar T) (M : PDA T Unit (Symbol T g.NT)), M.accepts = L := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨g, cfgPDA g, ContextFreeGrammar.cfgPDA_accepts g⟩

/-- The simulating PDA is finitely supported: its only reachable stack
symbols are the initial nonterminal and the finitely many symbols occurring
in production outputs, and the only input labels it can consume from a
supported stack symbol are terminals occurring in production outputs. -/
theorem ContextFreeGrammar.cfgPDA_finitelySupported (g : ContextFreeGrammar T) :
    (cfgPDA g).FinitelySupported := by
  classical
  refine ⟨{()}, insert (Symbol.nonterminal g.initial)
    (g.rules.biUnion fun r => r.output.toFinset),
    g.rules.biUnion fun r =>
      (r.output.filterMap fun s => match s with
        | Symbol.terminal a => some a
        | Symbol.nonterminal _ => none).toFinset,
    Finset.mem_singleton_self (), Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro q _ opt γ _ y hy
    cases q
    refine ⟨Finset.mem_singleton_self (), ?_⟩
    intro γ' hγ'
    have hy' : y ∈ cfgStep g () opt γ := hy
    cases opt with
    | none =>
      cases γ with
      | terminal b => simp [cfgStep] at hy'
      | nonterminal A =>
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy'
        exact Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr
            ⟨r, (Finset.mem_filter.mp hr).1, List.mem_toFinset.mpr hγ'⟩)
    | some a =>
      cases γ with
      | nonterminal A => simp [cfgStep] at hy'
      | terminal b =>
        simp only [cfgStep] at hy'
        split at hy'
        swap
        · simp at hy'
        rename_i hab
        subst hab
        obtain rfl : y = ((), []) := Finset.mem_singleton.mp hy'
        exact absurd hγ' List.not_mem_nil
  · intro q _ a ha γ hγ
    cases q
    cases γ with
    | nonterminal A => simp [cfgPDA, cfgStep]
    | terminal b =>
      have hb : b ∈ g.rules.biUnion fun r =>
          (r.output.filterMap fun s => match s with
            | Symbol.terminal a => some a
            | Symbol.nonterminal _ => none).toFinset := by
        cases Finset.mem_insert.mp hγ with
        | inl heq => cases heq
        | inr hmem =>
          obtain ⟨r, hr, hrout⟩ := Finset.mem_biUnion.mp hmem
          exact Finset.mem_biUnion.mpr ⟨r, hr,
            List.mem_toFinset.mpr (List.mem_filterMap.mpr
              ⟨Symbol.terminal b, List.mem_toFinset.mp hrout, rfl⟩)⟩
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      simp [cfgPDA, cfgStep, hab]

/-- Every context-free language is accepted by empty stack by a finitely
supported one-state pushdown automaton, the standard finite model. -/
theorem IsContextFree.exists_finitely_supported_pda_accepts {L : Language T}
    (hL : L.IsContextFree) :
    ∃ (g : ContextFreeGrammar T) (M : PDA T Unit (Symbol T g.NT)),
      M.FinitelySupported ∧ M.accepts = L := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨g, cfgPDA g, ContextFreeGrammar.cfgPDA_finitelySupported g,
    ContextFreeGrammar.cfgPDA_accepts g⟩

end Cslib.Language
