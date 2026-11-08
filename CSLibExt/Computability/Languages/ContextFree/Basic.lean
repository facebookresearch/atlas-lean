/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.ContextFreeGrammar

/-!
# Context-free grammars: basic derivation API

Small derivation lemmas around Mathlib's `ContextFreeGrammar`, together with a
semantic valuation of sentential forms. A *valuation* assigns a language to
every nonterminal; a sentential form is interpreted by interpreting its
symbols in order and concatenating. When every production's interpreted
right-hand side is contained in the language assigned to its left-hand side,
every derivation can only shrink the interpretation. This is the soundness
half of the usual grammar constructions for the closure properties of
context-free languages, packaged once instead of once per construction.

## Main definitions

* `Cslib.Language.evalForm`: interpret a sentential form under an assignment
  of languages to nonterminals.
* `Cslib.Language.IsValuation`: an assignment under which every production is
  sound.

## Main results

* `Cslib.Language.evalForm_le_of_derives`: derivations shrink interpretations
  under a valuation.
* `Cslib.Language.language_le_of_valuation`: the language of a grammar is
  contained in the language a valuation assigns to its initial nonterminal.
* `Cslib.Language.derives_append`: derivations on two halves of a sentential
  form concatenate.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*} {N : Type*} {g : ContextFreeGrammar T}

/-- The language a single grammar symbol denotes under an assignment `V` of
languages to nonterminals: a terminal denotes its one-letter word, a
nonterminal denotes its assigned language. -/
def evalSymbol (V : N → Language T) : Symbol T N → Language T
  | .terminal a => {[a]}
  | .nonterminal A => V A

@[simp]
theorem evalSymbol_terminal (V : N → Language T) (a : T) :
    evalSymbol V (.terminal a) = {[a]} :=
  rfl

@[simp]
theorem evalSymbol_nonterminal (V : N → Language T) (A : N) :
    evalSymbol V (.nonterminal A) = V A :=
  rfl

/-- The language a sentential form denotes under an assignment `V` of
languages to nonterminals: concatenate the denotations of its symbols in
order. The empty form denotes `{[]}`. -/
def evalForm (V : N → Language T) : List (Symbol T N) → Language T
  | [] => 1
  | s :: u => evalSymbol V s * evalForm V u

@[simp]
theorem evalForm_nil (V : N → Language T) : evalForm V ([] : List (Symbol T N)) = 1 :=
  rfl

@[simp]
theorem evalForm_cons (V : N → Language T) (s : Symbol T N) (u : List (Symbol T N)) :
    evalForm V (s :: u) = evalSymbol V s * evalForm V u :=
  rfl

/-- Interpreting a concatenation of sentential forms is the product of the
interpretations. -/
theorem evalForm_append (V : N → Language T) (u v : List (Symbol T N)) :
    evalForm V (u ++ v) = evalForm V u * evalForm V v := by
  induction u with
  | nil => simp
  | cons s u ih => simp [ih, mul_assoc]

/-- A terminal word, read as a sentential form, denotes its singleton
language under every assignment. -/
theorem evalForm_map_terminal (V : N → Language T) (w : List T) :
    evalForm V (w.map Symbol.terminal) = {w} := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, evalForm_cons, evalSymbol_terminal, ih]
    ext x
    simp only [Language.mem_mul]
    constructor
    · rintro ⟨y, rfl, z, rfl, h⟩
      exact h.symm
    · rintro rfl
      exact ⟨[a], rfl, w, rfl, rfl⟩

/-- An assignment of languages to nonterminals is a *valuation* of a grammar
when every production is sound for it: the interpreted right-hand side is
contained in the language assigned to the left-hand side. -/
def IsValuation (g : ContextFreeGrammar T) (V : g.NT → Language T) : Prop :=
  ∀ r ∈ g.rules, evalForm V r.output ≤ V r.input

private theorem mul_le_mul_of_le {a b c d : Language T} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b ≤ c * d := by
  intro w hw
  obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
  exact Language.mem_mul.mpr ⟨x, hac hx, y, hbd hy, hxy⟩

/-- A single production step can only shrink the interpretation of a
sentential form under a valuation. -/
theorem evalForm_le_of_produces {V : g.NT → Language T} (hV : IsValuation g V)
    {u v : List (Symbol T g.NT)} (h : g.Produces u v) :
    evalForm V v ≤ evalForm V u := by
  obtain ⟨r, hr, hrew⟩ := h
  obtain ⟨p, q, hu, hv⟩ := ContextFreeRule.rewrites_iff.mp hrew
  have hsingle : evalForm V [Symbol.nonterminal r.input] = V r.input := by simp
  calc
    evalForm V v = evalForm V p * evalForm V r.output * evalForm V q := by
          rw [hv, evalForm_append, evalForm_append]
    _ ≤ evalForm V p * V r.input * evalForm V q :=
          mul_le_mul_of_le (mul_le_mul_of_le le_rfl (hV r hr)) le_rfl
    _ = evalForm V u := by
          rw [hu, evalForm_append, evalForm_append, hsingle]

/-- A derivation can only shrink the interpretation of a sentential form
under a valuation. -/
theorem evalForm_le_of_derives {V : g.NT → Language T} (hV : IsValuation g V)
    {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
    evalForm V v ≤ evalForm V u := by
  induction h with
  | refl => exact le_rfl
  | tail _ last ih => exact le_trans (evalForm_le_of_produces hV last) ih

/-- The language generated by a grammar is contained in the language that
any valuation assigns to its initial nonterminal. -/
theorem language_le_of_valuation {V : g.NT → Language T} (hV : IsValuation g V) :
    g.language ≤ V g.initial := by
  intro w hw
  have hle := evalForm_le_of_derives hV ((ContextFreeGrammar.mem_language_iff g w).mp hw)
  have hsingle : evalForm V [Symbol.nonterminal g.initial] = V g.initial := by simp
  rw [evalForm_map_terminal, hsingle] at hle
  exact hle rfl

/-- Derivations on the two halves of a sentential form concatenate. -/
theorem derives_append {u u' v v' : List (Symbol T g.NT)}
    (hu : g.Derives u u') (hv : g.Derives v v') :
    g.Derives (u ++ v) (u' ++ v') :=
  (hu.append_right v).trans (hv.append_left u')

/-- Rename the nonterminals in a grammar symbol. -/
def mapSymbol {N' : Type*} (f : N → N') : Symbol T N → Symbol T N'
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (f A)

@[simp]
theorem mapSymbol_terminal {N' : Type*} (f : N → N') (a : T) :
    mapSymbol f (Symbol.terminal (N := N) a) = Symbol.terminal (N := N') a :=
  rfl

@[simp]
theorem mapSymbol_nonterminal {N' : Type*} (f : N → N') (A : N) :
    mapSymbol f (Symbol.nonterminal (T := T) A) = Symbol.nonterminal (T := T) (f A) :=
  rfl

/-- Rename the nonterminals in a production. -/
def mapRule {N' : Type*} (f : N → N') (r : ContextFreeRule T N) :
    ContextFreeRule T N' :=
  ⟨f r.input, r.output.map (mapSymbol f)⟩

@[simp]
theorem mapRule_input {N' : Type*} (f : N → N') (r : ContextFreeRule T N) :
    (mapRule f r).input = f r.input :=
  rfl

@[simp]
theorem mapRule_output {N' : Type*} (f : N → N') (r : ContextFreeRule T N) :
    (mapRule f r).output = r.output.map (mapSymbol f) :=
  rfl

/-- Renaming nonterminals commutes with interpreting a sentential form. -/
theorem evalForm_map {N' : Type*} (f : N → N') (V : N' → Language T)
    (u : List (Symbol T N)) :
    evalForm V (u.map (mapSymbol f)) = evalForm (V ∘ f) u := by
  induction u with
  | nil => rfl
  | cons s u ih =>
    cases s <;> simp [ih]

theorem rewrites_map {N' : Type*} {f : N → N'} {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (h : r.Rewrites u v) :
    (mapRule f r).Rewrites (u.map (mapSymbol f)) (v.map (mapSymbol f)) := by
  induction h with
  | head s => simpa using ContextFreeRule.Rewrites.head (r := mapRule f r) (s.map (mapSymbol f))
  | cons x _ ih => exact ContextFreeRule.Rewrites.cons _ ih

/-- A derivation lifts along any nonterminal renaming whose image rules are
all present in the target grammar. No injectivity is needed for this
direction. -/
theorem derives_map_of_forall_mem {G : ContextFreeGrammar T} {f : g.NT → G.NT}
    (hsub : ∀ r ∈ g.rules, mapRule f r ∈ G.rules)
    {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
    G.Derives (u.map (mapSymbol f)) (v.map (mapSymbol f)) := by
  induction h with
  | refl => rfl
  | tail _ last ih =>
    obtain ⟨r, hr, hrew⟩ := last
    exact ih.trans_produces ⟨mapRule f r, hsub r hr, rewrites_map hrew⟩

/-- The language a grammar generates from a chosen nonterminal in place of
its initial nonterminal. -/
def languageFrom (g : ContextFreeGrammar T) (A : g.NT) : Language T :=
  { w : List T | g.Derives [Symbol.nonterminal A] (w.map Symbol.terminal) }

@[simp]
theorem mem_languageFrom {A : g.NT} {w : List T} :
    w ∈ languageFrom g A ↔ g.Derives [Symbol.nonterminal A] (w.map Symbol.terminal) :=
  Iff.rfl

theorem languageFrom_initial : languageFrom g g.initial = g.language :=
  rfl

/-- A word in the interpreted language of a sentential form, under the
canonical assignment `languageFrom`, is really derivable from that form. -/
theorem derives_of_mem_evalForm_languageFrom {u : List (Symbol T g.NT)} {w : List T}
    (hw : w ∈ evalForm (languageFrom g) u) :
    g.Derives u (w.map Symbol.terminal) := by
  induction u generalizing w with
  | nil =>
    simp only [evalForm_nil, Language.mem_one] at hw
    subst hw
    rfl
  | cons s u ih =>
    obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
    have hder_y := ih hy
    cases s with
    | terminal a =>
      simp only [evalSymbol_terminal] at hx
      subst hx
      subst hxy
      simpa using hder_y.append_left [Symbol.terminal (N := g.NT) a]
    | nonterminal A =>
      simp only [evalSymbol_nonterminal, mem_languageFrom] at hx
      subst hxy
      simpa [List.map_append] using derives_append hx hder_y

/-- The canonical assignment is a valuation of its own grammar. Together
with `language_le_of_valuation`, this characterizes the languages generated
from each nonterminal as the least valuation in the cases that matter for
grammar constructions. -/
theorem isValuation_languageFrom : IsValuation g (languageFrom g) := by
  intro r hr w hw
  have hder := derives_of_mem_evalForm_languageFrom hw
  have hstep : g.Produces [Symbol.nonterminal r.input] r.output :=
    ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩
  exact hstep.trans_derives hder

/-- Renaming with an injective function on nonterminals is injective on
symbols. -/
theorem mapSymbol_injective {N' : Type*} {f : N → N'} (hf : Function.Injective f) :
    Function.Injective (mapSymbol (T := T) f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [hf.eq_iff]

/-- Renaming with an injective function on nonterminals is injective on
productions, so renamed rule sets can be formed with `Finset.map`. -/
theorem mapRule_injective {N' : Type*} {f : N → N'} (hf : Function.Injective f) :
    Function.Injective (mapRule (T := T) f) := by
  intro r s h
  have hin : f r.input = f s.input := congrArg ContextFreeRule.input h
  have hout : r.output.map (mapSymbol f) = s.output.map (mapSymbol f) :=
    congrArg ContextFreeRule.output h
  cases r
  cases s
  simp only [ContextFreeRule.mk.injEq] at *
  exact ⟨hf hin, (List.map_injective_iff.mpr (mapSymbol_injective hf)) hout⟩

/-- Renaming nonterminals does not change a form of pure terminals. -/
@[simp]
theorem map_mapSymbol_terminal {N' : Type*} (f : N → N') (w : List T) :
    w.map (mapSymbol f ∘ Symbol.terminal) = w.map Symbol.terminal :=
  List.map_congr_left fun _a _ => rfl

/-- The empty language is context-free: take a grammar with no productions. -/
theorem IsContextFree.zero : (0 : Language T).IsContextFree :=
  ⟨⟨Unit, (), ∅⟩, ContextFreeGrammar.language_eq_zero_of_forall_input_ne_initial (by simp)⟩

/-- The language `{[]}` is context-free: one production erases the initial
nonterminal. -/
theorem IsContextFree.one : (1 : Language T).IsContextFree := by
  refine ⟨⟨Unit, (), {⟨(), []⟩}⟩, ?_⟩
  apply le_antisymm
  · have hV : IsValuation ⟨Unit, (), {⟨(), []⟩}⟩ (fun _ => (1 : Language T)) := by
      intro r hr
      simp only [Finset.mem_singleton] at hr
      subst hr
      simp
    exact language_le_of_valuation hV
  · intro w hw
    have hw' : w = [] := (Language.mem_one w).mp hw
    subst hw'
    apply (ContextFreeGrammar.mem_language_iff _ _).mpr
    exact ContextFreeGrammar.Produces.single
      ⟨⟨(), []⟩, by simp, ContextFreeRule.Rewrites.input_output⟩

/-- A language containing a single word is context-free: one production
spells the word out. -/
theorem IsContextFree.singleton_word (w : List T) : ({w} : Language T).IsContextFree := by
  refine ⟨⟨Unit, (), {⟨(), w.map Symbol.terminal⟩}⟩, ?_⟩
  apply le_antisymm
  · have hV :
        IsValuation ⟨Unit, (), {⟨(), w.map Symbol.terminal⟩}⟩ (fun _ => ({w} : Language T)) := by
      intro r hr
      simp only [Finset.mem_singleton] at hr
      subst hr
      exact le_of_eq (evalForm_map_terminal _ w)
    exact language_le_of_valuation hV
  · intro x hx
    have hx' : w = x := hx.symm
    subst hx'
    apply (ContextFreeGrammar.mem_language_iff _ _).mpr
    exact ContextFreeGrammar.Produces.single
      ⟨⟨(), w.map Symbol.terminal⟩, by simp, ContextFreeRule.Rewrites.input_output⟩

end Cslib.Language
