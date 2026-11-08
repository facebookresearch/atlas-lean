/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Basic

/-!
# Derivation forests (`Yields`)

A sentential form *yields* a terminal word when the word splits into one
contribution per symbol: a terminal contributes itself, and a nonterminal
contributes what one of its productions yields. This is the derivation-tree
view of Mathlib's `Derives`, stated as a forest over sentential forms.

The equivalence with `Derives` has one easy direction (assemble the steps)
and one direction that traditionally needs a derivation-splitting argument.
Here it goes through the valuation API: the assignment sending a nonterminal
to the words it yields is a valuation, so everything derivable is in the
interpretation, and the interpretation of a form unfolds back to `Yields`.

## Main definitions

* `Cslib.Language.Yields`: a sentential form yields a terminal word.

## Main results

* `Cslib.Language.yields_iff_derives`: a form yields `w` iff it derives the
  terminal form of `w`.
* `Cslib.Language.mem_language_iff_yields`: membership in a grammar's
  language in terms of yields from its initial nonterminal.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*} {g : ContextFreeGrammar T}

/-- A sentential form yields a terminal word symbol by symbol: the empty
form yields the empty word, a leading terminal contributes itself, and a
leading nonterminal first expands through one of its productions. -/
inductive Yields (g : ContextFreeGrammar T) : List (Symbol T g.NT) → List T → Prop
  | nil : Yields g [] []
  | terminal (a : T) {u : List (Symbol T g.NT)} {w : List T} (h : Yields g u w) :
      Yields g (Symbol.terminal a :: u) (a :: w)
  | nonterminal {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules)
      {u : List (Symbol T g.NT)} {w₁ w₂ : List T}
      (hout : Yields g r.output w₁) (hrest : Yields g u w₂) :
      Yields g (Symbol.nonterminal r.input :: u) (w₁ ++ w₂)

/-- Yields over an append of sentential forms concatenates contributions. -/
theorem Yields.append {u v : List (Symbol T g.NT)} {w₁ w₂ : List T}
    (hu : Yields g u w₁) (hv : Yields g v w₂) : Yields g (u ++ v) (w₁ ++ w₂) := by
  induction hu with
  | nil => exact hv
  | terminal a _ ih => simpa using Yields.terminal a ih
  | nonterminal hr hout _ _ ih =>
    simpa [List.append_assoc] using Yields.nonterminal hr hout ih

/-- A yield over an append of sentential forms splits into yields over the
two forms. -/
theorem Yields.append_inv {u v : List (Symbol T g.NT)} {w : List T}
    (h : Yields g (u ++ v) w) :
    ∃ w₁ w₂, w = w₁ ++ w₂ ∧ Yields g u w₁ ∧ Yields g v w₂ := by
  induction u generalizing w with
  | nil => exact ⟨[], w, rfl, Yields.nil, h⟩
  | cons s u ih =>
    cases s with
    | terminal a =>
      cases h with
      | terminal _ htail =>
        obtain ⟨w₁, w₂, rfl, hu, hv⟩ := ih htail
        exact ⟨a :: w₁, w₂, rfl, Yields.terminal a hu, hv⟩
    | nonterminal A =>
      cases h with
      | nonterminal hr hout hrest =>
        obtain ⟨w₁, w₂, rfl, hu, hv⟩ := ih hrest
        exact ⟨_ ++ w₁, w₂, by rw [List.append_assoc],
          Yields.nonterminal hr hout hu, hv⟩

/-- One production, expanded once at the head, gives a yield from its
left-hand side. -/
theorem yields_of_rule {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) {w : List T}
    (hout : Yields g r.output w) : Yields g [Symbol.nonterminal r.input] w := by
  simpa using Yields.nonterminal hr hout Yields.nil

/-- Everything a form yields, it derives in Mathlib's sense. -/
theorem derives_of_yields {u : List (Symbol T g.NT)} {w : List T}
    (h : Yields g u w) : g.Derives u (w.map Symbol.terminal) := by
  induction h with
  | nil => rfl
  | terminal a _ ih => simpa using ih.append_left [Symbol.terminal (N := g.NT) a]
  | nonterminal hr _ _ ihout ihrest =>
    have hstep : g.Produces ([Symbol.nonterminal ‹ContextFreeRule T g.NT›.input] ++ ‹_›)
        (‹ContextFreeRule T g.NT›.output ++ ‹_›) :=
      (ContextFreeGrammar.Produces.append_right
        ⟨_, hr, ContextFreeRule.Rewrites.input_output⟩ _)
    rw [List.map_append]
    exact hstep.trans_derives (derives_append ihout ihrest)

/-- The language yielded from a single nonterminal. -/
private def yieldsFrom (g : ContextFreeGrammar T) (A : g.NT) : Language T :=
  { w : List T | Yields g [Symbol.nonterminal A] w }

/-- Membership in the interpretation of a form under the yields assignment
is exactly the yields relation on that form. -/
private theorem mem_evalForm_yieldsFrom_iff {u : List (Symbol T g.NT)} {w : List T} :
    w ∈ evalForm (yieldsFrom g) u ↔ Yields g u w := by
  induction u generalizing w with
  | nil =>
    simp only [evalForm_nil, Language.mem_one]
    constructor
    · rintro rfl
      exact Yields.nil
    · intro h
      cases h
      rfl
  | cons s u ih =>
    cases s with
    | terminal a =>
      constructor
      · intro hw
        obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
        have hx' : x = [a] := hx
        subst hx'
        subst hxy
        exact Yields.terminal a (ih.mp hy)
      · intro h
        cases h with
        | terminal _ htail =>
          exact Language.mem_mul.mpr ⟨[a], rfl, _, ih.mpr htail, rfl⟩
    | nonterminal A =>
      constructor
      · intro hw
        obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
        have hx' : Yields g [Symbol.nonterminal A] x := hx
        cases hx' with
        | nonterminal hr hout hrest =>
          cases hrest
          simp only [List.append_nil] at hxy
          subst hxy
          exact Yields.nonterminal hr hout (ih.mp hy)
      · intro h
        cases h with
        | nonterminal hr hout hrest =>
          exact Language.mem_mul.mpr
            ⟨_, yields_of_rule hr hout, _, ih.mpr hrest, rfl⟩

private theorem isValuation_yieldsFrom : IsValuation g (yieldsFrom g) := by
  intro r hr w hw
  exact yields_of_rule hr (mem_evalForm_yieldsFrom_iff.mp hw)

/-- Everything a form derives as a terminal word, it yields. The proof is
the valuation argument: yields languages form a valuation. -/
theorem yields_of_derives {u : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives u (w.map Symbol.terminal)) : Yields g u w := by
  have hle := evalForm_le_of_derives (g := g) isValuation_yieldsFrom h
  rw [evalForm_map_terminal] at hle
  exact mem_evalForm_yieldsFrom_iff.mp (hle rfl)

/-- A sentential form yields a word iff it derives that word as terminals. -/
theorem yields_iff_derives {u : List (Symbol T g.NT)} {w : List T} :
    Yields g u w ↔ g.Derives u (w.map Symbol.terminal) :=
  ⟨derives_of_yields, yields_of_derives⟩

/-- Membership in a grammar's language, through yields. -/
theorem mem_language_iff_yields {w : List T} :
    w ∈ g.language ↔ Yields g [Symbol.nonterminal g.initial] w := by
  rw [ContextFreeGrammar.mem_language_iff, yields_iff_derives]

end Cslib.Language
