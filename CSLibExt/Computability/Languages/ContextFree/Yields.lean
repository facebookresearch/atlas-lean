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

/-- **Yield of a sentential form.** For a context-free grammar $g$ with terminal alphabet
$T$, the relation "the sentential form $u$ yields the terminal word $w$" is the smallest
relation such that: the empty form yields the empty word; if $u$ yields $w$, then for every
terminal $a$ the form $a u$ yields $a w$; and if $A \to \alpha$ is a production of $g$,
$\alpha$ yields $w_1$ and $u$ yields $w_2$, then the form $A u$ yields $w_1 w_2$. -/
inductive Yields (g : ContextFreeGrammar T) : List (Symbol T g.NT) → List T → Prop
  | nil : Yields g [] []
  | terminal (a : T) {u : List (Symbol T g.NT)} {w : List T} (h : Yields g u w) :
      Yields g (Symbol.terminal a :: u) (a :: w)
  | nonterminal {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules)
      {u : List (Symbol T g.NT)} {w₁ w₂ : List T}
      (hout : Yields g r.output w₁) (hrest : Yields g u w₂) :
      Yields g (Symbol.nonterminal r.input :: u) (w₁ ++ w₂)

/-- **Concatenation of yields.** Let $g$ be a context-free grammar. If the sentential form
$u$ yields the terminal word $w_1$ and the sentential form $v$ yields the terminal word
$w_2$, then the concatenated form $u v$ yields $w_1 w_2$. -/
theorem Yields.append {u v : List (Symbol T g.NT)} {w₁ w₂ : List T}
    (hu : Yields g u w₁) (hv : Yields g v w₂) : Yields g (u ++ v) (w₁ ++ w₂) := by
  induction hu with
  | nil => exact hv
  | terminal a _ ih => simpa using Yields.terminal a ih
  | nonterminal hr hout _ _ ih =>
    simpa [List.append_assoc] using Yields.nonterminal hr hout ih

/-- **Splitting a yield over a concatenation.** Let $g$ be a context-free grammar. If the
concatenated sentential form $u v$ yields the terminal word $w$, then there are terminal
words $w_1$ and $w_2$ with $w = w_1 w_2$ such that $u$ yields $w_1$ and $v$ yields $w_2$. -/
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

/-- **Yield through one production.** Let $g$ be a context-free grammar and $A \to \alpha$ a
production of $g$. If $\alpha$ yields the terminal word $w$, then the one-symbol sentential
form $A$ yields $w$. -/
theorem yields_of_rule {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) {w : List T}
    (hout : Yields g r.output w) : Yields g [Symbol.nonterminal r.input] w := by
  simpa using Yields.nonterminal hr hout Yields.nil

/-- **Yields are derivable.** Let $g$ be a context-free grammar. If the sentential form $u$
yields the terminal word $w$, then $u$ derives $w$, read as a string of terminal symbols,
in $g$: that is, $u \Rightarrow^* w$ in zero or more rewriting steps. -/
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

/-- **Derivable terminal words are yields.** Let $g$ be a context-free grammar. If the
sentential form $u$ derives the terminal word $w$, read as a string of terminal symbols,
in $g$, then $u$ yields $w$.

The proof is the valuation argument: the languages yielded by the nonterminals form a
valuation. -/
theorem yields_of_derives {u : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives u (w.map Symbol.terminal)) : Yields g u w := by
  have hle := evalForm_le_of_derives (g := g) isValuation_yieldsFrom h
  rw [evalForm_map_terminal] at hle
  exact mem_evalForm_yieldsFrom_iff.mp (hle rfl)

/-- **Yields coincide with derivations of terminal words.** Let $g$ be a context-free grammar,
$u$ a sentential form of $g$ and $w$ a word of terminals. Then $u$ yields $w$ in $g$ if and only
if $u$ derives in $g$, by zero or more rewriting steps, the sentential form consisting of the
letters of $w$ read as terminals. -/
theorem yields_iff_derives {u : List (Symbol T g.NT)} {w : List T} :
    Yields g u w ↔ g.Derives u (w.map Symbol.terminal) :=
  ⟨derives_of_yields, yields_of_derives⟩

/-- **Language membership through yields.** Let $g$ be a context-free grammar with initial
nonterminal $S$. A terminal word $w$ belongs to the language of $g$ if and only if the
one-symbol sentential form $S$ yields $w$. -/
theorem mem_language_iff_yields {w : List T} :
    w ∈ g.language ↔ Yields g [Symbol.nonterminal g.initial] w := by
  rw [ContextFreeGrammar.mem_language_iff, yields_iff_derives]

end Cslib.Language
