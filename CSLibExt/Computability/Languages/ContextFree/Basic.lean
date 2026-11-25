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

/-- **Interpretation of a grammar symbol.** Under an assignment $V$ of languages to nonterminals, a
terminal $a$ denotes the language containing only the one-letter word $a$, and a nonterminal $A$
denotes its assigned language $V(A)$. -/
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

/-- **Interpretation of a sentential form.** Under an assignment $V$ of languages to nonterminals, a
sentential form denotes the concatenation, in order, of the languages its symbols denote: a
terminal $a$ denotes the language containing only the one-letter word $a$, and a nonterminal $A$
denotes $V(A)$. The empty sentential form denotes the language containing only the empty word. -/
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

/-- **Interpretation of a concatenation.** For every assignment $V$ of languages to nonterminals and
all sentential forms $u$ and $v$, the language that $uv$ denotes under $V$ is the concatenation of
the languages that $u$ and $v$ denote under $V$. -/
theorem evalForm_append (V : N → Language T) (u v : List (Symbol T N)) :
    evalForm V (u ++ v) = evalForm V u * evalForm V v := by
  induction u with
  | nil => simp
  | cons s u ih => simp [ih, mul_assoc]

/-- **A terminal word denotes its singleton.** Under every assignment of languages to
nonterminals, a terminal word $w$, read as a sentential form, denotes the singleton language
$\{w\}$. -/
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

/-- **Valuation of a grammar.** Let $g$ be a context-free grammar with terminals $T$, and let $V$
assign a language over $T$ to each nonterminal of $g$. Interpret a sentential form under $V$ by
sending each terminal $a$ to the language $\{a\}$ of the one-letter word $a$ and each nonterminal
$B$ to $V(B)$, and concatenating these languages in order (the empty form is interpreted as
$\{\varepsilon\}$). Then $V$ is a *valuation* of $g$ when, for every production $A \to u$
of $g$, the interpretation of $u$ under $V$ is contained in $V(A)$. -/
def IsValuation (g : ContextFreeGrammar T) (V : g.NT → Language T) : Prop :=
  ∀ r ∈ g.rules, evalForm V r.output ≤ V r.input

private theorem mul_le_mul_of_le {a b c d : Language T} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b ≤ c * d := by
  intro w hw
  obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
  exact Language.mem_mul.mpr ⟨x, hac hx, y, hbd hy, hxy⟩

/-- **A production step shrinks interpretations under a valuation.** Let $g$ be a context-free
grammar and $V$ a valuation of $g$. If a sentential form $u$ rewrites to $v$ by one production of
$g$, then the language that $v$ denotes under $V$ is contained in the language that $u$ denotes
under $V$. -/
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

/-- **Derivations shrink interpretations under a valuation.** Let $g$ be a context-free grammar and
$V$ a valuation of $g$. If a sentential form $u$ derives $v$ in $g$ (in zero or more steps), then
the language that $v$ denotes under $V$ is contained in the language that $u$ denotes under $V$. -/
theorem evalForm_le_of_derives {V : g.NT → Language T} (hV : IsValuation g V)
    {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
    evalForm V v ≤ evalForm V u := by
  induction h with
  | refl => exact le_rfl
  | tail _ last ih => exact le_trans (evalForm_le_of_produces hV last) ih

/-- **Valuations bound the language of a grammar.** For every context-free grammar $g$ and every
valuation $V$ of $g$, the language generated by $g$ is contained in $V(S)$, where $S$ is the
initial nonterminal of $g$. -/
theorem language_le_of_valuation {V : g.NT → Language T} (hV : IsValuation g V) :
    g.language ≤ V g.initial := by
  intro w hw
  have hle := evalForm_le_of_derives hV ((ContextFreeGrammar.mem_language_iff g w).mp hw)
  have hsingle : evalForm V [Symbol.nonterminal g.initial] = V g.initial := by simp
  rw [evalForm_map_terminal, hsingle] at hle
  exact hle rfl

/-- **Concatenating derivations.** Let $g$ be a context-free grammar and let $u$, $u'$, $v$, $v'$
be sentential forms of $g$. If $u$ derives $u'$ and $v$ derives $v'$ in $g$ (each in zero or more
steps), then the concatenation $uv$ derives $u'v'$ in $g$. -/
theorem derives_append {u u' v v' : List (Symbol T g.NT)}
    (hu : g.Derives u u') (hv : g.Derives v v') :
    g.Derives (u ++ v) (u' ++ v') :=
  (hu.append_right v).trans (hv.append_left u')

/-- **Renaming the nonterminals of a symbol.** Given a map $f$ from nonterminals $N$ to
nonterminals $N'$, renaming a grammar symbol by $f$ leaves a terminal $a$ unchanged and sends a
nonterminal $A$ to the nonterminal $f(A)$. -/
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

/-- **Renaming the nonterminals of a production.** Given a map $f$ from nonterminals $N$ to
nonterminals $N'$, the renaming by $f$ of a production $A \to u$ is the production
$f(A) \to u'$, where $u'$ is obtained from $u$ by replacing each nonterminal $B$ with $f(B)$ and
leaving each terminal unchanged. -/
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

/-- **Interpretation after renaming nonterminals.** Let $f \colon N \to N'$ be a map of
nonterminals, extended to sentential forms by renaming each nonterminal and keeping each terminal,
and let $V$ assign a language to each nonterminal in $N'$. For every sentential form $u$ over $N$,
the language that $f(u)$ denotes under $V$ equals the language that $u$ denotes under the
assignment $V \circ f$. -/
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

/-- **Derivations transfer along a renaming of nonterminals.** Let $g$ and $G$ be context-free
grammars over the same terminal alphabet, and let $f$ map the nonterminals of $g$ to those of $G$.
Extend $f$ to symbols and sentential forms by renaming each nonterminal and keeping each terminal.
Suppose that for every production $A \to \alpha$ of $g$, the renamed production $f(A) \to f(\alpha)$
is a production of $G$. Then whenever a sentential form $u$ derives $v$ in $g$ (in zero or more
steps), $f(u)$ derives $f(v)$ in $G$.

No injectivity of $f$ is needed for this direction. -/
theorem derives_map_of_forall_mem {G : ContextFreeGrammar T} {f : g.NT → G.NT}
    (hsub : ∀ r ∈ g.rules, mapRule f r ∈ G.rules)
    {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
    G.Derives (u.map (mapSymbol f)) (v.map (mapSymbol f)) := by
  induction h with
  | refl => rfl
  | tail _ last ih =>
    obtain ⟨r, hr, hrew⟩ := last
    exact ih.trans_produces ⟨mapRule f r, hsub r hr, rewrites_map hrew⟩

/-- **Language generated from a nonterminal.** For a context-free grammar $g$ and a nonterminal
$A$ of $g$, the language generated by $g$ from $A$ is the set of words $w$ over the terminals of
$g$ such that $g$ derives $w$ from the one-symbol sentential form $A$. It is the language of $g$
with $A$ in place of the initial nonterminal. -/
def languageFrom (g : ContextFreeGrammar T) (A : g.NT) : Language T :=
  { w : List T | g.Derives [Symbol.nonterminal A] (w.map Symbol.terminal) }

@[simp]
theorem mem_languageFrom {A : g.NT} {w : List T} :
    w ∈ languageFrom g A ↔ g.Derives [Symbol.nonterminal A] (w.map Symbol.terminal) :=
  Iff.rfl

theorem languageFrom_initial : languageFrom g g.initial = g.language :=
  rfl

/-- **Words of the canonical interpretation are derivable.** Let $g$ be a context-free grammar and
assign to each nonterminal $A$ of $g$ the language of terminal words that $g$ derives from $A$. If a
terminal word $w$ lies in the language that a sentential form $u$ of $g$ denotes under this
assignment, then $u$ derives $w$ in $g$. -/
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

/-- **The languages generated from each nonterminal form a valuation.** For every context-free
grammar $g$, the assignment that sends each nonterminal $A$ of $g$ to the language generated by
$g$ from $A$ is a valuation of $g$. -/
theorem isValuation_languageFrom : IsValuation g (languageFrom g) := by
  intro r hr w hw
  have hder := derives_of_mem_evalForm_languageFrom hw
  have hstep : g.Produces [Symbol.nonterminal r.input] r.output :=
    ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩
  exact hstep.trans_derives hder

/-- **Injective renamings are injective on symbols.** If $f$ is an injective map from
nonterminals $N$ to nonterminals $N'$, then renaming grammar symbols by $f$, which fixes each
terminal and sends each nonterminal $A$ to $f(A)$, is injective. -/
theorem mapSymbol_injective {N' : Type*} {f : N → N'} (hf : Function.Injective f) :
    Function.Injective (mapSymbol (T := T) f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [hf.eq_iff]

/-- **Injective renamings are injective on productions.** If $f$ is an injective map from
nonterminals $N$ to nonterminals $N'$, then renaming the nonterminals of productions over $N$ by
$f$ is injective: two productions with the same renaming are equal.

In particular, renaming a finite set of productions by $f$ merges none of them. -/
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

/-- **Renaming nonterminals fixes terminal words.** Let $f$ map nonterminals $N$ to nonterminals
$N'$, and let $w$ be a word over the terminals. Reading $w$ as a sentential form over $N$ and
renaming its nonterminals by $f$ gives $w$ read as a sentential form over $N'$. -/
@[simp]
theorem map_mapSymbol_terminal {N' : Type*} (f : N → N') (w : List T) :
    w.map (mapSymbol f ∘ Symbol.terminal) = w.map Symbol.terminal :=
  List.map_congr_left fun _a _ => rfl

/-- **The empty language is context-free.** The empty language over any alphabet is
context-free: take a grammar with no productions. -/
theorem IsContextFree.zero : (0 : Language T).IsContextFree :=
  ⟨⟨Unit, (), ∅⟩, ContextFreeGrammar.language_eq_zero_of_forall_input_ne_initial (by simp)⟩

/-- **The language of the empty word is context-free.** For every alphabet $T$, the language
over $T$ whose only word is the empty word is context-free: a grammar with one nonterminal and
a single production erasing it generates this language. -/
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

/-- **Singleton languages are context-free.** For every word $w$ over an alphabet $T$, the
language $\{w\}$ consisting of $w$ alone is context-free: one production spells the word out. -/
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
