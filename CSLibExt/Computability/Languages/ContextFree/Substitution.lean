/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Context-free languages under substitution
-/
module

public import CSLibExt.Computability.Languages.ContextFree.ChomskyNormalForm
public import CSLibExt.Computability.Languages.ContextFree.Encoded
public import CSLibExt.Computability.Languages.Substitution
public import Mathlib.Data.Finset.Union

/-!
# Context-free languages under substitution

A substitution replaces each letter `a` of a word by any word of a language `s a`. When `L` and
every `s a` are context-free, so is the result (Hopcroft and Ullman, *Introduction to Automata
Theory, Languages, and Computation*, 1979, Theorem 6.2): keep the productions of a grammar for
`L` with each terminal `a` replaced by the start symbol of a grammar for `s a`, and add the
productions of those grammars on disjoint nonterminals.

Only the finitely many letters occurring in the productions need a grammar, so the source
alphabet may be infinite. Grammars for the letters are taken with natural-number nonterminals
(`EncodedCFG.isContextFree_iff`), and the letters are numbered by their positions in
`grammarTerminals g` (`Substitution.code`), so the new nonterminals are `g.NT ⊕ (ℕ × ℕ)`.

## Main results

Substitution itself (`Cslib.Language.substitution`) is defined in `Languages/Substitution.lean`.

* `Cslib.Language.IsContextFree.substitution`: context-free languages are closed under
  substitution by context-free languages.
-/

@[expose] public section

namespace Cslib.Language

attribute [local instance] Classical.propDecidable

variable {T T' : Type*}

namespace Substitution

noncomputable section

variable (g : ContextFreeGrammar T) (e : T → EncodedCFG T')

/-- A numbering of the letters of `g`: the position in `grammarTerminals g`. -/
def code (a : T) : ℕ :=
  (grammarTerminals g).idxOf a

/-- The letter with a given number. -/
def decode (k : ℕ) : Option T :=
  (grammarTerminals g)[k]?

theorem decode_code {a : T} (ha : a ∈ grammarTerminals g) : decode g (code g a) = some a :=
  List.getElem?_idxOf ha

/-- Replace a terminal `a` by the start symbol of the grammar for `s a`. -/
def substSymbol : Symbol T g.NT → Symbol T' (g.NT ⊕ (ℕ × ℕ))
  | .terminal a => .nonterminal (.inr (code g a, (e a).start))
  | .nonterminal B => .nonterminal (.inl B)

/-- A production of `g` with its terminals replaced. -/
def mainRule (r : ContextFreeRule T g.NT) : ContextFreeRule T' (g.NT ⊕ (ℕ × ℕ)) :=
  ⟨.inl r.input, r.output.map (substSymbol g e)⟩

/-- A production of the grammar for letter `a`, on the nonterminals tagged by its number. -/
def subRule (a : T) (r : ContextFreeRule T' ℕ) : ContextFreeRule T' (g.NT ⊕ (ℕ × ℕ)) :=
  mapRule (fun n => .inr (code g a, n)) r

/-- The productions of the substitution grammar. -/
def rules : Finset (ContextFreeRule T' (g.NT ⊕ (ℕ × ℕ))) :=
  g.rules.image (mainRule g e) ∪
    (grammarTerminals g).toFinset.biUnion fun a => (e a).toCFG.rules.image (subRule g a)

/-- The grammar of the substitution. -/
abbrev grammar : ContextFreeGrammar T' where
  NT := g.NT ⊕ (ℕ × ℕ)
  initial := .inl g.initial
  rules := rules g e

theorem mem_rules {r : ContextFreeRule T' (g.NT ⊕ (ℕ × ℕ))} :
    r ∈ rules g e ↔ (∃ r₀ ∈ g.rules, mainRule g e r₀ = r) ∨
      ∃ a ∈ grammarTerminals g, ∃ r₀ ∈ (e a).toCFG.rules, subRule g a r₀ = r := by
  simp only [rules, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, List.mem_toFinset]

theorem mainRule_mem {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    mainRule g e r ∈ (grammar g e).rules :=
  (mem_rules g e).2 (.inl ⟨r, hr, rfl⟩)

theorem subRule_mem {a : T} (ha : a ∈ grammarTerminals g) {r : ContextFreeRule T' ℕ}
    (hr : r ∈ (e a).toCFG.rules) : subRule g a r ∈ (grammar g e).rules :=
  (mem_rules g e).2 (.inr ⟨a, ha, r, hr, rfl⟩)

/-! ### Soundness -/

variable (s : T → Language T')

/-- The intended languages: the substitution image of what a nonterminal of `g` generates, and
what the grammar for a letter generates from a nonterminal. -/
def val : g.NT ⊕ (ℕ × ℕ) → Language T'
  | .inl B => substitution (languageFrom g B) s
  | .inr (k, n) =>
      match decode g k with
      | some a => languageFrom (e a).toCFG n
      | none => 0

theorem evalForm_map_substSymbol (he : ∀ a, (e a).language = s a) (u : List (Symbol T g.NT))
    (hu : ∀ a, Symbol.terminal a ∈ u → a ∈ grammarTerminals g) :
    evalForm (val g e s) (u.map (substSymbol g e)) =
      substitution (evalForm (languageFrom g) u) s := by
  induction u with
  | nil => rw [List.map_nil, evalForm_nil, evalForm_nil, substitution_one]
  | cons x u ih =>
      have ih' := ih fun a ha => hu a (List.mem_cons_of_mem _ ha)
      rw [List.map_cons, evalForm_cons, evalForm_cons, substitution_mul, ih']
      congr 1
      cases x with
      | terminal a =>
          have ha := hu a List.mem_cons_self
          change val g e s (.inr (code g a, (e a).start)) = _
          rw [evalSymbol_terminal, substitution_letter, val, decode_code g ha, ← he a]
          rfl
      | nonterminal B => rfl

theorem isValuation (he : ∀ a, (e a).language = s a) :
    IsValuation (grammar g e) (val g e s) := by
  intro r hr
  rcases (mem_rules g e).1 hr with ⟨r₀, hr₀, rfl⟩ | ⟨a, ha, r₀, hr₀, rfl⟩
  · change evalForm (val g e s) (r₀.output.map (substSymbol g e)) ≤
      substitution (languageFrom g r₀.input) s
    rw [evalForm_map_substSymbol g e s he _ fun a ha => mem_grammarTerminals hr₀ ha]
    exact substitution_mono (isValuation_languageFrom r₀ hr₀) s
  · rw [subRule, mapRule_output, mapRule_input, evalForm_map]
    have hV : (val g e s ∘ fun n => (.inr (code g a, n) : g.NT ⊕ (ℕ × ℕ))) =
        languageFrom (e a).toCFG := by
      funext n
      simp only [Function.comp_apply, val, decode_code g ha]
    rw [hV]
    have := isValuation_languageFrom r₀ hr₀
    simpa [val, decode_code g ha] using this

/-! ### Completeness -/

theorem mem_grammarTerminals_of_derives {u v : List (Symbol T g.NT)} (h : g.Derives u v)
    (hu : ∀ a, Symbol.terminal a ∈ u → a ∈ grammarTerminals g) :
    ∀ a, Symbol.terminal a ∈ v → a ∈ grammarTerminals g := by
  induction h with
  | refl => exact hu
  | tail _ hstep ih =>
      obtain ⟨r, hr, hrew⟩ := hstep
      obtain ⟨p, q, rfl, rfl⟩ := ContextFreeRule.rewrites_iff.1 hrew
      intro a ha
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · exact ih a (by simp [ha])
      · exact mem_grammarTerminals hr ha
      · exact ih a (by simp [ha])

theorem derives_substSymbol {u v : List (Symbol T g.NT)} (h : g.Derives u v) :
    (grammar g e).Derives (u.map (substSymbol g e)) (v.map (substSymbol g e)) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      obtain ⟨r, hr, hrew⟩ := hstep
      refine ih.trans_produces ⟨mainRule g e r, mainRule_mem g e hr, ?_⟩
      obtain ⟨p, q, rfl, rfl⟩ := ContextFreeRule.rewrites_iff.1 hrew
      exact ContextFreeRule.rewrites_iff.2 ⟨p.map (substSymbol g e), q.map (substSymbol g e),
        by rw [List.map_append, List.map_append]; rfl,
        by rw [List.map_append, List.map_append]; rfl⟩

theorem derives_letter (he : ∀ a, (e a).language = s a) {a : T} (ha : a ∈ grammarTerminals g)
    {y : List T'} (hy : y ∈ s a) :
    (grammar g e).Derives [Symbol.nonterminal (.inr (code g a, (e a).start))]
      (y.map Symbol.terminal) := by
  rw [← he a, EncodedCFG.language, ContextFreeGrammar.mem_language_iff] at hy
  have hsub : ∀ r ∈ (e a).toCFG.rules,
      mapRule (fun n => (.inr (code g a, n) : g.NT ⊕ (ℕ × ℕ))) r ∈ (grammar g e).rules :=
    fun r hr => subRule_mem g e ha hr
  have := derives_map_of_forall_mem (G := grammar g e) hsub hy
  simpa [List.map_map] using this

theorem derives_word (he : ∀ a, (e a).language = s a) (x : List T)
    (hx : ∀ a ∈ x, a ∈ grammarTerminals g) {y : List T'} (hy : y ∈ (x.map s).prod) :
    (grammar g e).Derives ((x.map Symbol.terminal).map (substSymbol g e))
      (y.map Symbol.terminal) := by
  induction x generalizing y with
  | nil =>
      rw [List.map_nil, List.prod_nil, Language.mem_one] at hy
      subst hy
      rfl
  | cons a x ih =>
      rw [List.map_cons, List.prod_cons] at hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Language.mem_mul.1 hy
      have h₁ := derives_letter g e s he (hx a List.mem_cons_self) hy₁
      have h₂ := ih (fun b hb => hx b (List.mem_cons_of_mem _ hb)) hy₂
      simpa [substSymbol, List.map_append] using derives_append h₁ h₂

theorem language_grammar (he : ∀ a, (e a).language = s a) :
    (grammar g e).language = substitution g.language s := by
  apply le_antisymm
  · exact language_le_of_valuation (isValuation g e s he)
  · rintro y ⟨x, hx, hy⟩
    rw [ContextFreeGrammar.mem_language_iff] at hx
    have hletters := mem_grammarTerminals_of_derives g hx (by simp)
    have h₁ := derives_substSymbol g e hx
    exact (ContextFreeGrammar.mem_language_iff _ _).2
      (h₁.trans (derives_word g e s he x (fun a ha => hletters a (by simpa using ha)) hy))

end

end Substitution

/-- **Context-free languages are closed under substitution by context-free languages.** -/
theorem IsContextFree.substitution {L : Language T} (hL : L.IsContextFree)
    {s : T → Language T'} (hs : ∀ a, (s a).IsContextFree) :
    (Cslib.Language.substitution L s).IsContextFree := by
  obtain ⟨g, rfl⟩ := hL
  choose e he using fun a => EncodedCFG.isContextFree_iff.1 (hs a)
  exact ⟨Substitution.grammar g e, Substitution.language_grammar g e s he⟩

end Cslib.Language
