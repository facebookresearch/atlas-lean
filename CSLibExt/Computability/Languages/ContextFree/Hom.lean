/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Basic

/-!
# Context-free languages under word-valued homomorphisms

Expanding every terminal `a` of a grammar to a fixed word `φ a` maps its
language by the induced word homomorphism `w ↦ (w.map φ).flatten`. As for
letter maps, soundness is a valuation (the homomorphic image of the canonical
assignment) and completeness lifts derivations through the expansion.

## Main results

* `Cslib.Language.IsContextFree.homImage`: homomorphic images of
  context-free languages are context-free.
-/

@[expose] public section

namespace Cslib.Language

attribute [local instance] Classical.propDecidable

variable {T T' : Type*} {N : Type*} {g : ContextFreeGrammar T}

/-- The homomorphic image of a language under a word-valued homomorphism. -/
private def homImageLang (φ : T → List T') (L : Language T) : Language T' :=
  { y : List T' | ∃ x ∈ L, (x.map φ).flatten = y }

/-- Expand a grammar symbol under a word-valued homomorphism. -/
private def expandSymbol (φ : T → List T') : Symbol T N → List (Symbol T' N)
  | .terminal a => (φ a).map Symbol.terminal
  | .nonterminal A => [Symbol.nonterminal A]

/-- Expand every symbol of a sentential form. -/
private def expandForm (φ : T → List T') (u : List (Symbol T N)) :
    List (Symbol T' N) :=
  u.flatMap (expandSymbol φ)

/-- Expand the terminals of a production into their homomorphic words. -/
private def expandRule (φ : T → List T') (r : ContextFreeRule T N) :
    ContextFreeRule T' N :=
  ⟨r.input, expandForm φ r.output⟩

/-- The grammar obtained by expanding every terminal of `g` by `φ`. -/
private noncomputable abbrev homGrammar (φ : T → List T') (g : ContextFreeGrammar T) :
    ContextFreeGrammar T' where
  NT := g.NT
  initial := g.initial
  rules := g.rules.image (expandRule φ)

private theorem evalForm_expandForm (φ : T → List T') (u : List (Symbol T g.NT)) :
    evalForm (fun A => homImageLang φ (languageFrom g A))
        (expandForm φ u) =
      homImageLang φ (evalForm (languageFrom g) u) := by
  induction u with
  | nil =>
    ext y
    constructor
    · intro hy
      have hy0 : y = [] := hy
      subst hy0
      exact ⟨[], rfl, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hx0 : x = [] := hx
      subst hx0
      rfl
  | cons s u ih =>
    cases s with
    | terminal a =>
      rw [show expandForm φ (Symbol.terminal (N := g.NT) a :: u) =
          (φ a).map Symbol.terminal ++ expandForm φ u from rfl, evalForm_append,
        evalForm_map_terminal, ih]
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, z, hz, hxy⟩ := Language.mem_mul.mp hy
        obtain ⟨z₀, hz₀, hzfl⟩ : ∃ z₀ ∈ evalForm (languageFrom g) u,
            (z₀.map φ).flatten = z := hz
        have hx' : x = φ a := hx
        refine ⟨a :: z₀, Language.mem_mul.mpr ⟨[a], rfl, z₀, hz₀, rfl⟩, ?_⟩
        simp only [List.map_cons, List.flatten_cons, ← hxy, hx', hzfl]
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨x₁, hx₁, x₂, hx₂, hxapp⟩ := Language.mem_mul.mp hx
        have hx₁' : x₁ = [a] := hx₁
        subst hx₁'
        exact Language.mem_mul.mpr
          ⟨φ a, rfl, (x₂.map φ).flatten, ⟨x₂, hx₂, rfl⟩, by rw [← hxapp]; simp⟩
    | nonterminal A =>
      rw [show expandForm φ (Symbol.nonterminal (T := T) A :: u) =
          Symbol.nonterminal (T := T') A :: expandForm φ u from rfl]
      simp only [evalForm_cons, evalSymbol_nonterminal, ih]
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, z, hz, hxy⟩ := Language.mem_mul.mp hy
        obtain ⟨x₀, hx₀, hxfl⟩ : ∃ x₀ ∈ languageFrom g A, (x₀.map φ).flatten = x := hx
        obtain ⟨z₀, hz₀, hzfl⟩ : ∃ z₀ ∈ evalForm (languageFrom g) u,
            (z₀.map φ).flatten = z := hz
        exact ⟨x₀ ++ z₀, Language.mem_mul.mpr ⟨x₀, hx₀, z₀, hz₀, rfl⟩, by
          simp [hxfl, hzfl, hxy]⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨x₁, hx₁, x₂, hx₂, hxapp⟩ := Language.mem_mul.mp hx
        exact Language.mem_mul.mpr
          ⟨(x₁.map φ).flatten, ⟨x₁, hx₁, rfl⟩, (x₂.map φ).flatten, ⟨x₂, hx₂, rfl⟩, by
            rw [← hxapp]; simp⟩

private theorem isValuation_homGrammar (φ : T → List T') :
    IsValuation (homGrammar φ g)
      (fun A => homImageLang φ (languageFrom g A)) := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.mp hr
  change evalForm _ (expandForm φ r₀.output) ≤ _
  rw [evalForm_expandForm (g := g) φ r₀.output]
  intro y hy
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ evalForm (languageFrom g) r₀.output, (x.map φ).flatten = y :=
    hy
  exact ⟨x, isValuation_languageFrom r₀ hr₀ hx, rfl⟩

private theorem rewrites_expand {φ : T → List T'} {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (h : r.Rewrites u v) :
    (expandRule φ r).Rewrites (expandForm φ u) (expandForm φ v) := by
  rw [ContextFreeRule.rewrites_iff] at h ⊢
  obtain ⟨p, q, rfl, rfl⟩ := h
  refine ⟨expandForm φ p, expandForm φ q, ?_, ?_⟩ <;> simp [expandForm, expandRule, expandSymbol]

private theorem derives_expand {φ : T → List T'} {u v : List (Symbol T g.NT)}
    (h : g.Derives u v) :
    (homGrammar φ g).Derives (expandForm φ u) (expandForm φ v) := by
  induction h with
  | refl => rfl
  | tail _ last ih =>
    obtain ⟨r, hr, hrew⟩ := last
    exact ih.trans_produces
      ⟨expandRule φ r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, rewrites_expand hrew⟩

private theorem expandForm_map_terminal (φ : T → List T') (w : List T) :
    expandForm (N := g.NT) φ (w.map Symbol.terminal) =
      ((w.map φ).flatten).map Symbol.terminal := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    calc expandForm (N := g.NT) φ ((a :: w).map Symbol.terminal)
        = (φ a).map Symbol.terminal ++ expandForm (N := g.NT) φ (w.map Symbol.terminal) :=
          rfl
      _ = ((φ a ++ (w.map φ).flatten).map Symbol.terminal) := by
          rw [ih, List.map_append]
      _ = (((a :: w).map φ).flatten).map Symbol.terminal := by
          simp

private theorem homGrammar_language (φ : T → List T') :
    (homGrammar φ g).language =
      homImageLang φ g.language := by
  apply le_antisymm
  · have hle := language_le_of_valuation (g := homGrammar φ g) (isValuation_homGrammar φ)
    simpa [languageFrom_initial] using hle
  · intro y hy
    obtain ⟨w, hw, rfl⟩ : ∃ w ∈ g.language, (w.map φ).flatten = y := hy
    apply (ContextFreeGrammar.mem_language_iff _ _).mpr
    have hlift := derives_expand (φ := φ) ((ContextFreeGrammar.mem_language_iff g w).mp hw)
    rw [expandForm_map_terminal] at hlift
    exact hlift

/-- **Context-free languages are closed under homomorphic images.** Let $T$ and $T'$ be alphabets,
$L$ a context-free language over $T$, and $\varphi$ a map sending each letter of $T$ to a word
over $T'$. Then the language of all words $\varphi(a_1) \cdots \varphi(a_n)$ with
$a_1 \cdots a_n \in L$ is context-free.

A grammar for it replaces every terminal $a$ in every production by the word $\varphi(a)$. -/
theorem IsContextFree.homImage {L : Language T} (hL : L.IsContextFree)
    (φ : T → List T') :
    Language.IsContextFree ((fun w => (w.map φ).flatten) '' L) := by
  obtain ⟨g, rfl⟩ := hL
  refine ⟨homGrammar φ g, ?_⟩
  rw [homGrammar_language]
  rfl

end Cslib.Language
