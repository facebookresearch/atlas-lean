/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Closure

/-!
# Context-free languages under letter maps

Renaming every terminal of a grammar by a function on alphabets maps its
language by `Language.map`. Soundness is again a valuation: a nonterminal is
assigned the mapped version of its canonical language in the original
grammar. Completeness lifts derivations symbol by symbol.

This is closure under a *letter* homomorphism. The stronger word-valued
homomorphism and inverse homomorphism closures are separate follow-ups.

## Main results

* `Cslib.Language.IsContextFree.map`: the image of a context-free language
  under a letter map is context-free.
-/

@[expose] public section

namespace Cslib.Language

attribute [local instance] Classical.propDecidable

variable {T T' : Type*} {N : Type*} {g : ContextFreeGrammar T}

/-- Rename the terminals in a grammar symbol. -/
private def mapTerminalSymbol (f : T → T') : Symbol T N → Symbol T' N
  | .terminal a => .terminal (f a)
  | .nonterminal A => .nonterminal A

/-- Rename the terminals in a production. -/
private def mapTerminalRule (f : T → T') (r : ContextFreeRule T N) :
    ContextFreeRule T' N :=
  ⟨r.input, r.output.map (mapTerminalSymbol f)⟩

/-- The grammar obtained by renaming every terminal of `g` by `f`. -/
private noncomputable abbrev mapGrammar (f : T → T') (g : ContextFreeGrammar T) :
    ContextFreeGrammar T' where
  NT := g.NT
  initial := g.initial
  rules := g.rules.image (mapTerminalRule f)

private theorem evalForm_mapTerminal (f : T → T') (u : List (Symbol T g.NT)) :
    evalForm (fun A => Language.map f (languageFrom g A)) (u.map (mapTerminalSymbol f)) =
      Language.map f (evalForm (languageFrom g) u) := by
  induction u with
  | nil => simp
  | cons s u ih =>
    cases s with
    | terminal a =>
      have hsingle : Language.map f ({[a]} : Language T) = {[f a]} := by
        rw [show Language.map f ({[a]} : Language T) =
            (List.map f) '' ({[a]} : Set (List T)) from rfl, Set.image_singleton]
        rfl
      simp only [List.map_cons, evalForm_cons, ih, mapTerminalSymbol,
        evalSymbol, map_mul, hsingle]
    | nonterminal A =>
      simp only [List.map_cons, evalForm_cons, ih, mapTerminalSymbol, evalSymbol, map_mul]

private theorem isValuation_mapGrammar (f : T → T') :
    IsValuation (mapGrammar f g) (fun A => Language.map f (languageFrom g A)) := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.mp hr
  change evalForm _ (r₀.output.map (mapTerminalSymbol f)) ≤ _
  rw [evalForm_mapTerminal (g := g) f r₀.output]
  intro y hy
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ evalForm (languageFrom g) r₀.output, x.map f = y := hy
  exact ⟨x, isValuation_languageFrom r₀ hr₀ hx, rfl⟩

private theorem rewrites_mapTerminal {f : T → T'} {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (h : r.Rewrites u v) :
    (mapTerminalRule f r).Rewrites (u.map (mapTerminalSymbol f))
      (v.map (mapTerminalSymbol f)) := by
  induction h with
  | head s =>
    simpa [mapTerminalRule, mapTerminalSymbol] using
      ContextFreeRule.Rewrites.head (r := mapTerminalRule f r) (s.map (mapTerminalSymbol f))
  | cons x _ ih => exact ContextFreeRule.Rewrites.cons _ ih

private theorem derives_mapTerminal {f : T → T'} {u v : List (Symbol T g.NT)}
    (h : g.Derives u v) :
    (mapGrammar f g).Derives (u.map (mapTerminalSymbol f))
      (v.map (mapTerminalSymbol f)) := by
  induction h with
  | refl => rfl
  | tail _ last ih =>
    obtain ⟨r, hr, hrew⟩ := last
    exact ih.trans_produces
      ⟨mapTerminalRule f r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, rewrites_mapTerminal hrew⟩

private theorem mapGrammar_language (f : T → T') :
    (mapGrammar f g).language = Language.map f g.language := by
  apply le_antisymm
  · have hle := language_le_of_valuation (g := mapGrammar f g) (isValuation_mapGrammar f)
    simpa [languageFrom_initial] using hle
  · intro y hy
    obtain ⟨w, hw, hwf⟩ : ∃ w ∈ g.language, w.map f = y := hy
    apply (ContextFreeGrammar.mem_language_iff _ _).mpr
    have hlift := derives_mapTerminal (f := f) ((ContextFreeGrammar.mem_language_iff g w).mp hw)
    have htarget : (w.map (Symbol.terminal (N := g.NT))).map (mapTerminalSymbol (N := g.NT) f) =
        (w.map f).map (Symbol.terminal (N := g.NT)) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun a _ => rfl
    rw [htarget] at hlift
    rw [← hwf]
    exact hlift

/-- **Context-free languages are closed under letter maps.** Let $L$ be a context-free language
over an alphabet $T$ and let $f \colon T \to T'$ be a map of alphabets. Then the image of $L$
under $f$, the language $\{f(a_1) \cdots f(a_n) \mid a_1 \cdots a_n \in L\}$ over $T'$, is
context-free. -/
theorem IsContextFree.map {L : Language T} (hL : L.IsContextFree) (f : T → T') :
    (Language.map f L).IsContextFree := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨mapGrammar f g, mapGrammar_language f⟩

end Cslib.Language
