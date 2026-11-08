/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Basic
public import Mathlib.Data.Set.Finite.List

/-!
# Closure properties of context-free languages

The usual grammar constructions for union, concatenation, and Kleene star,
packaged through the valuation API of `ContextFree/Basic.lean`: the combined
grammar is sound because the intended combined language, together with the
canonical `languageFrom` assignment on each component, is a valuation of it;
it is complete because component derivations lift along the nonterminal
injections.

## Main results

* `Cslib.Language.IsContextFree.add`: context-free languages are closed
  under union.
* `Cslib.Language.IsContextFree.mul`: closure under concatenation.
* `Cslib.Language.IsContextFree.kstar`: closure under Kleene star.
* `Cslib.Language.IsContextFree.pow` and `IsContextFree.of_finite`: powers
  and finite languages are context-free.
-/

@[expose] public section

namespace Cslib.Language

open scoped Computability

attribute [local instance] Classical.propDecidable

variable {T : Type*} {g h : ContextFreeGrammar T}

/-- Nonterminals of a two-grammar combination: a fresh start symbol plus the
tagged nonterminals of each component. -/
private inductive BinNT (A B : Type*)
  | start : BinNT A B
  | left : A → BinNT A B
  | right : B → BinNT A B

/-- The valuation of a two-grammar combination whose fresh start symbol is
meant to generate `L`: component nonterminals get their canonical languages
in their own grammar. -/
private def binValuation (g h : ContextFreeGrammar T) (L : Language T) :
    BinNT g.NT h.NT → Language T
  | .start => L
  | .left A => languageFrom g A
  | .right B => languageFrom h B

private theorem binValuation_start (L : Language T) :
    binValuation g h L .start = L :=
  rfl

private theorem binValuation_left (L : Language T) (A : g.NT) :
    binValuation g h L (.left A) = languageFrom g A :=
  rfl

private theorem binValuation_right (L : Language T) (B : h.NT) :
    binValuation g h L (.right B) = languageFrom h B :=
  rfl

private theorem evalForm_binValuation_left (L : Language T) (u : List (Symbol T g.NT)) :
    evalForm (binValuation g h L) (u.map (mapSymbol BinNT.left)) =
      evalForm (languageFrom g) u := by
  rw [evalForm_map]
  rfl

private theorem evalForm_binValuation_right (L : Language T) (u : List (Symbol T h.NT)) :
    evalForm (binValuation g h L) (u.map (mapSymbol BinNT.right)) =
      evalForm (languageFrom h) u := by
  rw [evalForm_map]
  rfl

/-- Combined component rules are sound for the binary valuation, whatever
language its start symbol is assigned. -/
private theorem isValuation_binValuation_component
    {G : ContextFreeGrammar T} {f : g.NT → G.NT} {V : G.NT → Language T}
    (hV : V ∘ f = languageFrom g) {r : ContextFreeRule T G.NT}
    (hr : ∃ r₀ ∈ g.rules, mapRule f r₀ = r) :
    evalForm V r.output ≤ V r.input := by
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  simp only [mapRule_output, mapRule_input]
  rw [evalForm_map, hV]
  change evalForm (languageFrom g) r₀.output ≤ (V ∘ f) r₀.input
  rw [hV]
  exact isValuation_languageFrom r₀ hr₀

/-- Grammar for the union of two languages: a fresh start symbol chooses a
component start symbol, then that component's rules take over. -/
private noncomputable abbrev unionGrammar (g h : ContextFreeGrammar T) :
    ContextFreeGrammar T where
  NT := BinNT g.NT h.NT
  initial := .start
  rules :=
    {⟨.start, [Symbol.nonterminal (BinNT.left g.initial)]⟩,
      ⟨.start, [Symbol.nonterminal (BinNT.right h.initial)]⟩}
      ∪ g.rules.map ⟨mapRule BinNT.left,
          mapRule_injective (fun {_ _} h => BinNT.left.inj h)⟩
      ∪ h.rules.map ⟨mapRule BinNT.right,
          mapRule_injective (fun {_ _} h => BinNT.right.inj h)⟩

private theorem isValuation_unionGrammar :
    IsValuation (unionGrammar g h)
      (binValuation g h (g.language + h.language)) := by
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  swap
  · exact isValuation_binValuation_component (g := h) (G := unionGrammar g h)
      (f := BinNT.right) (V := binValuation g h (g.language + h.language))
      (funext fun _ => rfl) (Finset.mem_map.mp hr)
  rcases Finset.mem_union.mp hr with hr | hr
  swap
  · exact isValuation_binValuation_component (g := g) (G := unionGrammar g h)
      (f := BinNT.left) (V := binValuation g h (g.language + h.language))
      (funext fun _ => rfl) (Finset.mem_map.mp hr)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · simp only [evalForm_cons, evalForm_nil, evalSymbol_nonterminal, binValuation_left,
      binValuation_start, mul_one, languageFrom_initial]
    intro w hw
    exact (Language.mem_add _ _ _).mpr (Or.inl hw)
  · simp only [evalForm_cons, evalForm_nil, evalSymbol_nonterminal, binValuation_right,
      binValuation_start, mul_one, languageFrom_initial]
    intro w hw
    exact (Language.mem_add _ _ _).mpr (Or.inr hw)

private theorem derives_union_left {w : List T}
    (hw : g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal)) :
    (unionGrammar g h).Derives [Symbol.nonterminal .start] (w.map Symbol.terminal) := by
  have hstep : (unionGrammar g h).Produces [Symbol.nonterminal .start]
      [Symbol.nonterminal (BinNT.left g.initial)] :=
    ⟨⟨.start, [Symbol.nonterminal (BinNT.left g.initial)]⟩,
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _)),
      ContextFreeRule.Rewrites.input_output⟩
  have hlift := derives_map_of_forall_mem (G := unionGrammar g h) (f := BinNT.left)
    (fun r hr =>
      Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨r, hr, rfl⟩))) hw
  simp only [List.map_map, map_mapSymbol_terminal] at hlift
  exact hstep.trans_derives hlift

private theorem derives_union_right {w : List T}
    (hw : h.Derives [Symbol.nonterminal h.initial] (w.map Symbol.terminal)) :
    (unionGrammar g h).Derives [Symbol.nonterminal .start] (w.map Symbol.terminal) := by
  have hstep : (unionGrammar g h).Produces [Symbol.nonterminal .start]
      [Symbol.nonterminal (BinNT.right h.initial)] :=
    ⟨⟨.start, [Symbol.nonterminal (BinNT.right h.initial)]⟩,
      Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))),
      ContextFreeRule.Rewrites.input_output⟩
  have hlift := derives_map_of_forall_mem (G := unionGrammar g h) (f := BinNT.right)
    (fun r hr =>
      Finset.mem_union_right _ (Finset.mem_map.mpr ⟨r, hr, rfl⟩)) hw
  simp only [List.map_map, map_mapSymbol_terminal] at hlift
  exact hstep.trans_derives hlift

private theorem unionGrammar_language :
    (unionGrammar g h).language = g.language + h.language := by
  apply le_antisymm
  · have hle := language_le_of_valuation (g := unionGrammar g h) isValuation_unionGrammar
    simpa [binValuation_start] using hle
  · intro w hw
    apply (ContextFreeGrammar.mem_language_iff _ _).mpr
    rcases (Language.mem_add _ _ _).mp hw with hw | hw
    · exact derives_union_left ((ContextFreeGrammar.mem_language_iff g w).mp hw)
    · exact derives_union_right ((ContextFreeGrammar.mem_language_iff h w).mp hw)

/-- Context-free languages are closed under union. -/
theorem IsContextFree.add {L M : Language T} (hL : L.IsContextFree) (hM : M.IsContextFree) :
    (L + M).IsContextFree := by
  obtain ⟨g, rfl⟩ := hL
  obtain ⟨h, rfl⟩ := hM
  exact ⟨unionGrammar g h, unionGrammar_language⟩

/-- Grammar for the concatenation of two languages: a fresh start symbol
produces the two component start symbols in order. -/
private noncomputable abbrev mulGrammar (g h : ContextFreeGrammar T) :
    ContextFreeGrammar T where
  NT := BinNT g.NT h.NT
  initial := .start
  rules :=
    {⟨.start, [Symbol.nonterminal (BinNT.left g.initial),
        Symbol.nonterminal (BinNT.right h.initial)]⟩}
      ∪ g.rules.map ⟨mapRule BinNT.left,
          mapRule_injective (fun {_ _} h => BinNT.left.inj h)⟩
      ∪ h.rules.map ⟨mapRule BinNT.right,
          mapRule_injective (fun {_ _} h => BinNT.right.inj h)⟩

private theorem isValuation_mulGrammar :
    IsValuation (mulGrammar g h)
      (binValuation g h (g.language * h.language)) := by
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  swap
  · exact isValuation_binValuation_component (g := h) (G := mulGrammar g h)
      (f := BinNT.right) (V := binValuation g h (g.language * h.language))
      (funext fun _ => rfl) (Finset.mem_map.mp hr)
  rcases Finset.mem_union.mp hr with hr | hr
  swap
  · exact isValuation_binValuation_component (g := g) (G := mulGrammar g h)
      (f := BinNT.left) (V := binValuation g h (g.language * h.language))
      (funext fun _ => rfl) (Finset.mem_map.mp hr)
  simp only [Finset.mem_singleton] at hr
  subst hr
  simp [binValuation_left, binValuation_right, binValuation_start, languageFrom_initial]

private theorem mulGrammar_language :
    (mulGrammar g h).language = g.language * h.language := by
  apply le_antisymm
  · have hle := language_le_of_valuation (g := mulGrammar g h) isValuation_mulGrammar
    simpa [binValuation_start] using hle
  · intro w hw
    obtain ⟨a, ha, b, hb, hab⟩ := Language.mem_mul.mp hw
    apply (ContextFreeGrammar.mem_language_iff _ _).mpr
    have hstep : (mulGrammar g h).Produces [Symbol.nonterminal .start]
        [Symbol.nonterminal (BinNT.left g.initial),
          Symbol.nonterminal (BinNT.right h.initial)] :=
      ⟨⟨.start, [Symbol.nonterminal (BinNT.left g.initial),
          Symbol.nonterminal (BinNT.right h.initial)]⟩,
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _)),
        ContextFreeRule.Rewrites.input_output⟩
    have hliftL := derives_map_of_forall_mem (G := mulGrammar g h) (f := BinNT.left)
      (fun r hr =>
        Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_map.mpr ⟨r, hr, rfl⟩)))
      ((ContextFreeGrammar.mem_language_iff g a).mp ha)
    have hliftR := derives_map_of_forall_mem (G := mulGrammar g h) (f := BinNT.right)
      (fun r hr =>
        Finset.mem_union_right _ (Finset.mem_map.mpr ⟨r, hr, rfl⟩))
      ((ContextFreeGrammar.mem_language_iff h b).mp hb)
    simp only [List.map_map, map_mapSymbol_terminal] at hliftL hliftR
    subst hab
    rw [List.map_append]
    exact hstep.trans_derives (derives_append hliftL hliftR)

/-- Context-free languages are closed under concatenation. -/
theorem IsContextFree.mul {L M : Language T} (hL : L.IsContextFree) (hM : M.IsContextFree) :
    (L * M).IsContextFree := by
  obtain ⟨g, rfl⟩ := hL
  obtain ⟨h, rfl⟩ := hM
  exact ⟨mulGrammar g h, mulGrammar_language⟩

/-- Nonterminals of a one-grammar combination with a fresh start symbol. -/
private inductive StarNT (A : Type*)
  | start : StarNT A
  | of : A → StarNT A

/-- The valuation of a one-grammar combination whose fresh start symbol is
meant to generate `L`. -/
private def starValuation (g : ContextFreeGrammar T) (L : Language T) :
    StarNT g.NT → Language T
  | .start => L
  | .of A => languageFrom g A

private theorem starValuation_start (L : Language T) :
    starValuation g L .start = L :=
  rfl

private theorem starValuation_of (L : Language T) (A : g.NT) :
    starValuation g L (.of A) = languageFrom g A :=
  rfl

/-- Grammar for the Kleene star of a language: the fresh start symbol either
erases, or produces one component word followed by itself. -/
private noncomputable abbrev starGrammar (g : ContextFreeGrammar T) :
    ContextFreeGrammar T where
  NT := StarNT g.NT
  initial := .start
  rules :=
    {⟨.start, []⟩,
      ⟨.start, [Symbol.nonterminal (StarNT.of g.initial), Symbol.nonterminal .start]⟩}
      ∪ g.rules.map ⟨mapRule StarNT.of,
          mapRule_injective (fun {_ _} h => StarNT.of.inj h)⟩

private theorem isValuation_starGrammar :
    IsValuation (starGrammar g) (starValuation g g.language∗) := by
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  swap
  · exact isValuation_binValuation_component (g := g) (G := starGrammar g)
      (f := StarNT.of) (V := starValuation g g.language∗)
      (funext fun _ => rfl) (Finset.mem_map.mp hr)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl
  · simp only [evalForm_nil, starValuation_start]
    exact one_le_kstar (a := g.language)
  · simp only [evalForm_cons, evalForm_nil, evalSymbol_nonterminal, starValuation_of,
      starValuation_start, mul_one, languageFrom_initial]
    exact mul_kstar_le_kstar (a := g.language)

private theorem derives_starGrammar_flatten {Ws : List (List T)}
    (hWs : ∀ w ∈ Ws, w ∈ g.language) :
    (starGrammar g).Derives [Symbol.nonterminal .start]
      (Ws.flatten.map Symbol.terminal) := by
  induction Ws with
  | nil =>
    exact ContextFreeGrammar.Produces.single
      ⟨⟨.start, []⟩,
        Finset.mem_union_left _ (Finset.mem_insert_self _ _),
        ContextFreeRule.Rewrites.input_output⟩
  | cons w Ws ih =>
    have hw : w ∈ g.language := hWs w (by simp)
    have hWs' : ∀ x ∈ Ws, x ∈ g.language := fun x hx => hWs x (by simp [hx])
    have hstep : (starGrammar g).Produces [Symbol.nonterminal .start]
        [Symbol.nonterminal (StarNT.of g.initial), Symbol.nonterminal .start] :=
      ⟨⟨.start, [Symbol.nonterminal (StarNT.of g.initial), Symbol.nonterminal .start]⟩,
        Finset.mem_union_left _
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
        ContextFreeRule.Rewrites.input_output⟩
    have hlift := derives_map_of_forall_mem (G := starGrammar g) (f := StarNT.of)
      (fun r hr => Finset.mem_union_right _ (Finset.mem_map.mpr ⟨r, hr, rfl⟩))
      ((ContextFreeGrammar.mem_language_iff g w).mp hw)
    simp only [List.map_map, map_mapSymbol_terminal] at hlift
    have htail := ih hWs'
    simp only [List.flatten_cons, List.map_append]
    exact hstep.trans_derives (derives_append hlift htail)

private theorem starGrammar_language :
    (starGrammar g).language = g.language∗ := by
  apply le_antisymm
  · have hle := language_le_of_valuation (g := starGrammar g) isValuation_starGrammar
    simpa [starValuation_start] using hle
  · intro w hw
    obtain ⟨Ws, hwflatten, hWs⟩ := Language.mem_kstar.mp hw
    apply (ContextFreeGrammar.mem_language_iff _ _).mpr
    subst hwflatten
    exact derives_starGrammar_flatten hWs

/-- Context-free languages are closed under Kleene star. -/
theorem IsContextFree.kstar {L : Language T} (hL : L.IsContextFree) :
    (L∗).IsContextFree := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨starGrammar g, starGrammar_language⟩

/-- Powers of a context-free language are context-free. -/
theorem IsContextFree.pow {L : Language T} (hL : L.IsContextFree) :
    ∀ n : ℕ, (L ^ n).IsContextFree
  | 0 => by simpa using IsContextFree.one (T := T)
  | n + 1 => by
    rw [pow_succ]
    exact IsContextFree.mul (IsContextFree.pow hL n) hL

/-- Every finite language is context-free. -/
theorem IsContextFree.of_finite {L : Language T} (h : Set.Finite L) : L.IsContextFree := by
  refine Set.Finite.induction_on _ h ?_ ?_
  · change (0 : Language T).IsContextFree
    exact IsContextFree.zero
  · intro a s _ _ ih
    rw [Set.insert_eq]
    exact IsContextFree.add (IsContextFree.singleton_word a) ih

/-- Over a finite alphabet, a language whose words all have length at most
`n` is context-free. -/
theorem IsContextFree.of_length_le [Finite T] {L : Language T} (n : ℕ)
    (h : ∀ w ∈ L, w.length ≤ n) : L.IsContextFree := by
  apply IsContextFree.of_finite
  refine (List.finite_length_le T n).subset ?_
  intro w hw
  exact h w hw

end Cslib.Language
