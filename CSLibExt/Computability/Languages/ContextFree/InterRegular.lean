/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Regular
public import CSLibExt.Computability.Languages.ContextFree.Yields

/-!
# Intersection of a context-free language with a regular language

State annotation without a normal-form conversion. Given a DFA `M`, the
annotated grammar has nonterminals `(p, A, q)`, generating exactly the words
that `A` yields while taking `M` from `p` to `q`, together with chain
nonterminals `(p, i, q)` consuming the `i`-th production-output suffix.
Chain forms are encoded by their index in a fixed suffix list, which keeps
the nonterminal type small for alphabets in any universe. A fresh start
symbol picks an accepting end state.

Soundness is the valuation that reads these meanings off; completeness is
induction on `Yields` derivations. No finite-alphabet assumption is needed:
chain rules are only created for the finitely many production suffixes.

## Main results

* `Cslib.Language.IsContextFree.inf_dfa_accepts`: intersecting a CFL with
  a DFA's language stays context-free.
* `Cslib.Language.IsContextFree.inf_isRegular`: intersecting a CFL with a
  regular language stays context-free.
-/

@[expose] public section

namespace Cslib.Language

attribute [local instance] Classical.propDecidable

variable {T : Type*} {σ : Type} {g : ContextFreeGrammar T} {M : DFA T σ}

/-- Nonterminals of the DFA-annotated grammar: a fresh start symbol,
state-annotated original nonterminals, and chain nonterminals consuming an
indexed production-output suffix from a start state to an end state. -/
private inductive AnnotNT (σ : Type) (N : Type)
  | start : AnnotNT σ N
  | main : σ → N → σ → AnnotNT σ N
  | chain : σ → ℕ → σ → AnnotNT σ N

/-- A fixed list of all suffixes of production outputs. -/
private noncomputable def suffixList (g : ContextFreeGrammar T) : List (List (Symbol T g.NT)) :=
  g.rules.toList.flatMap fun r => r.output.tails

private theorem mem_suffixList {u : List (Symbol T g.NT)} :
    u ∈ suffixList g ↔ ∃ r ∈ g.rules, u ∈ r.output.tails := by
  simp [suffixList]

/-- The sentential form encoded by a chain index; out-of-range indices
decode to the empty form. -/
private noncomputable def decodeForm (g : ContextFreeGrammar T) (i : ℕ) : List (Symbol T g.NT) :=
  (suffixList g)[i]?.getD []

/-- The index encoding a given form. -/
private noncomputable def indexOfForm (g : ContextFreeGrammar T) (u : List (Symbol T g.NT)) : ℕ :=
  (suffixList g).idxOf u

private theorem decodeForm_indexOfForm {u : List (Symbol T g.NT)}
    (hu : u ∈ suffixList g) : decodeForm g (indexOfForm g u) = u := by
  unfold decodeForm indexOfForm
  rw [List.getElem?_idxOf hu]
  rfl

private theorem mem_suffixList_of_decodeForm {i : ℕ} (hi : i < (suffixList g).length) :
    decodeForm g i ∈ suffixList g := by
  unfold decodeForm
  rw [List.getElem?_eq_getElem hi]
  exact List.getElem_mem _

private theorem output_mem_suffixList {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    r.output ∈ suffixList g :=
  mem_suffixList.mpr ⟨r, hr, (List.mem_tails _ _).mpr (List.suffix_refl _)⟩

private theorem tail_mem_suffixList {s : Symbol T g.NT} {u : List (Symbol T g.NT)}
    (hu : (s :: u) ∈ suffixList g) : u ∈ suffixList g := by
  obtain ⟨r, hr, hmem⟩ := mem_suffixList.mp hu
  refine mem_suffixList.mpr ⟨r, hr, ?_⟩
  rw [List.mem_tails] at hmem ⊢
  obtain ⟨p, hp⟩ := hmem
  exact ⟨p ++ [s], by rw [List.append_assoc]; exact hp⟩

/-- One step of a chain nonterminal. The function is total so the rule set
can be formed by `Finset.image` over all index/state tuples; tuples that do
not describe a genuine step map to the identity production, which is sound
for every valuation and adds nothing. -/
private noncomputable def chainStepRule (M : DFA T σ) (p r q : σ) (i : ℕ) :
    ContextFreeRule T (AnnotNT σ g.NT) :=
  match decodeForm g i with
  | Symbol.terminal a :: rest =>
      ⟨.chain p i q,
        [Symbol.terminal a,
          Symbol.nonterminal (.chain (M.step p a) (indexOfForm g rest) q)]⟩
  | Symbol.nonterminal B :: rest =>
      ⟨.chain p i q,
        [Symbol.nonterminal (.main p B r),
          Symbol.nonterminal (.chain r (indexOfForm g rest) q)]⟩
  | [] => ⟨.chain p i q, [Symbol.nonterminal (.chain p i q)]⟩

/-- The DFA-annotated grammar, generating `g.language ⊓ M.accepts`. -/
private noncomputable abbrev interGrammar (g : ContextFreeGrammar T) (M : DFA T σ)
    [Fintype σ] : ContextFreeGrammar T where
  NT := AnnotNT σ g.NT
  initial := .start
  rules :=
    ((Finset.univ.filter fun q => q ∈ M.accept).image fun q =>
        (⟨.start, [Symbol.nonterminal (.main M.start g.initial q)]⟩ :
          ContextFreeRule T (AnnotNT σ g.NT)))
      ∪ ((g.rules ×ˢ (Finset.univ : Finset (σ × σ))).image fun rpq =>
          (⟨.main rpq.2.1 rpq.1.input rpq.2.2,
              [Symbol.nonterminal
                (.chain rpq.2.1 (indexOfForm g rpq.1.output) rpq.2.2)]⟩ :
            ContextFreeRule T (AnnotNT σ g.NT)))
      ∪ ((Finset.univ : Finset σ).image fun p =>
          (⟨.chain p (indexOfForm g []) p, []⟩ :
            ContextFreeRule T (AnnotNT σ g.NT)))
      ∪ (((Finset.range (suffixList g).length) ×ˢ
            (Finset.univ : Finset (σ × σ × σ))).image
          fun iprq => chainStepRule M iprq.2.1 iprq.2.2.1 iprq.2.2.2 iprq.1)

/-- The intended meaning of each annotated nonterminal. -/
private def annotValuation (g : ContextFreeGrammar T) (M : DFA T σ) :
    AnnotNT σ g.NT → Language T
  | .start => { w : List T | Yields g [Symbol.nonterminal g.initial] w ∧
      M.evalFrom M.start w ∈ M.accept }
  | .main p A q => { w : List T | Yields g [Symbol.nonterminal A] w ∧
      M.evalFrom p w = q }
  | .chain p i q => { w : List T | Yields g (decodeForm g i) w ∧
      M.evalFrom p w = q }

private theorem annotValuation_start :
    annotValuation g M .start =
      { w : List T | Yields g [Symbol.nonterminal g.initial] w ∧
        M.evalFrom M.start w ∈ M.accept } :=
  rfl

private theorem annotValuation_main (p q : σ) (A : g.NT) :
    annotValuation g M (.main p A q) =
      { w : List T | Yields g [Symbol.nonterminal A] w ∧ M.evalFrom p w = q } :=
  rfl

private theorem annotValuation_chain (p q : σ) (i : ℕ) :
    annotValuation g M (.chain p i q) =
      { w : List T | Yields g (decodeForm g i) w ∧ M.evalFrom p w = q } :=
  rfl

private theorem decodeForm_indexOfForm_nil : decodeForm g (indexOfForm g []) = [] := by
  by_cases hnil : ([] : List (Symbol T g.NT)) ∈ suffixList g
  · exact decodeForm_indexOfForm hnil
  · have hempty : suffixList g = [] := by
      by_contra hne
      obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨r, hr, -⟩ := mem_suffixList.mp hu
      exact hnil (mem_suffixList.mpr
        ⟨r, hr, (List.mem_tails _ _).mpr ⟨r.output, by simp⟩⟩)
    unfold decodeForm indexOfForm
    simp [hempty]

/-- Inverting a yield from one nonterminal: a first production and a yield
from its output. -/
private theorem yields_singleton_inv {A : g.NT} {w : List T}
    (h : Yields g [Symbol.nonterminal A] w) :
    ∃ r ∈ g.rules, r.input = A ∧ Yields g r.output w := by
  cases h with
  | nonterminal hr hout hrest =>
    cases hrest
    exact ⟨_, hr, rfl, by simpa using hout⟩

private theorem isValuation_interGrammar [Fintype σ] :
    IsValuation (interGrammar g M) (annotValuation g M) := by
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  swap
  · -- Chain step rules.
    obtain ⟨⟨i, p, mid, q⟩, hmem, rfl⟩ := Finset.mem_image.mp hr
    have hi : i < (suffixList g).length :=
      Finset.mem_range.mp (Finset.mem_product.mp hmem).1
    have hmemform : decodeForm g i ∈ suffixList g := mem_suffixList_of_decodeForm hi
    cases hform : decodeForm g i with
    | nil =>
      unfold chainStepRule
      rw [hform]
      simp
    | cons s rest =>
      have hrestmem : rest ∈ suffixList g := by
        have h' := hmemform
        rw [hform] at h'
        exact tail_mem_suffixList h'
      have hdecode_rest : decodeForm g (indexOfForm g rest) = rest :=
        decodeForm_indexOfForm hrestmem
      cases s with
      | terminal a =>
        unfold chainStepRule
        rw [hform]
        intro w hw
        obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
        obtain ⟨y₁, hy₁, y₂, hy₂, hyapp⟩ := Language.mem_mul.mp hy
        have hx' : x = [a] := hx
        have hy₂' : y₂ = [] := hy₂
        subst hx'
        subst hy₂'
        simp only [List.append_nil] at hyapp
        subst hyapp
        subst hxy
        simp only [evalSymbol_nonterminal] at hy₁
        rw [annotValuation_chain, hdecode_rest] at hy₁
        rw [annotValuation_chain, hform]
        exact ⟨Yields.terminal a hy₁.1, hy₁.2⟩
      | nonterminal B =>
        unfold chainStepRule
        rw [hform]
        intro w hw
        obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
        obtain ⟨y₁, hy₁, y₂, hy₂, hyapp⟩ := Language.mem_mul.mp hy
        have hy₂' : y₂ = [] := hy₂
        subst hy₂'
        simp only [List.append_nil] at hyapp
        subst hyapp
        subst hxy
        simp only [evalSymbol_nonterminal] at hx hy₁
        rw [annotValuation_main] at hx
        rw [annotValuation_chain, hdecode_rest] at hy₁
        obtain ⟨rb, hrb, hrinput, hrbt⟩ := yields_singleton_inv hx.1
        subst hrinput
        rw [annotValuation_chain, hform]
        refine ⟨Yields.nonterminal hrb hrbt hy₁.1, ?_⟩
        rw [DFA.evalFrom_of_append, hx.2]
        exact hy₁.2
  rcases Finset.mem_union.mp hr with hr | hr
  swap
  · -- Empty chain rules.
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hr
    intro w hw
    have hw0 : w = [] := hw
    subst hw0
    rw [annotValuation_chain, decodeForm_indexOfForm_nil]
    exact ⟨Yields.nil, rfl⟩
  rcases Finset.mem_union.mp hr with hr | hr
  swap
  · -- Main (production) rules.
    obtain ⟨⟨r₀, p, q⟩, hmem, rfl⟩ := Finset.mem_image.mp hr
    have hr₀ : r₀ ∈ g.rules := (Finset.mem_product.mp hmem).1
    simp only [evalForm_cons, evalForm_nil, evalSymbol_nonterminal, annotValuation_chain,
      annotValuation_main, decodeForm_indexOfForm (output_mem_suffixList hr₀)]
    intro w hw
    obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
    have hy0 : y = [] := hy
    subst hy0
    simp only [List.append_nil] at hxy
    subst hxy
    exact ⟨yields_of_rule hr₀ hx.1, hx.2⟩
  · -- Start rules.
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    have hqacc : q ∈ M.accept := (Finset.mem_filter.mp hq).2
    simp only [evalForm_cons, evalForm_nil, evalSymbol_nonterminal, annotValuation_main,
      annotValuation_start]
    intro w hw
    obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hw
    have hy0 : y = [] := hy
    subst hy0
    simp only [List.append_nil] at hxy
    subst hxy
    exact ⟨hx.1, by rw [hx.2]; exact hqacc⟩

private theorem mem_chainStepRule [Fintype σ] {p mid q : σ} {i : ℕ}
    (hi : i < (suffixList g).length) :
    chainStepRule M p mid q i ∈ (interGrammar g M).rules :=
  Finset.mem_union_right _
    (Finset.mem_image.mpr
      ⟨(i, p, mid, q), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_univ _⟩, rfl⟩)

private theorem chainStepRule_input {p r q : σ} {i : ℕ} :
    (chainStepRule (g := g) M p r q i).input = .chain p i q := by
  unfold chainStepRule
  split <;> rfl

private theorem chainStepRule_output_terminal {p mid q : σ} {a : T}
    {rest : List (Symbol T g.NT)} {i : ℕ}
    (hdec : decodeForm g i = Symbol.terminal (N := g.NT) a :: rest) :
    (chainStepRule M p mid q i).output =
      [Symbol.terminal (N := AnnotNT σ g.NT) a,
        Symbol.nonterminal (.chain (M.step p a) (indexOfForm g rest) q)] := by
  unfold chainStepRule
  rw [hdec]

private theorem chainStepRule_output_nonterminal {p mid q : σ} {B : g.NT}
    {rest : List (Symbol T g.NT)} {i : ℕ}
    (hdec : decodeForm g i = Symbol.nonterminal (T := T) B :: rest) :
    (chainStepRule M p mid q i).output =
      [Symbol.nonterminal (.main p B mid),
        Symbol.nonterminal (.chain mid (indexOfForm g rest) q)] := by
  unfold chainStepRule
  rw [hdec]

/-- Completeness for chain nonterminals: a yield through a form, tracked
through the DFA, is an annotated derivation. -/
private theorem derives_chain [Fintype σ] {u : List (Symbol T g.NT)} {w : List T}
    {p q : σ} (hu : u ∈ suffixList g) (hy : Yields g u w)
    (he : M.evalFrom p w = q) :
    (interGrammar g M).Derives
      [Symbol.nonterminal (.chain p (indexOfForm g u) q)] (w.map Symbol.terminal) := by
  induction hy generalizing p q with
  | nil =>
    have hqp : q = p := he.symm
    subst hqp
    exact ContextFreeGrammar.Produces.single
      ⟨⟨.chain q (indexOfForm g []) q, []⟩,
        Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩)),
        ContextFreeRule.Rewrites.input_output⟩
  | terminal a _ ih =>
    have htailmem : ‹List (Symbol T g.NT)› ∈ suffixList g := tail_mem_suffixList hu
    have hdec : decodeForm g (indexOfForm g (Symbol.terminal (N := g.NT) a :: ‹_›)) =
        Symbol.terminal (N := g.NT) a :: ‹_› := decodeForm_indexOfForm hu
    have hstep : (interGrammar g M).Produces
        [Symbol.nonterminal
          (.chain p (indexOfForm g (Symbol.terminal (N := g.NT) a :: ‹_›)) q)]
        [Symbol.terminal a,
          Symbol.nonterminal (.chain (M.step p a) (indexOfForm g ‹_›) q)] := by
      refine ⟨chainStepRule M p q q
          (indexOfForm g (Symbol.terminal (N := g.NT) a :: ‹List (Symbol T g.NT)›)),
        mem_chainStepRule ?_, ?_⟩
      · exact List.idxOf_lt_length_of_mem hu
      · have hprod := ContextFreeRule.Rewrites.input_output
          (r := chainStepRule (g := g) M p q q
            (indexOfForm g (Symbol.terminal (N := g.NT) a :: ‹List (Symbol T g.NT)›)))
        rwa [chainStepRule_input, chainStepRule_output_terminal hdec] at hprod
    have htail := ih htailmem (by simpa [DFA.evalFrom_cons] using he)
    have hboth := derives_append (g := interGrammar g M)
      (ContextFreeGrammar.Derives.refl (g := interGrammar g M)
        [Symbol.terminal (N := AnnotNT σ g.NT) a]) htail
    simpa using hstep.trans_derives hboth
  | nonterminal hr _ _ ihout ihrest =>
    rename_i r₀ u₀ w₁ w₂ hout hrest
    have htailmem : ‹List (Symbol T g.NT)› ∈ suffixList g := tail_mem_suffixList hu
    set mid : σ := M.evalFrom p w₁ with hmid
    have hdec : decodeForm g (indexOfForm g (Symbol.nonterminal r₀.input :: u₀)) =
        Symbol.nonterminal r₀.input :: u₀ := decodeForm_indexOfForm hu
    have hstep : (interGrammar g M).Produces
        [Symbol.nonterminal (.chain p (indexOfForm g (Symbol.nonterminal r₀.input :: u₀)) q)]
        [Symbol.nonterminal (.main p r₀.input mid),
          Symbol.nonterminal (.chain mid (indexOfForm g u₀) q)] := by
      refine ⟨chainStepRule M p mid q
          (indexOfForm g (Symbol.nonterminal r₀.input :: u₀)), mem_chainStepRule ?_, ?_⟩
      · exact List.idxOf_lt_length_of_mem hu
      · have hprod := ContextFreeRule.Rewrites.input_output
          (r := chainStepRule (g := g) M p mid q
            (indexOfForm g (Symbol.nonterminal r₀.input :: u₀)))
        rwa [chainStepRule_input, chainStepRule_output_nonterminal hdec] at hprod
    have hmainstep : (interGrammar g M).Produces
        [Symbol.nonterminal (.main p r₀.input mid)]
        [Symbol.nonterminal (.chain p (indexOfForm g r₀.output) mid)] :=
      ⟨⟨.main p r₀.input mid,
          [Symbol.nonterminal (.chain p (indexOfForm g r₀.output) mid)]⟩,
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr
            ⟨(r₀, p, mid), Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, rfl⟩))),
        ContextFreeRule.Rewrites.input_output⟩
    have hmain : (interGrammar g M).Derives
        [Symbol.nonterminal (.main p r₀.input mid)] (w₁.map Symbol.terminal) :=
      hmainstep.trans_derives (ihout (output_mem_suffixList hr) rfl)
    have hrest' : (interGrammar g M).Derives
        [Symbol.nonterminal (.chain mid (indexOfForm g u₀) q)] (w₂.map Symbol.terminal) :=
      ihrest htailmem (by
        have happend : M.evalFrom p (w₁ ++ w₂) = M.evalFrom mid w₂ := by
          rw [DFA.evalFrom_of_append]
        rw [← happend]
        exact he)
    have hboth := derives_append (g := interGrammar g M) hmain hrest'
    rw [← List.map_append] at hboth
    exact hstep.trans_derives hboth

/-- Completeness for main nonterminals: a yield from one nonterminal,
tracked through the DFA, is an annotated derivation. -/
private theorem derives_main [Fintype σ] {A : g.NT} {w : List T} {p q : σ}
    (hy : Yields g [Symbol.nonterminal A] w) (he : M.evalFrom p w = q) :
    (interGrammar g M).Derives
      [Symbol.nonterminal (.main p A q)] (w.map Symbol.terminal) := by
  obtain ⟨r, hr, hrinput, hout⟩ := yields_singleton_inv hy
  subst hrinput
  have hstep : (interGrammar g M).Produces
      [Symbol.nonterminal (.main p r.input q)]
      [Symbol.nonterminal (.chain p (indexOfForm g r.output) q)] :=
    ⟨⟨.main p r.input q,
        [Symbol.nonterminal (.chain p (indexOfForm g r.output) q)]⟩,
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr
          ⟨(r, p, q), Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, rfl⟩))),
      ContextFreeRule.Rewrites.input_output⟩
  exact hstep.trans_derives
    (derives_chain (output_mem_suffixList hr) hout he)

private theorem interGrammar_language [Fintype σ] :
    (interGrammar g M).language = g.language ⊓ M.accepts := by
  apply le_antisymm
  · have hle := language_le_of_valuation (g := interGrammar g M)
      isValuation_interGrammar
    intro w hw
    have hw' : Yields g [Symbol.nonterminal g.initial] w ∧
        M.evalFrom M.start w ∈ M.accept := hle hw
    exact ⟨mem_language_iff_yields.mpr hw'.1, hw'.2⟩
  · intro w hw
    have hg : w ∈ g.language := hw.1
    have hacc : M.evalFrom M.start w ∈ M.accept := hw.2
    apply (ContextFreeGrammar.mem_language_iff _ _).mpr
    have hy : Yields g [Symbol.nonterminal g.initial] w :=
      mem_language_iff_yields.mp hg
    have hstep : (interGrammar g M).Produces [Symbol.nonterminal .start]
        [Symbol.nonterminal (.main M.start g.initial (M.evalFrom M.start w))] :=
      ⟨⟨.start, [Symbol.nonterminal (.main M.start g.initial (M.evalFrom M.start w))]⟩,
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image.mpr
            ⟨M.evalFrom M.start w,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc⟩, rfl⟩))),
        ContextFreeRule.Rewrites.input_output⟩
    exact hstep.trans_derives (derives_main hy rfl)

/-- **Intersection of a context-free language with the language of a DFA.** If $L$ is a
context-free language over an alphabet $T$ and $M$ is a deterministic finite automaton over $T$
with finitely many states, then the intersection of $L$ with the language accepted by $M$ is
context-free. -/
theorem IsContextFree.inf_dfa_accepts [Finite σ] {L : Language T}
    (hL : L.IsContextFree) (M : DFA T σ) :
    (L ⊓ M.accepts).IsContextFree := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨@interGrammar T σ g M (Fintype.ofFinite σ),
    @interGrammar_language T σ g M (Fintype.ofFinite σ)⟩

/-- **Intersection of a context-free language with a regular language.** If $L$ is a context-free
language and $R$ a regular language over the same alphabet, then $L \cap R$ is context-free.

No finite-alphabet assumption is needed: the grammar built in the proof only mentions terminals
that occur in the productions of the original grammar. -/
theorem IsContextFree.inf_isRegular {L R : Language T} (hL : L.IsContextFree)
    (hR : R.IsRegular) :
    (L ⊓ R).IsContextFree := by
  obtain ⟨σ, hσ, M, rfl⟩ := hR
  exact @IsContextFree.inf_dfa_accepts T σ (@Finite.of_fintype σ hσ) _ hL M

end Cslib.Language
