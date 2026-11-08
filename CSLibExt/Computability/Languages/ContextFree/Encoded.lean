/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Encoded context-free grammars
-/
module

public import CSLibExt.Computability.Languages.ContextFree.Basic
public import Mathlib.Computability.Primrec.List

/-!
# Encoded context-free grammars

Mathlib's `ContextFreeGrammar` carries its type of nonterminals as a field, so
grammars do not form a `Primcodable` type and cannot be inputs or outputs of
computable functions. `EncodedCFG T` is a concrete encoding: the nonterminals
are natural numbers, the start nonterminal is a number, and the productions are
a list of pairs of a left-hand side and a right-hand side, in which `Sum.inl i`
stands for nonterminal `i` and `Sum.inr a` for terminal `a`. The decoded grammar
has nonterminals `ℕ`; only finitely many of them occur in its productions, and those can be
reindexed by some `Fin n`.

* `EncodedCFG.toCFG`, `EncodedCFG.language`: the grammar an encoding denotes,
  with nonterminals `ℕ`, and its language.
* The `Primcodable (EncodedCFG T)` instance, with `primrec_start`,
  `primrec_rules` and `primrec₂_mk`.
* `EncodedCFG.ofCFG` and `EncodedCFG.language_ofCFG`: every grammar, whatever
  its type of nonterminals, has an encoding with the same language;
  `EncodedCFG.isContextFree_iff`: a language is context-free exactly when it is
  the language of an encoded grammar.
* `language_eq_of_maps`: two grammars with nonterminal renamings in both
  directions that preserve the productions and the start nonterminal generate
  the same language.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*}

/-- Renaming twice is renaming with the composite. -/
@[simp]
theorem mapSymbol_mapSymbol {N₁ N₂ N₃ : Type*} (f : N₁ → N₂) (b : N₂ → N₃) (s : Symbol T N₁) :
    mapSymbol b (mapSymbol f s) = mapSymbol (b ∘ f) s := by
  cases s <;> rfl

/-- Two grammars generate the same language when there are nonterminal
renamings in both directions that map productions to productions and the start
nonterminal to the start nonterminal. The renamings need not be inverse to each
other. -/
theorem language_eq_of_maps {g G : ContextFreeGrammar T} (f : g.NT → G.NT) (b : G.NT → g.NT)
    (hf : ∀ r ∈ g.rules, mapRule f r ∈ G.rules) (hb : ∀ r ∈ G.rules, mapRule b r ∈ g.rules)
    (hfi : f g.initial = G.initial) (hbi : b G.initial = g.initial) :
    G.language = g.language := by
  ext w
  simp only [ContextFreeGrammar.mem_language_iff]
  constructor
  · intro h
    simpa [List.map_map, hbi] using derives_map_of_forall_mem hb h
  · intro h
    simpa [List.map_map, hfi] using derives_map_of_forall_mem hf h

/-- A context-free grammar in a form that computable functions can take and
return: nonterminals are natural numbers, and each production is a pair of a
left-hand side and a right-hand side, in which `Sum.inl i` is nonterminal `i`
and `Sum.inr a` is terminal `a`. -/
structure EncodedCFG (T : Type*) where
  /-- The start nonterminal. -/
  start : ℕ
  /-- The productions. -/
  rules : List (ℕ × List (ℕ ⊕ T))

namespace EncodedCFG

/-- Decode a symbol. -/
def decodeSymbol : ℕ ⊕ T → Symbol T ℕ
  | .inl i => .nonterminal i
  | .inr a => .terminal a

/-- Encode a symbol. -/
def encodeSymbol : Symbol T ℕ → ℕ ⊕ T
  | .terminal a => .inr a
  | .nonterminal i => .inl i

@[simp]
theorem decodeSymbol_encodeSymbol (s : Symbol T ℕ) : decodeSymbol (encodeSymbol s) = s := by
  cases s <;> rfl

@[simp]
theorem encodeSymbol_decodeSymbol (s : ℕ ⊕ T) : encodeSymbol (decodeSymbol s) = s := by
  cases s <;> rfl

/-- Decode a production. -/
def decodeRule (e : ℕ × List (ℕ ⊕ T)) : ContextFreeRule T ℕ :=
  ⟨e.1, e.2.map decodeSymbol⟩

/-- Encode a production. -/
def encodeRule (r : ContextFreeRule T ℕ) : ℕ × List (ℕ ⊕ T) :=
  (r.input, r.output.map encodeSymbol)

@[simp]
theorem decodeRule_encodeRule (r : ContextFreeRule T ℕ) : decodeRule (encodeRule r) = r := by
  cases r
  simp [decodeRule, encodeRule, List.map_map, Function.comp_def]

@[simp]
theorem encodeRule_decodeRule (e : ℕ × List (ℕ ⊕ T)) : encodeRule (decodeRule e) = e := by
  cases e
  simp [decodeRule, encodeRule, List.map_map, Function.comp_def]

section Semantics

variable [DecidableEq T]

/-- The grammar an encoding denotes, with nonterminals `ℕ` (reducibly, so that
nonterminals of `g.toCFG` can be written as numerals). -/
abbrev toCFG (g : EncodedCFG T) : ContextFreeGrammar T where
  NT := ℕ
  initial := g.start
  rules := (g.rules.map decodeRule).toFinset

/-- The language of an encoded grammar. -/
def language (g : EncodedCFG T) : Language T :=
  g.toCFG.language

theorem mem_toCFG_rules {g : EncodedCFG T} {r : ContextFreeRule T ℕ} :
    r ∈ g.toCFG.rules ↔ ∃ e ∈ g.rules, decodeRule e = r :=
  List.mem_toFinset.trans List.mem_map

theorem mem_language_iff {g : EncodedCFG T} {w : List T} :
    w ∈ g.language ↔
      g.toCFG.Derives [Symbol.nonterminal g.start] (w.map Symbol.terminal) :=
  Iff.rfl

/-- The language of an encoded grammar is context-free. -/
theorem language_isContextFree (g : EncodedCFG T) : g.language.IsContextFree :=
  ⟨g.toCFG, rfl⟩

end Semantics

section Numbering

/-- The nonterminal of a symbol, if it is one. -/
def ntOf {N : Type*} : Symbol T N → Option N
  | .terminal _ => none
  | .nonterminal A => some A

/-- The nonterminals a grammar mentions, its initial nonterminal first. -/
noncomputable def usedNT (G : ContextFreeGrammar T) : List G.NT :=
  G.initial :: G.rules.toList.flatMap fun r => r.input :: r.output.filterMap ntOf

theorem initial_mem_usedNT (G : ContextFreeGrammar T) : G.initial ∈ usedNT G :=
  List.mem_cons_self ..

theorem input_mem_usedNT {G : ContextFreeGrammar T} {r : ContextFreeRule T G.NT}
    (hr : r ∈ G.rules) : r.input ∈ usedNT G :=
  List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨r, Finset.mem_toList.2 hr, List.mem_cons_self ..⟩)

theorem output_mem_usedNT {G : ContextFreeGrammar T} {r : ContextFreeRule T G.NT}
    (hr : r ∈ G.rules) {A : G.NT} (hA : Symbol.nonterminal A ∈ r.output) : A ∈ usedNT G :=
  List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨r, Finset.mem_toList.2 hr,
    List.mem_cons_of_mem _ (List.mem_filterMap.2 ⟨_, hA, rfl⟩)⟩)

open Classical in
/-- The number of a nonterminal: its position in `usedNT`. -/
noncomputable def ntIndex (G : ContextFreeGrammar T) (A : G.NT) : ℕ :=
  (usedNT G).idxOf A

/-- The nonterminal with a given number, or the initial one. -/
noncomputable def ntOfIndex (G : ContextFreeGrammar T) (n : ℕ) : G.NT :=
  (usedNT G).getD n G.initial

theorem ntOfIndex_ntIndex {G : ContextFreeGrammar T} {A : G.NT} (hA : A ∈ usedNT G) :
    ntOfIndex G (ntIndex G A) = A := by
  classical
  have hlt : (usedNT G).idxOf A < (usedNT G).length := List.idxOf_lt_length_of_mem hA
  simp only [ntOfIndex, ntIndex]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by convert hlt), Option.getD_some]
  convert List.getElem_idxOf hlt

/-- Renaming a production of `G` to numbers and back gives it back. -/
theorem mapRule_ntOfIndex_ntIndex {G : ContextFreeGrammar T} {r : ContextFreeRule T G.NT}
    (hr : r ∈ G.rules) : mapRule (ntOfIndex G) (mapRule (ntIndex G) r) = r := by
  cases r with
  | mk input output =>
    simp only [mapRule, List.map_map, ContextFreeRule.mk.injEq]
    refine ⟨ntOfIndex_ntIndex (input_mem_usedNT hr), ?_⟩
    conv_rhs => rw [← List.map_id output]
    refine List.map_congr_left fun s hs => ?_
    cases s with
    | terminal a => rfl
    | nonterminal A =>
        simp only [Function.comp_apply, mapSymbol_nonterminal, id_eq]
        rw [ntOfIndex_ntIndex (output_mem_usedNT hr hs)]

end Numbering

section Encoding

variable [DecidableEq T]

/-- An encoding of any context-free grammar: its nonterminals are numbered by
their positions in `usedNT`. -/
noncomputable def ofCFG (G : ContextFreeGrammar T) : EncodedCFG T :=
  ⟨ntIndex G G.initial, G.rules.toList.map fun r => encodeRule (mapRule (ntIndex G) r)⟩

/-- **The encoding of a grammar generates the same language.** -/
theorem language_ofCFG (G : ContextFreeGrammar T) : (ofCFG G).language = G.language := by
  refine language_eq_of_maps (g := G) (G := (ofCFG G).toCFG) (ntIndex G) (ntOfIndex G)
    (fun r hr => ?_) (fun r hr => ?_) rfl (ntOfIndex_ntIndex (initial_mem_usedNT G))
  · exact mem_toCFG_rules.2 ⟨_, List.mem_map.2 ⟨r, Finset.mem_toList.2 hr, rfl⟩,
      decodeRule_encodeRule _⟩
  · obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.1 hr
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 he
    change mapRule (ntOfIndex G) (decodeRule (encodeRule (mapRule (ntIndex G) r₀))) ∈ G.rules
    rw [decodeRule_encodeRule, mapRule_ntOfIndex_ntIndex (Finset.mem_toList.1 hr₀)]
    exact Finset.mem_toList.1 hr₀

/-- **A language is context-free exactly when an encoded grammar generates
it.** -/
theorem isContextFree_iff {L : Language T} :
    L.IsContextFree ↔ ∃ g : EncodedCFG T, g.language = L :=
  ⟨fun ⟨G, hG⟩ => ⟨ofCFG G, (language_ofCFG G).trans hG⟩,
    fun ⟨g, hg⟩ => hg ▸ language_isContextFree g⟩

end Encoding

section Primcodable

/-- Encoded grammars are pairs of a start nonterminal and a production list. -/
def equivProd : EncodedCFG T ≃ ℕ × List (ℕ × List (ℕ ⊕ T)) where
  toFun g := (g.start, g.rules)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Primcodable T]

instance : Primcodable (EncodedCFG T) :=
  Primcodable.ofEquiv _ equivProd

theorem primrec_equivProd : Primrec (equivProd (T := T)) :=
  Primrec.of_equiv

theorem primrec_start : Primrec (start (T := T)) :=
  Primrec.fst.comp primrec_equivProd

theorem primrec_rules : Primrec (rules (T := T)) :=
  Primrec.snd.comp primrec_equivProd

theorem primrec₂_mk : Primrec₂ (mk (T := T)) :=
  (Primrec.of_equiv_symm (e := equivProd (T := T))).of_eq fun _ => rfl

end Primcodable

end EncodedCFG

end Cslib.Language
