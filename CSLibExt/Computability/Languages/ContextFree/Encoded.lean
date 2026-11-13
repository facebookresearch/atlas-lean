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

/-- **Renaming the nonterminals of a symbol twice.** For maps $f : N_1 \to N_2$ and
$b : N_2 \to N_3$ and a grammar symbol $s$ with terminals in $T$ and nonterminals in $N_1$,
renaming the nonterminals of $s$ by $f$ and then by $b$ gives the same symbol as renaming them by
$b \circ f$. -/
@[simp]
theorem mapSymbol_mapSymbol {N₁ N₂ N₃ : Type*} (f : N₁ → N₂) (b : N₂ → N₃) (s : Symbol T N₁) :
    mapSymbol b (mapSymbol f s) = mapSymbol (b ∘ f) s := by
  cases s <;> rfl

/-- **Grammars with renamings in both directions generate the same language.** Let $g$ and $G$
be context-free grammars over the same terminals. Suppose there are maps $f$ from the
nonterminals of $g$ to those of $G$ and $b$ from the nonterminals of $G$ to those of $g$ such
that renaming the nonterminals of any production of $g$ by $f$ gives a production of $G$,
renaming the nonterminals of any production of $G$ by $b$ gives a production of $g$, $f$ sends
the start nonterminal of $g$ to that of $G$, and $b$ sends the start nonterminal of $G$ to that
of $g$. Then $g$ and $G$ generate the same language. The renamings need not be inverse to each
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

/-- **Encoded context-free grammars.** An encoded context-free grammar over a terminal type $T$
consists of a start nonterminal, which is a natural number, and a list of productions. Each
production is a pair of a left-hand side, a natural number, and a right-hand side, a list of
elements of the disjoint union $\mathbb{N} \sqcup T$, in which a number $i$ from the left summand
stands for nonterminal $i$ and an element $a$ of $T$ for terminal $a$.

Unlike a general context-free grammar, whose type of nonterminals is part of its data, an
encoded grammar is a concrete object that computable functions can take and return. -/
structure EncodedCFG (T : Type*) where
  /-- The start nonterminal. -/
  start : ℕ
  /-- The productions. -/
  rules : List (ℕ × List (ℕ ⊕ T))

namespace EncodedCFG

/-- **Decoding a grammar symbol.** Decoding sends an element of the disjoint union
$\mathbb{N} \sqcup T$ to a grammar symbol with terminals $T$ and nonterminals $\mathbb{N}$:
a natural number $i$ from the left summand goes to the nonterminal $i$, and an element $a$ of
$T$ from the right summand goes to the terminal $a$. -/
def decodeSymbol : ℕ ⊕ T → Symbol T ℕ
  | .inl i => .nonterminal i
  | .inr a => .terminal a

/-- **Encoding a grammar symbol.** Encoding sends a grammar symbol with terminals $T$ and
nonterminals $\mathbb{N}$ to an element of the disjoint union $\mathbb{N} \sqcup T$: the
terminal $a$ goes to $a$ in the right summand $T$, and the nonterminal $i$ goes to $i$ in the
left summand $\mathbb{N}$. -/
def encodeSymbol : Symbol T ℕ → ℕ ⊕ T
  | .terminal a => .inr a
  | .nonterminal i => .inl i

@[simp]
theorem decodeSymbol_encodeSymbol (s : Symbol T ℕ) : decodeSymbol (encodeSymbol s) = s := by
  cases s <;> rfl

@[simp]
theorem encodeSymbol_decodeSymbol (s : ℕ ⊕ T) : encodeSymbol (decodeSymbol s) = s := by
  cases s <;> rfl

/-- **Decoding a production.** Decoding a pair $(A, s)$ of a natural number $A$ and a list $s$
of elements of the disjoint union $\mathbb{N} \sqcup T$ gives the production, with terminals
$T$ and nonterminals $\mathbb{N}$, whose left-hand side is the nonterminal $A$ and whose
right-hand side is $s$ with each entry decoded as a symbol: a number $i$ from the left summand
becomes the nonterminal $i$ and an element $a$ of $T$ becomes the terminal $a$. -/
def decodeRule (e : ℕ × List (ℕ ⊕ T)) : ContextFreeRule T ℕ :=
  ⟨e.1, e.2.map decodeSymbol⟩

/-- **Encoding a production.** Encoding a production with terminals $T$ and nonterminals
$\mathbb{N}$ gives the pair $(A, s)$ where $A \in \mathbb{N}$ is its left-hand side and $s$ is
its right-hand side with each symbol encoded as an element of the disjoint union
$\mathbb{N} \sqcup T$: the terminal $a$ becomes $a$ in the right summand and the nonterminal
$i$ becomes $i$ in the left summand. -/
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

/-- **Grammar denoted by an encoding.** For an encoded context-free grammar $g$ over $T$, the
context-free grammar over $T$ whose nonterminals are the natural numbers, whose initial
nonterminal is the start nonterminal of $g$, and whose productions are the decodings of the
encoded productions of $g$: an encoded production $(i, u)$ becomes the production rewriting the
nonterminal $i$ to the word obtained from $u$ by reading each entry $\mathrm{inl}\, j$ as the
nonterminal $j$ and each entry $\mathrm{inr}\, a$ as the terminal $a$. -/
abbrev toCFG (g : EncodedCFG T) : ContextFreeGrammar T where
  NT := ℕ
  initial := g.start
  rules := (g.rules.map decodeRule).toFinset

/-- **Language of an encoded grammar.** The language of an encoded context-free grammar $g$ over
$T$ is the language generated by the context-free grammar that $g$ denotes, whose nonterminals
are the natural numbers, whose initial nonterminal is the start nonterminal of $g$ and whose
productions are the decoded productions of $g$. -/
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

/-- **Nonterminal of a symbol.** The partial map from grammar symbols with terminals in $T$ and
nonterminals in $N$ to $N$ that sends a nonterminal $A$ to $A$ and has no value on terminals. -/
def ntOf {N : Type*} : Symbol T N → Option N
  | .terminal _ => none
  | .nonterminal A => some A

/-- **List of nonterminals mentioned by a grammar.** For a context-free grammar $G$, the list
consisting of the initial nonterminal of $G$ followed, for each production of $G$ in turn (in some
fixed order of its finite set of productions), by the left-hand side of the production and then
the nonterminals of its right-hand side in order. Nonterminals may occur more than once. -/
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
/-- **Numbering of nonterminals.** For a context-free grammar $G$, the number of a nonterminal $A$
of $G$ is the position, counting from $0$, of the first occurrence of $A$ in the list of
nonterminals that $G$ mentions (its initial nonterminal first); if $A$ does not occur in that
list, its number is the length of the list. -/
noncomputable def ntIndex (G : ContextFreeGrammar T) (A : G.NT) : ℕ :=
  (usedNT G).idxOf A

/-- **Nonterminal with a given number.** For a context-free grammar $G$ and a natural number $n$,
the nonterminal of $G$ with number $n$ is the entry at position $n$, counting from $0$, of the
list of nonterminals that $G$ mentions (its initial nonterminal first); if the list has no entry
at position $n$, it is the initial nonterminal of $G$. -/
noncomputable def ntOfIndex (G : ContextFreeGrammar T) (n : ℕ) : G.NT :=
  (usedNT G).getD n G.initial

theorem ntOfIndex_ntIndex {G : ContextFreeGrammar T} {A : G.NT} (hA : A ∈ usedNT G) :
    ntOfIndex G (ntIndex G A) = A := by
  classical
  have hlt : (usedNT G).idxOf A < (usedNT G).length := List.idxOf_lt_length_of_mem hA
  simp only [ntOfIndex, ntIndex]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by convert hlt), Option.getD_some]
  convert List.getElem_idxOf hlt

/-- **Numbering the nonterminals of a production and back recovers it.** Let $G$ be a context-free
grammar over $T$ and $r$ a production of $G$. Replacing each nonterminal $A$ of $r$ by its number,
the position, counting from $0$, of the first occurrence of $A$ in the list of nonterminals that
$G$ mentions, and then replacing each number $n$ by the nonterminal of $G$ with number $n$ (the
entry at position $n$ of that list, or the initial nonterminal of $G$ if the list has no such
entry) gives $r$ again. -/
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

/-- **Encoding of a context-free grammar.** For a context-free grammar $G$ over $T$, the encoded
grammar whose start nonterminal is the number of the initial nonterminal of $G$ and whose
productions are the productions of $G$, listed in some fixed order, with every nonterminal $A$
replaced by its number, the position, counting from $0$, of the first occurrence of $A$ in the
list of nonterminals that $G$ mentions (its initial nonterminal first). -/
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

/-- **Encoded grammars as pairs.** Sending an encoded grammar over $T$ to the pair of its start
nonterminal and its list of productions is a bijection from encoded grammars over $T$ onto
pairs $(s, R)$ of a natural number $s$ and a list $R$ of pairs of a natural number and a list
of elements of the disjoint union $\mathbb{N} \sqcup T$. -/
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
