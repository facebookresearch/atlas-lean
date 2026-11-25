/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The complement of the Post correspondence problem reduces to universality of CFGs
-/
module

public import CSLibExt.Computability.Decidability.CFGUndecidable

/-!
# The complement of the Post correspondence problem reduces to universality of CFGs

Over a finite alphabet `α`, write the index `i` of a domino in unary as the bits `| 1ⁱ`
(`bitCode`, with `true` for `|`). The **list language** of one side of a PCP instance `P` is
`{ w_{i₁} ⋯ w_{iₙ} code(iₙ) ⋯ code(i₁) | n ≥ 1 }` over `α ⊕ Bool` (`listLang`), and `P` has a
solution exactly when the top and bottom list languages meet (`pcp_iff_exists_mem_listLang`).

The complement of a list language is context-free, and `univGrammar P` generates the union of the
two complements, so it generates every word exactly when `P` has no solution
(`forall_mem_language_univGrammar_iff`). A word is outside the top list language when

* it is **malformed** (`malformedLang`): it has no index bits, its bits start with a `1`, a bit is
  followed by a letter, or some code has at least `|P|` ones; or
* it is well formed, `x code(iₙ) ⋯ code(i₁)`, but `x ≠ t_{i₁} ⋯ t_{iₙ}` (`mismatchLang`). The
  grammar peels `t_{i₁}` off the front of `x` against `code(i₁)` at the end, until `x` stops
  matching: it is a proper prefix of `t_{i₁}`, it disagrees with `t_{i₁}` at a letter, or a nonempty
  rest of `x` is left over at the last index.

The language of each nonterminal is pinned down from above by a valuation
(`Cslib.Language.IsValuation`, `isValuation_univVal`) and from below by explicit derivations.

`univGrammar` is primitive recursive, so the complement of PCP many-one reduces to universality
of encoded context-free grammars (`manyOneReducible_not_pcp_univ`).

## Main results

- `listLang`, `pcp_iff_exists_mem_listLang`.
- `univGrammar`, `language_univGrammar`, `forall_mem_language_univGrammar_iff`.
- `manyOneReducible_not_pcp_univ`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Theorem 5.13
  (`ALL_CFG` is undecidable, there via computation histories).
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation*, 3rd ed., Pearson, 2006, §9.5 (the complements of the list languages are
  context-free, so `L(G) = Σ*` is undecidable).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.Grammar

open Cslib.Language Post

variable {α : Type*}

/-! ### Index codes and list languages -/

/-- **Unary code of an index.** The code of an index $i \in \mathbb{N}$ is the bit word
$\mathbf{t}\,\mathbf{f}^i$ of length $i + 1$: the bit $\mathbf{t}$ (true) followed by $i$ copies
of the bit $\mathbf{f}$ (false); with $|$ for true and $1$ for false, it is the word $|\,1^i$. -/
def bitCode (i : ℕ) : List Bool := true :: List.replicate i false

/-- **Concatenated code of an index sequence.** For a finite sequence $I = (i_1, \dots, i_n)$
of natural numbers, its code is the bit word $c(i_1)\,c(i_2) \cdots c(i_n)$, the concatenation of
the unary codes $c(i) = \mathbf{t}\,\mathbf{f}^i$ of its entries; the empty sequence has the
empty code. -/
def bitCodes (I : List ℕ) : List Bool := I.flatMap bitCode

@[simp]
theorem bitCodes_nil : bitCodes [] = [] := rfl

@[simp]
theorem bitCodes_cons (i : ℕ) (I : List ℕ) :
    bitCodes (i :: I) = true :: (List.replicate i false ++ bitCodes I) := rfl

theorem bitCodes_append (I J : List ℕ) : bitCodes (I ++ J) = bitCodes I ++ bitCodes J := by
  simp [bitCodes]

/-- **List word of an index sequence.** Let $P = (d_0, \dots, d_{m-1})$ be a list of dominoes over
$\alpha$, let $s$ be a function sending each domino to a word over $\alpha$, and set
$w_i = s(d_i)$ for $i < m$ and $w_i = s(\varepsilon, \varepsilon)$ for $i \ge m$, where
$(\varepsilon, \varepsilon)$ is the domino with empty top and bottom. The list word of an index
sequence $i_1, \dots, i_n$ is the word $w_{i_1} \cdots w_{i_n}\, c(i_n) \cdots c(i_1)$ over
$\alpha \oplus \mathrm{Bool}$, where $c(i)$ is the unary code of $i$: the bit $\mathrm{true}$
followed by $i$ bits $\mathrm{false}$. -/
def listWord (side : Domino α → List α) (P : List (Domino α)) (I : List ℕ) : List (α ⊕ Bool) :=
  (flat side P I).map Sum.inl ++ (bitCodes I.reverse).map Sum.inr

/-- **List language of a PCP instance.** Let $P = (d_0, \dots, d_{m-1})$ be a list of dominoes
over $\alpha$, let $s$ be a function sending each domino to a word over $\alpha$ (for instance its
top word), and write $w_i = s(d_i)$. The list language of $s$ and $P$ is the language over
$\alpha \oplus \mathrm{Bool}$ of all words $w_{i_1} \cdots w_{i_n}\, c(i_n) \cdots c(i_1)$ with
$n \ge 1$ and $i_1, \dots, i_n < m$, where $c(i)$ is the unary code of $i$: the bit
$\mathrm{true}$ followed by $i$ bits $\mathrm{false}$. -/
def listLang (side : Domino α → List α) (P : List (Domino α)) : Language (α ⊕ Bool) :=
  {w | ∃ I : List ℕ, I ≠ [] ∧ (∀ i ∈ I, i < P.length) ∧ w = listWord side P I}

theorem mem_listLang {side : Domino α → List α} {P : List (Domino α)} {w : List (α ⊕ Bool)} :
    w ∈ listLang side P ↔
      ∃ I : List ℕ, I ≠ [] ∧ (∀ i ∈ I, i < P.length) ∧ w = listWord side P I :=
  Iff.rfl

theorem eq_of_replicate_append_eq {j j' : ℕ} {u u' : List Bool}
    (hu : ∀ b ∈ u.head?, b = true) (hu' : ∀ b ∈ u'.head?, b = true)
    (h : List.replicate j false ++ u = List.replicate j' false ++ u') : j = j' ∧ u = u' := by
  induction j generalizing j' with
  | zero =>
    cases j' with
    | zero => exact ⟨rfl, by simpa using h⟩
    | succ j' =>
      cases u with
      | nil => simp at h
      | cons b u =>
        simp only [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append,
          List.cons.injEq] at h
        exact absurd (hu b rfl) (by simp [h.1])
  | succ j ih =>
    cases j' with
    | zero =>
      cases u' with
      | nil => simp at h
      | cons b u' =>
        simp only [List.replicate_succ, List.cons_append, List.replicate_zero, List.nil_append,
          List.cons.injEq] at h
        exact absurd (hu' b rfl) (by simp [← h.1])
    | succ j' =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩

theorem head?_bitCodes (I : List ℕ) : ∀ b ∈ (bitCodes I).head?, b = true := by
  cases I <;> simp

/-- **Concatenated index codes are uniquely decodable.** For a finite sequence
$I = (i_1, \dots, i_n)$ of natural numbers write $c(I) = c(i_1) \cdots c(i_n)$, where
$c(i) = \mathbf{t}\,\mathbf{f}^i$ is the unary code of $i$. If $I$ and $J$ are finite sequences of
natural numbers with $c(I) = c(J)$, then $I = J$. -/
theorem bitCodes_injective : Function.Injective bitCodes := by
  intro I
  induction I with
  | nil =>
    intro J h
    cases J with
    | nil => rfl
    | cons j J => simp at h
  | cons i I ih =>
    intro J h
    cases J with
    | nil => simp at h
    | cons j J =>
      simp only [bitCodes_cons, List.cons.injEq, true_and] at h
      obtain ⟨rfl, h'⟩ := eq_of_replicate_append_eq (head?_bitCodes I) (head?_bitCodes J) h
      rw [ih h']

theorem eq_of_listWord_eq {side side' : Domino α → List α} {P : List (Domino α)} {I J : List ℕ}
    (h : listWord side P I = listWord side' P J) :
    flat side P I = flat side' P J ∧ I = J := by
  obtain ⟨hx, hy⟩ := eq_of_map_inl_append_map_inr h
  exact ⟨hx, List.reverse_injective (bitCodes_injective hy)⟩

/-- **A PCP instance is solvable exactly when its top and bottom list languages meet.** A list $P$
of dominoes has a PCP solution if and only if some word belongs both to the list language of the
top words of $P$ and to the list language of the bottom words of $P$. -/
theorem pcp_iff_exists_mem_listLang (P : List (Domino α)) :
    PCP P ↔ ∃ w, w ∈ listLang Prod.fst P ∧ w ∈ listLang Prod.snd P := by
  constructor
  · rintro ⟨s, hne, hmem, htop⟩
    obtain ⟨I, hlt, rfl⟩ := exists_indices hmem
    have hne' : I ≠ [] := by rintro rfl; exact hne rfl
    refine ⟨listWord Prod.fst P I, ⟨I, hne', hlt, rfl⟩, ⟨I, hne', hlt, ?_⟩⟩
    simp only [listWord, flat_eq]
    rw [show (I.map (domino P)).flatMap Prod.fst = (I.map (domino P)).flatMap Prod.snd from htop]
  · rintro ⟨w, ⟨I, hne, hlt, rfl⟩, ⟨J, -, -, h⟩⟩
    obtain ⟨hflat, rfl⟩ := eq_of_listWord_eq h
    refine ⟨I.map (domino P), by simpa using hne, fun d hd ↦ ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
      exact domino_mem (hlt i hi)
    · simpa [flat_eq, top, bottom] using hflat

/-! ### The grammar -/

/-- **Encoded nonterminal.** For a type $\alpha$ and a natural number $A$, the nonterminal $A$ as a
symbol of an encoded grammar over the alphabet $\alpha \oplus \mathrm{Bool}$, that is, the element
$\mathrm{inl}\, A$ of $\mathbb{N} \oplus (\alpha \oplus \mathrm{Bool})$. -/
def uNt (A : ℕ) : ℕ ⊕ (α ⊕ Bool) := .inl A

/-- **Encoded letter terminal.** For a letter $a \in \alpha$, the terminal $a$ of the alphabet
$\alpha \oplus \mathrm{Bool}$ as a symbol of an encoded grammar, that is, the element
$\mathrm{inr}(\mathrm{inl}\, a)$ of $\mathbb{N} \oplus (\alpha \oplus \mathrm{Bool})$. -/
def uLetter (a : α) : ℕ ⊕ (α ⊕ Bool) := .inr (.inl a)

/-- **Encoded bit terminal.** For a type $\alpha$ and a bit $b$, the terminal $b$ of the alphabet
$\alpha \oplus \mathrm{Bool}$ as a symbol of an encoded grammar, that is, the element
$\mathrm{inr}(\mathrm{inr}\, b)$ of $\mathbb{N} \oplus (\alpha \oplus \mathrm{Bool})$. -/
def uBit (b : Bool) : ℕ ⊕ (α ⊕ Bool) := .inr (.inr b)

section Rules

variable [Fintype α] [DecidableEq α]

/-- **List of all letters.** For a finite alphabet $\alpha$, the list of all letters of $\alpha$,
each appearing exactly once, in some fixed but unspecified order. -/
noncomputable def allLetters : List α := Finset.univ.toList

/-- **The letters other than a given letter.** For a letter $a$ of a finite alphabet with decidable
equality, the list of all letters $b$ of the alphabet with $b \ne a$, in the order of a fixed
enumeration of the alphabet. -/
noncomputable def others (a : α) : List α := allLetters.filter fun b ↦ b ≠ a

/-- **Domino-independent productions of the universality grammar.** For a finite alphabet
$\alpha$ and $k \in \mathbb{N}$, this is a list of productions whose nonterminals $N_0, N_1, \dots$
are encoded as natural numbers and whose terminals are the letters $a \in \alpha$ and the two bits
$\mathbf{t}$ (true) and $\mathbf{f}$ (false). Writing $c(i) = \mathbf{t}\,\mathbf{f}^i$ for the
unary code of an index $i$, the list consists of the productions $N_3 \to \varepsilon$,
$N_5 \to \varepsilon$, $N_6 \to \varepsilon$, $N_7 \to \varepsilon$; $N_5 \to \mathbf{t}\,N_5$,
$N_5 \to \mathbf{f}\,N_5$, $N_6 \to \mathbf{t}\,N_6$, $N_6 \to \mathbf{f}\,N_6$;
$N_0 \to N_3$, $N_0 \to N_3\,\mathbf{f}\,N_5$, $N_0 \to N_6\,c(k)\,N_6$, $N_0 \to N_1$,
$N_0 \to N_2$; for each letter $a \in \alpha$, the productions $N_3 \to a\,N_3$,
$N_4 \to a\,N_3$, $N_6 \to a\,N_6$, $N_0 \to N_6\,\mathbf{t}\,a\,N_6$ and
$N_0 \to N_6\,\mathbf{f}\,a\,N_6$; and for each $i < k$, the production $N_7 \to c(i)\,N_7$.

The nonterminal $N_0$ is the start symbol. The intended languages are: for $N_3$ the words of
letters, for $N_4$ the nonempty words of letters, for $N_5$ the words of bits, for $N_6$ all
words, and for $N_7$ the concatenated codes of indices below $k$. The start productions (those
with left side $N_0$) generate the malformed words and the two mismatch nonterminals $N_1$ and
$N_2$. -/
noncomputable def baseRules (k : ℕ) : List (ℕ × List (ℕ ⊕ (α ⊕ Bool))) :=
  [(3, []), (5, []), (6, []), (7, []),
    (5, [uBit true, uNt 5]), (5, [uBit false, uNt 5]),
    (6, [uBit true, uNt 6]), (6, [uBit false, uNt 6]),
    (0, [uNt 3]), (0, [uNt 3, uBit false, uNt 5]), (0, uNt 6 :: (bitCode k).map uBit ++ [uNt 6]),
    (0, [uNt 1]), (0, [uNt 2])] ++
  allLetters.flatMap (fun a ↦ [(3, [uLetter a, uNt 3]), (4, [uLetter a, uNt 3]),
    (6, [uLetter a, uNt 6]), (0, [uNt 6, uBit true, uLetter a, uNt 6]),
    (0, [uNt 6, uBit false, uLetter a, uNt 6])]) ++
  (List.range k).map fun i ↦ (7, (bitCode i).map uBit ++ [uNt 7])

/-- **The mismatch productions** of a nonterminal $A$ for one side of a list $P$ of dominoes over a
finite alphabet. Let $s$ be a map from dominoes to words (in use, the top or the bottom). For each
index $i < |P|$ write $w = s(d_i)$ for the $i$-th domino $d_i$ of $P$ and $\mathrm{code}(i)$ for
the unary code of $i$ as bits. With letters and bits as terminals and $N_3$, $N_4$, $N_7$ the
nonterminals $3$, $4$, $7$ (meant to generate words of letters, nonempty words of letters and
codes of indices), the productions are $A \to w\,A\,\mathrm{code}(i)$ and
$A \to w\,N_4\,\mathrm{code}(i)$, which peel $w$ off, and, for each proper prefix $u$ of $w$,
$A \to u\,N_7\,\mathrm{code}(i)$ and $A \to u\,a\,N_3\,N_7\,\mathrm{code}(i)$ for every letter $a$
other than the letter of $w$ following $u$, which stop matching. -/
noncomputable def mismatchRules (side : Domino α → List α) (A : ℕ) (P : List (Domino α)) :
    List (ℕ × List (ℕ ⊕ (α ⊕ Bool))) :=
  (List.range P.length).flatMap fun i ↦
    (A, (side (domino P i)).map uLetter ++ uNt A :: (bitCode i).map uBit) ::
    (A, (side (domino P i)).map uLetter ++ uNt 4 :: (bitCode i).map uBit) ::
    (List.range (side (domino P i)).length).flatMap fun m ↦
      (A, ((side (domino P i)).take m).map uLetter ++ uNt 7 :: (bitCode i).map uBit) ::
      (((side (domino P i)).drop m).take 1).flatMap fun c ↦ (others c).map fun a ↦
        (A, ((side (domino P i)).take m).map uLetter ++
          uLetter a :: uNt 3 :: uNt 7 :: (bitCode i).map uBit)

/-- **The universality grammar.** For a finite alphabet $\alpha$ with decidable equality and a list
$P$ of dominoes over $\alpha$, the encoded context-free grammar over $\alpha \oplus \mathrm{Bool}$
with start nonterminal $0$ whose productions are the base productions for $k = |P|$, followed by
the mismatch productions of the top words of $P$ with nonterminal $1$, followed by the mismatch
productions of the bottom words of $P$ with nonterminal $2$.

Its language is the union of the complements of the top and bottom list languages of $P$. -/
noncomputable def univGrammar (P : List (Domino α)) : EncodedCFG (α ⊕ Bool) :=
  ⟨0, baseRules P.length ++ mismatchRules Prod.fst 1 P ++ mismatchRules Prod.snd 2 P⟩

theorem mem_others {a b : α} : b ∈ others a ↔ b ≠ a := by
  simp [others, allLetters]

end Rules

@[simp]
theorem decodeSymbol_uNt (A : ℕ) :
    EncodedCFG.decodeSymbol (uNt A : ℕ ⊕ (α ⊕ Bool)) = Symbol.nonterminal A := rfl

@[simp]
theorem decodeSymbol_uLetter (a : α) :
    EncodedCFG.decodeSymbol (uLetter a : ℕ ⊕ (α ⊕ Bool)) = Symbol.terminal (Sum.inl a) := rfl

@[simp]
theorem decodeSymbol_uBit (b : Bool) :
    EncodedCFG.decodeSymbol (uBit b : ℕ ⊕ (α ⊕ Bool)) = Symbol.terminal (Sum.inr b) := rfl

theorem map_decodeSymbol_uLetter (x : List α) :
    (x.map uLetter).map EncodedCFG.decodeSymbol =
      (x.map Sum.inl).map (Symbol.terminal (N := ℕ)) := by
  simp [Function.comp_def]

theorem map_decodeSymbol_uBit (y : List Bool) :
    (y.map (uBit (α := α))).map EncodedCFG.decodeSymbol =
      (y.map Sum.inr).map (Symbol.terminal (N := ℕ)) := by
  simp [Function.comp_def]

/-! ### The languages of the nonterminals -/

/-- **Words of letters.** For an alphabet $\alpha$, the language of words of letters is the set of
all words over $\alpha \oplus \mathrm{Bool}$ whose symbols all lie in $\alpha$, that is, the words
over $\alpha$ (including the empty word) viewed as words over $\alpha \oplus \mathrm{Bool}$. -/
def lettersLang : Language (α ⊕ Bool) := {w | ∃ x : List α, w = x.map Sum.inl}

/-- **Nonempty words of letters.** For an alphabet $\alpha$, the language of nonempty words of
letters is the set of all nonempty words over $\alpha \oplus \mathrm{Bool}$ whose symbols all lie
in $\alpha$, that is, the nonempty words over $\alpha$ viewed as words over
$\alpha \oplus \mathrm{Bool}$. -/
def letters1Lang : Language (α ⊕ Bool) := {w | ∃ x : List α, x ≠ [] ∧ w = x.map Sum.inl}

/-- **Words of bits.** For an alphabet $\alpha$, the language over the disjoint union of $\alpha$
and the bits $\{\mathbf{t}, \mathbf{f}\}$ consisting of the words in which every symbol is a bit,
including the empty word. -/
def bitsLang : Language (α ⊕ Bool) := {w | ∃ y : List Bool, w = y.map Sum.inr}

/-- **Codes of index sequences below $k$.** For an alphabet $\alpha$ and $k \in \mathbb{N}$, the
language over the disjoint union of $\alpha$ and the bits $\{\mathbf{t}, \mathbf{f}\}$ consisting of
the bit words $c(j_1) \cdots c(j_n)$ with $n \ge 0$ and $j_1, \dots, j_n < k$, where
$c(j) = \mathbf{t}\,\mathbf{f}^j$ is the unary code of $j$. In particular it contains the empty
word. -/
def codesLang (k : ℕ) : Language (α ⊕ Bool) :=
  {w | ∃ J : List ℕ, (∀ j ∈ J, j < k) ∧ w = (bitCodes J).map Sum.inr}

/-- **The mismatch language** of one side of a list $P$ of dominoes. Let $s$ be a map from dominoes
to words (in use, the top or the bottom), write $w_i = s(d_i)$ for the $i$-th domino $d_i$ of $P$
and $\mathrm{code}(i)$ for the unary code of $i$ as bits. The language, over letters and bits,
consists of the words $x\,\mathrm{code}(i_n) \cdots \mathrm{code}(i_1)$ where $x$ is a word of
letters and $i_1, \dots, i_n$ with $n \ge 1$ are indices below $|P|$ such that
$x \ne w_{i_1} \cdots w_{i_n}$. -/
def mismatchLang (side : Domino α → List α) (P : List (Domino α)) : Language (α ⊕ Bool) :=
  {w | ∃ (x : List α) (I : List ℕ), I ≠ [] ∧ (∀ i ∈ I, i < P.length) ∧ x ≠ flat side P I ∧
    w = x.map Sum.inl ++ (bitCodes I.reverse).map Sum.inr}

/-- **Malformed words.** Consider words over $\alpha \oplus \mathrm{Bool}$, whose symbols are
letters from $\alpha$ and bits, and read the bit $\mathrm{true}$ as the separator $|$ and the bit
$\mathrm{false}$ as $1$. For $k \in \mathbb{N}$, a word is malformed with bound $k$ when at least
one of the following holds: it consists of letters only (possibly none); it is a word of letters
followed by a nonempty word of bits whose first bit is $1$; some bit is immediately followed by a
letter; or it contains the block $|\,1^k$ (the bit $|$ followed by $k$ bits $1$) as a contiguous
factor. -/
def malformedLang (k : ℕ) : Language (α ⊕ Bool) :=
  {w | (∃ x : List α, w = x.map Sum.inl) ∨
    (∃ (x : List α) (y : List Bool), w = x.map Sum.inl ++ Sum.inr false :: y.map Sum.inr) ∨
    (∃ (u v : List (α ⊕ Bool)) (b : Bool) (a : α), w = u ++ Sum.inr b :: Sum.inl a :: v) ∨
    (∃ u v : List (α ⊕ Bool), w = u ++ (bitCode k).map Sum.inr ++ v)}

/-- **Intended languages of the nonterminals of the universality grammar.** For a list $P$ of
dominoes over $\alpha$, the assignment of a language over $\alpha \oplus \mathrm{Bool}$ to each
natural number that sends $0$ to the union of the malformed language for $k = |P|$ and the
mismatch languages of the top words and of the bottom words of $P$; $1$ to the mismatch language
of the top words of $P$; $2$ to the mismatch language of the bottom words of $P$; $3$ to the words
of letters; $4$ to the nonempty words of letters; $5$ to the words of bits; $6$ to the set of all
words; $7$ to the codes of index sequences with all indices below $|P|$; and every other number
to the empty language. -/
def univVal (P : List (Domino α)) : ℕ → Language (α ⊕ Bool)
  | 0 => {w | w ∈ malformedLang P.length ∨ w ∈ mismatchLang Prod.fst P ∨
      w ∈ mismatchLang Prod.snd P}
  | 1 => mismatchLang Prod.fst P
  | 2 => mismatchLang Prod.snd P
  | 3 => lettersLang
  | 4 => letters1Lang
  | 5 => bitsLang
  | 6 => {_w | True}
  | 7 => codesLang P.length
  | _ => {_w | False}

theorem mem_singleton_mul {T : Type*} {u w : List T} {L : Language T} :
    w ∈ ({u} : Language T) * L ↔ ∃ z ∈ L, w = u ++ z := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨a, rfl, z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨u, rfl, z, hz, rfl⟩

theorem mem_mul_eq {T : Type*} {w : List T} {L M : Language T} :
    w ∈ L * M ↔ ∃ a ∈ L, ∃ b ∈ M, w = a ++ b := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem mem_singleton_lang {T : Type*} {u w : List T} : w ∈ ({u} : Language T) ↔ w = u :=
  Iff.rfl

/-- **Evaluating a form with one nonterminal.** Let $V$ assign a language over $T$ to each
nonterminal. For terminal words $u$ and $v$, a nonterminal $A$ and a word $w$, the word $w$ lies
in the language that $V$ assigns to the sentential form $u\,A\,v$ if and only if $w = u z v$ for
some $z \in V(A)$. -/
theorem mem_evalForm_one {T N : Type*} {V : N → Language T} {u v w : List T} {A : N} :
    w ∈ evalForm V (u.map Symbol.terminal ++ Symbol.nonterminal A :: v.map Symbol.terminal) ↔
      ∃ z ∈ V A, w = u ++ z ++ v := by
  simp only [evalForm_append, evalForm_cons, evalSymbol_nonterminal, evalForm_map_terminal,
    mem_mul_eq, mem_singleton_lang, exists_eq_left]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, by simp⟩

/-- **Evaluating a form with two nonterminals.** Let $V$ assign a language over $T$ to each
nonterminal. For terminal words $u$, $v$ and $x$, nonterminals $A$ and $B$ and a word $w$, the
word $w$ lies in the language that $V$ assigns to the sentential form $u\,A\,v\,B\,x$ if and
only if $w = u z_1 v z_2 x$ for some $z_1 \in V(A)$ and $z_2 \in V(B)$. -/
theorem mem_evalForm_two {T N : Type*} {V : N → Language T} {u v x w : List T} {A B : N} :
    w ∈ evalForm V (u.map Symbol.terminal ++ Symbol.nonterminal A ::
      (v.map Symbol.terminal ++ Symbol.nonterminal B :: x.map Symbol.terminal)) ↔
      ∃ z₁ ∈ V A, ∃ z₂ ∈ V B, w = u ++ z₁ ++ v ++ z₂ ++ x := by
  simp only [evalForm_append, evalForm_cons, evalSymbol_nonterminal, evalForm_map_terminal,
    mem_mul_eq, mem_singleton_lang, exists_eq_left]
  constructor
  · rintro ⟨_, ⟨z₁, hz₁, _, ⟨_, ⟨z₂, hz₂, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨z₁, hz₁, z₂, hz₂, by simp⟩
  · rintro ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    exact ⟨_, ⟨z₁, hz₁, _, ⟨_, ⟨z₂, hz₂, rfl⟩, rfl⟩, rfl⟩, by simp⟩

/-! ### Upper bounds: every production is sound for `univVal` -/

section Sound

variable [Fintype α] [DecidableEq α] {P : List (Domino α)}

omit [Fintype α] [DecidableEq α] in
theorem mem_univVal_zero {w : List (α ⊕ Bool)} :
    w ∈ univVal P 0 ↔ w ∈ malformedLang P.length ∨ w ∈ mismatchLang Prod.fst P ∨
      w ∈ mismatchLang Prod.snd P :=
  Iff.rfl

theorem bitCodes_reverse_cons (i : ℕ) (I : List ℕ) :
    bitCodes (i :: I).reverse = bitCodes I.reverse ++ bitCode i := by
  simp [bitCodes]

omit [DecidableEq α] in
theorem baseRules_sound {e : ℕ × List (ℕ ⊕ (α ⊕ Bool))} (he : e ∈ baseRules P.length) :
    evalForm (univVal P) (EncodedCFG.decodeRule e).output ≤ univVal P e.1 := by
  simp only [baseRules, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at he
  rcases he with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    ⟨a, -, rfl | rfl | rfl | rfl | rfl⟩) | ⟨i, hi, rfl⟩ <;> intro w hw
  · -- `3 → ε`
    obtain rfl : w = [] := hw
    exact ⟨[], rfl⟩
  · obtain rfl : w = [] := hw
    exact ⟨[], rfl⟩
  · trivial
  · obtain rfl : w = [] := hw
    exact ⟨[], by simp, rfl⟩
  · -- `5 → 1 5`
    change w ∈ evalForm _ ([Sum.inr true].map Symbol.terminal ++ Symbol.nonterminal 5 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal) at hw
    obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := mem_evalForm_one.mp hw
    exact ⟨true :: y, by simp⟩
  · change w ∈ evalForm _ ([Sum.inr false].map Symbol.terminal ++ Symbol.nonterminal 5 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal) at hw
    obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := mem_evalForm_one.mp hw
    exact ⟨false :: y, by simp⟩
  · trivial
  · trivial
  · -- `0 → 3`: no bits
    change w ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 3 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal) at hw
    obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := mem_evalForm_one.mp hw
    exact Or.inl (Or.inl ⟨x, by simp⟩)
  · -- `0 → 3 1 5`: the bits start with a `1`
    change w ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 3 ::
      ([Sum.inr false].map Symbol.terminal ++ Symbol.nonterminal 5 ::
        ([] : List (α ⊕ Bool)).map Symbol.terminal)) at hw
    obtain ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩ := mem_evalForm_two.mp hw
    exact Or.inl (Or.inr (Or.inl ⟨x, y, by simp⟩))
  · -- `0 → 6 code(k) 6`: a code with at least `k` ones
    simp only [EncodedCFG.decodeRule, List.map_cons, List.map_append, decodeSymbol_uNt,
      map_decodeSymbol_uBit, List.map_nil] at hw
    change w ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 6 ::
      (((bitCode P.length).map Sum.inr).map Symbol.terminal ++ Symbol.nonterminal 6 ::
        ([] : List (α ⊕ Bool)).map Symbol.terminal)) at hw
    obtain ⟨u, -, v, -, rfl⟩ := mem_evalForm_two.mp hw
    exact Or.inl (Or.inr (Or.inr (Or.inr ⟨u, v, by simp⟩)))
  · change w ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 1 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal) at hw
    obtain ⟨_, h, rfl⟩ := mem_evalForm_one.mp hw
    rw [List.nil_append, List.append_nil]
    exact Or.inr (Or.inl h)
  · change w ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 2 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal) at hw
    obtain ⟨_, h, rfl⟩ := mem_evalForm_one.mp hw
    rw [List.nil_append, List.append_nil]
    exact Or.inr (Or.inr h)
  · -- `3 → a 3`
    change w ∈ evalForm _ ([Sum.inl a].map Symbol.terminal ++ Symbol.nonterminal 3 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal) at hw
    obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := mem_evalForm_one.mp hw
    exact ⟨a :: x, by simp⟩
  · -- `4 → a 3`
    change w ∈ evalForm _ ([Sum.inl a].map Symbol.terminal ++ Symbol.nonterminal 3 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal) at hw
    obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := mem_evalForm_one.mp hw
    exact ⟨a :: x, List.cons_ne_nil _ _, by simp⟩
  · trivial
  · -- `0 → 6 | a 6`: a bit followed by a letter
    change w ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 6 ::
      ([Sum.inr true, Sum.inl a].map Symbol.terminal ++ Symbol.nonterminal 6 ::
        ([] : List (α ⊕ Bool)).map Symbol.terminal)) at hw
    obtain ⟨u, -, v, -, rfl⟩ := mem_evalForm_two.mp hw
    exact Or.inl (Or.inr (Or.inr (Or.inl ⟨u, v, true, a, by simp⟩)))
  · change w ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 6 ::
      ([Sum.inr false, Sum.inl a].map Symbol.terminal ++ Symbol.nonterminal 6 ::
        ([] : List (α ⊕ Bool)).map Symbol.terminal)) at hw
    obtain ⟨u, -, v, -, rfl⟩ := mem_evalForm_two.mp hw
    exact Or.inl (Or.inr (Or.inr (Or.inl ⟨u, v, false, a, by simp⟩)))
  · -- `7 → code(i) 7`
    simp only [EncodedCFG.decodeRule, List.map_append, map_decodeSymbol_uBit, List.map_cons,
      decodeSymbol_uNt, List.map_nil] at hw
    change w ∈ evalForm _ (((bitCode i).map Sum.inr).map Symbol.terminal ++
      Symbol.nonterminal 7 :: ([] : List (α ⊕ Bool)).map Symbol.terminal) at hw
    obtain ⟨_, ⟨J, hJ, rfl⟩, rfl⟩ := mem_evalForm_one.mp hw
    refine ⟨i :: J, ?_, by simp [bitCodes]⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact hJ j hj

theorem mismatchRules_sound {side : Domino α → List α} {A : ℕ}
    (hA : univVal P A = mismatchLang side P) {e : ℕ × List (ℕ ⊕ (α ⊕ Bool))}
    (he : e ∈ mismatchRules side A P) :
    evalForm (univVal P) (EncodedCFG.decodeRule e).output ≤ univVal P e.1 := by
  simp only [mismatchRules, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map] at he
  obtain ⟨i, hi, rfl | rfl | ⟨m, hm, rfl | ⟨c, hc, a, ha, rfl⟩⟩⟩ := he <;> intro w hw <;>
    rw [hA]
  · -- `A → wᵢ A code(i)`
    simp only [EncodedCFG.decodeRule, List.map_append, map_decodeSymbol_uLetter, List.map_cons,
      decodeSymbol_uNt, map_decodeSymbol_uBit] at hw
    obtain ⟨_, hz, rfl⟩ := mem_evalForm_one.mp hw
    rw [hA] at hz
    obtain ⟨x, I, hne, hlt, hx, rfl⟩ := hz
    refine ⟨side (domino P i) ++ x, i :: I, List.cons_ne_nil _ _, ?_, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hlt j hj
    · intro h
      exact hx (List.append_cancel_left (h.trans (by simp [flat])))
    · rw [bitCodes_reverse_cons]
      simp
  · -- `A → wᵢ L⁺ code(i)`
    simp only [EncodedCFG.decodeRule, List.map_append, map_decodeSymbol_uLetter, List.map_cons,
      decodeSymbol_uNt, map_decodeSymbol_uBit] at hw
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := mem_evalForm_one.mp hw
    refine ⟨side (domino P i) ++ y, [i], List.cons_ne_nil _ _, by simpa using hi, ?_, ?_⟩
    · intro h
      exact hy (by simpa [flat] using h)
    · simp [bitCodes]
  · -- `A → u codes code(i)`, `u` a proper prefix of `wᵢ`
    simp only [EncodedCFG.decodeRule, List.map_append, map_decodeSymbol_uLetter, List.map_cons,
      decodeSymbol_uNt, map_decodeSymbol_uBit] at hw
    obtain ⟨_, ⟨J, hJ, rfl⟩, rfl⟩ := mem_evalForm_one.mp hw
    refine ⟨(side (domino P i)).take m, i :: J.reverse, List.cons_ne_nil _ _, ?_, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hJ j (List.mem_reverse.mp hj)
    · intro h
      have := congrArg List.length h
      simp only [flat, List.flatMap_cons, List.length_append, List.length_take] at this
      omega
    · rw [bitCodes_reverse_cons]
      simp
  · -- `A → u a L* codes code(i)`, where `a` is not the next letter of `wᵢ`
    obtain ⟨rest, hrest⟩ : ∃ rest, (side (domino P i)).drop m = c :: rest := by
      cases h : (side (domino P i)).drop m with
      | nil => simp [h] at hc
      | cons d rest =>
        rw [h] at hc
        simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hc
        exact ⟨rest, by rw [hc]⟩
    have e : ((List.take m (side (domino P i))).map uLetter ++ uLetter a :: uNt 3 :: uNt 7 ::
        (bitCode i).map uBit).map EncodedCFG.decodeSymbol =
        ((List.take m (side (domino P i)) ++ [a]).map Sum.inl).map Symbol.terminal ++
          Symbol.nonterminal 3 :: (([] : List (α ⊕ Bool)).map Symbol.terminal ++
            Symbol.nonterminal 7 :: ((bitCode i).map Sum.inr).map Symbol.terminal) := by
      simp [Function.comp_def]
    change w ∈ evalForm _ (List.map _ _) at hw
    rw [e] at hw
    obtain ⟨_, ⟨y, rfl⟩, _, ⟨J, hJ, rfl⟩, rfl⟩ := mem_evalForm_two.mp hw
    refine ⟨(side (domino P i)).take m ++ a :: y, i :: J.reverse, List.cons_ne_nil _ _, ?_, ?_,
      ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hJ j (List.mem_reverse.mp hj)
    · intro h
      simp only [flat, List.flatMap_cons] at h
      have hlen : (List.take m (side (domino P i))).length = m := by
        rw [List.length_take]
        omega
      have := congrArg (List.drop m) h
      rw [List.drop_left' hlen, List.drop_append_of_le_length (by omega), hrest] at this
      simp only [List.cons_append, List.cons.injEq] at this
      exact (mem_others.mp ha) this.1
    · rw [bitCodes_reverse_cons]
      simp

/-- **The intended languages form a valuation of the universality grammar.** Let $\alpha$ be a
finite alphabet with decidable equality and let $P$ be a list of dominoes over $\alpha$. The
assignment of intended languages to the nonterminals of the universality grammar of $P$ is a
valuation of that grammar: for every production $A \to \gamma$, the language that $\gamma$ denotes
under the assignment is contained in the language assigned to $A$. -/
theorem isValuation_univVal (P : List (Domino α)) :
    IsValuation (univGrammar P).toCFG (univVal P) := by
  intro r hr
  obtain ⟨e, he, rfl⟩ := EncodedCFG.mem_toCFG_rules.mp hr
  simp only [univGrammar, List.mem_append] at he
  rcases he with (he | he) | he
  · exact baseRules_sound he
  · exact mismatchRules_sound rfl he
  · exact mismatchRules_sound rfl he

end Sound

/-! ### Lower bounds: the intended words are derivable -/

/-- **A word that does not start with $w$ leaves $w$ at some position.**
Let $w$ and $x$ be words over an alphabet $\alpha$ such that $w$ is not a prefix of $x$. Then
there is a position $m < |w|$ with the following property: writing $w = u\,c\,r$ with $|u| = m$
and $c \in \alpha$, either $x = u$, or $x = u\,a\,y$ for some letter $a \ne c$ and some word $y$. -/
theorem exists_mismatch_of_not_prefix {w x : List α} (h : ¬w <+: x) :
    ∃ m < w.length, ∃ c rest, w.drop m = c :: rest ∧
      (x = w.take m ∨ ∃ a y, a ≠ c ∧ x = w.take m ++ a :: y) := by
  induction w generalizing x with
  | nil => exact absurd (List.nil_prefix) h
  | cons c w ih =>
    cases x with
    | nil => exact ⟨0, by simp, c, w, rfl, Or.inl rfl⟩
    | cons d x =>
      by_cases hdc : d = c
      · subst hdc
        have h' : ¬w <+: x := fun hw ↦ h (List.cons_prefix_cons.mpr ⟨rfl, hw⟩)
        obtain ⟨m, hm, c', rest, hdrop, hx⟩ := ih h'
        refine ⟨m + 1, by simpa using hm, c', rest, by simpa using hdrop, ?_⟩
        rcases hx with rfl | ⟨a, y, ha, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨a, y, ha, rfl⟩
      · exact ⟨0, by simp, c, w, rfl, Or.inr ⟨d, x, hdc, rfl⟩⟩

section Complete

variable [Fintype α] [DecidableEq α] {P : List (Domino α)}

theorem mem_languageFrom_of_rule {e : ℕ × List (ℕ ⊕ (α ⊕ Bool))} (he : e ∈ (univGrammar P).rules)
    {w : List (α ⊕ Bool)}
    (hw : w ∈ evalForm (languageFrom (univGrammar P).toCFG) (EncodedCFG.decodeRule e).output) :
    w ∈ languageFrom (univGrammar P).toCFG e.1 :=
  isValuation_languageFrom _ (EncodedCFG.mem_toCFG_rules.mpr ⟨e, he, rfl⟩) hw

theorem mem_rules_of_mem_baseRules {e : ℕ × List (ℕ ⊕ (α ⊕ Bool))}
    (he : e ∈ baseRules P.length) : e ∈ (univGrammar P).rules := by
  simp [univGrammar, he]

omit [DecidableEq α] in
theorem mem_baseRules_letter (k : ℕ) (a : α) {e : ℕ × List (ℕ ⊕ (α ⊕ Bool))}
    (he : e ∈ [(3, [uLetter a, uNt 3]), (4, [uLetter a, uNt 3]), (6, [uLetter a, uNt 6]),
      (0, [uNt 6, uBit true, uLetter a, uNt 6]), (0, [uNt 6, uBit false, uLetter a, uNt 6])]) :
    e ∈ baseRules (α := α) k := by
  simp only [baseRules, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨a, by simp [allLetters], he⟩)

theorem letters_mem (x : List α) :
    x.map Sum.inl ∈ languageFrom (univGrammar P).toCFG 3 := by
  induction x with
  | nil =>
    exact mem_languageFrom_of_rule (e := (3, [])) (mem_rules_of_mem_baseRules (by simp [baseRules]))
      (by simp [EncodedCFG.decodeRule])
  | cons a x ih =>
    refine mem_languageFrom_of_rule (e := (3, [uLetter a, uNt 3]))
      (mem_rules_of_mem_baseRules (mem_baseRules_letter _ a (by simp))) ?_
    change _ ∈ evalForm _ ([Sum.inl a].map Symbol.terminal ++ Symbol.nonterminal 3 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal)
    exact mem_evalForm_one.mpr ⟨_, ih, by simp⟩

theorem letters1_mem {x : List α} (hx : x ≠ []) :
    x.map Sum.inl ∈ languageFrom (univGrammar P).toCFG 4 := by
  obtain ⟨a, x, rfl⟩ := List.exists_cons_of_ne_nil hx
  refine mem_languageFrom_of_rule (e := (4, [uLetter a, uNt 3]))
    (mem_rules_of_mem_baseRules (mem_baseRules_letter _ a (by simp))) ?_
  change _ ∈ evalForm _ ([Sum.inl a].map Symbol.terminal ++ Symbol.nonterminal 3 ::
    ([] : List (α ⊕ Bool)).map Symbol.terminal)
  exact mem_evalForm_one.mpr ⟨_, letters_mem x, by simp⟩

theorem bits_mem (y : List Bool) :
    y.map Sum.inr ∈ languageFrom (univGrammar P).toCFG (5 : ℕ) := by
  induction y with
  | nil =>
    exact mem_languageFrom_of_rule (e := (5, [])) (mem_rules_of_mem_baseRules (by simp [baseRules]))
      (by simp [EncodedCFG.decodeRule])
  | cons b y ih =>
    refine mem_languageFrom_of_rule (e := (5, [uBit b, uNt 5]))
      (mem_rules_of_mem_baseRules (by cases b <;> simp [baseRules])) ?_
    change _ ∈ evalForm _ ([Sum.inr b].map Symbol.terminal ++ Symbol.nonterminal 5 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal)
    exact mem_evalForm_one.mpr ⟨_, ih, by simp⟩

theorem any_mem (w : List (α ⊕ Bool)) : w ∈ languageFrom (univGrammar P).toCFG (6 : ℕ) := by
  induction w with
  | nil =>
    exact mem_languageFrom_of_rule (e := (6, [])) (mem_rules_of_mem_baseRules (by simp [baseRules]))
      (by simp [EncodedCFG.decodeRule])
  | cons s w ih =>
    rcases s with a | b
    · refine mem_languageFrom_of_rule (e := (6, [uLetter a, uNt 6]))
        (mem_rules_of_mem_baseRules (mem_baseRules_letter _ a (by simp))) ?_
      change _ ∈ evalForm _ ([Sum.inl a].map Symbol.terminal ++ Symbol.nonterminal 6 ::
        ([] : List (α ⊕ Bool)).map Symbol.terminal)
      exact mem_evalForm_one.mpr ⟨_, ih, by simp⟩
    · refine mem_languageFrom_of_rule (e := (6, [uBit b, uNt 6]))
        (mem_rules_of_mem_baseRules (by cases b <;> simp [baseRules])) ?_
      change _ ∈ evalForm _ ([Sum.inr b].map Symbol.terminal ++ Symbol.nonterminal 6 ::
        ([] : List (α ⊕ Bool)).map Symbol.terminal)
      exact mem_evalForm_one.mpr ⟨_, ih, by simp⟩

theorem codes_mem {J : List ℕ} (hJ : ∀ j ∈ J, j < P.length) :
    (bitCodes J).map Sum.inr ∈ languageFrom (univGrammar P).toCFG (7 : ℕ) := by
  induction J with
  | nil =>
    exact mem_languageFrom_of_rule (e := (7, [])) (mem_rules_of_mem_baseRules (by simp [baseRules]))
      (by simp [EncodedCFG.decodeRule])
  | cons j J ih =>
    have hj : j < P.length := hJ j List.mem_cons_self
    refine mem_languageFrom_of_rule (e := (7, (bitCode j).map uBit ++ [uNt 7]))
      (mem_rules_of_mem_baseRules ?_) ?_
    · simp only [baseRules, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨j, hj, rfl⟩
    · simp only [EncodedCFG.decodeRule, List.map_append, map_decodeSymbol_uBit, List.map_cons,
        decodeSymbol_uNt, List.map_nil]
      change _ ∈ evalForm _ (((bitCode j).map Sum.inr).map Symbol.terminal ++
        Symbol.nonterminal 7 :: ([] : List (α ⊕ Bool)).map Symbol.terminal)
      exact mem_evalForm_one.mpr ⟨_, ih fun k hk ↦ hJ k (List.mem_cons_of_mem _ hk),
        by simp [bitCodes]⟩

/-- **Membership in the mismatch productions.** Let $P$ be a list of dominoes over a finite
alphabet with decidable equality, $A$ a nonterminal, $s$ a map from dominoes to words (in use, the
top or the bottom), $i < |P|$ an index, $w = s(d_i)$ for the $i$-th domino $d_i$ of $P$, and
$\mathrm{code}(i)$ the unary code of $i$ as bits. Write letters and bits as terminals and $N_3$,
$N_4$, $N_7$ for the nonterminals $3$, $4$ and $7$. Each of the following encoded productions
belongs to the mismatch productions of $A$ for $s$ and $P$: $A \to w\,A\,\mathrm{code}(i)$;
$A \to w\,N_4\,\mathrm{code}(i)$; for each $m < |w|$, with $u$ the prefix of $w$ of length $m$,
$A \to u\,N_7\,\mathrm{code}(i)$; and, for each such $m$ and each letter $a$ different from the
letter of $w$ following $u$, $A \to u\,a\,N_3\,N_7\,\mathrm{code}(i)$. -/
theorem mem_mismatchRules {side : Domino α → List α} {A i : ℕ} (hi : i < P.length)
    {e : ℕ × List (ℕ ⊕ (α ⊕ Bool))}
    (he : e = (A, (side (domino P i)).map uLetter ++ uNt A :: (bitCode i).map uBit) ∨
      e = (A, (side (domino P i)).map uLetter ++ uNt 4 :: (bitCode i).map uBit) ∨
      (∃ m < (side (domino P i)).length,
        e = (A, ((side (domino P i)).take m).map uLetter ++ uNt 7 :: (bitCode i).map uBit) ∨
        ∃ c ∈ ((side (domino P i)).drop m).take 1, ∃ a ∈ others c,
          e = (A, ((side (domino P i)).take m).map uLetter ++
            uLetter a :: uNt 3 :: uNt 7 :: (bitCode i).map uBit))) :
    e ∈ mismatchRules side A P := by
  simp only [mismatchRules, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map]
  refine ⟨i, hi, ?_⟩
  rcases he with h | h | ⟨m, hm, h | ⟨c, hc, a, ha, h⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨m, hm, Or.inl h⟩)
  · exact Or.inr (Or.inr ⟨m, hm, Or.inr ⟨c, hc, a, ha, h.symm⟩⟩)

/-- **Every mismatched word is derivable from the mismatch nonterminal.** Let $P$ be a list of
dominoes over a finite alphabet, $s$ a map from dominoes to words (in use, the top or the bottom),
$w_i = s(d_i)$ for the $i$-th domino $d_i$ of $P$, and $\mathrm{code}(i)$ the unary code of $i$ as
bits. Let $A$ be a nonterminal such that every mismatch production of $A$ for $s$ and $P$ is a
production of the universality grammar of $P$. Then for every nonempty sequence
$i_1, \dots, i_n$ of indices below $|P|$ and every word $x$ of letters with
$x \ne w_{i_1} \cdots w_{i_n}$, the word $x\,\mathrm{code}(i_n) \cdots \mathrm{code}(i_1)$ is
derivable from $A$ in the universality grammar of $P$. -/
theorem mismatch_mem {side : Domino α → List α} {A : ℕ}
    (hrules : ∀ e ∈ mismatchRules side A P, e ∈ (univGrammar P).rules) :
    ∀ I : List ℕ, I ≠ [] → (∀ i ∈ I, i < P.length) → ∀ x : List α, x ≠ flat side P I →
      x.map Sum.inl ++ (bitCodes I.reverse).map Sum.inr ∈ languageFrom (univGrammar P).toCFG A
  | [], hne, _, _, _ => absurd rfl hne
  | i :: I, _, hlt, x, hx => by
    have hi : i < P.length := hlt i List.mem_cons_self
    have hlt' : ∀ j ∈ I, j < P.length := fun j hj ↦ hlt j (List.mem_cons_of_mem _ hj)
    rw [bitCodes_reverse_cons]
    by_cases hpre : side (domino P i) <+: x
    · obtain ⟨x', rfl⟩ := hpre
      rcases eq_or_ne I [] with rfl | hI
      · -- `A → wᵢ L⁺ code(i)`
        have hx' : x' ≠ [] := by
          rintro rfl
          exact hx (by simp [flat])
        refine mem_languageFrom_of_rule (hrules _ (mem_mismatchRules hi (Or.inr (Or.inl rfl)))) ?_
        simp only [EncodedCFG.decodeRule, List.map_append, map_decodeSymbol_uLetter,
          List.map_cons, decodeSymbol_uNt, map_decodeSymbol_uBit]
        exact mem_evalForm_one.mpr ⟨_, letters1_mem hx', by simp⟩
      · -- `A → wᵢ A code(i)`
        have hx' : x' ≠ flat side P I := fun h ↦ hx (by simp [flat, h])
        refine mem_languageFrom_of_rule (hrules _ (mem_mismatchRules hi (Or.inl rfl))) ?_
        simp only [EncodedCFG.decodeRule, List.map_append, map_decodeSymbol_uLetter,
          List.map_cons, decodeSymbol_uNt, map_decodeSymbol_uBit]
        exact mem_evalForm_one.mpr ⟨_, mismatch_mem hrules I hI hlt' x' hx', by simp⟩
    · obtain ⟨m, hm, c, rest, hdrop, rfl | ⟨a, y, ha, rfl⟩⟩ := exists_mismatch_of_not_prefix hpre
      · -- `A → u codes code(i)`
        refine mem_languageFrom_of_rule
          (hrules _ (mem_mismatchRules hi (Or.inr (Or.inr ⟨m, hm, Or.inl rfl⟩)))) ?_
        simp only [EncodedCFG.decodeRule, List.map_append, map_decodeSymbol_uLetter,
          List.map_cons, decodeSymbol_uNt, map_decodeSymbol_uBit]
        exact mem_evalForm_one.mpr ⟨_, codes_mem fun j hj ↦ hlt' j (List.mem_reverse.mp hj),
          by simp⟩
      · -- `A → u a L* codes code(i)`
        have hc : c ∈ ((side (domino P i)).drop m).take 1 := by simp [hdrop]
        refine mem_languageFrom_of_rule (hrules _ (mem_mismatchRules hi
          (Or.inr (Or.inr ⟨m, hm, Or.inr ⟨c, hc, a, mem_others.mpr ha, rfl⟩⟩)))) ?_
        have e : ((List.take m (side (domino P i))).map uLetter ++ uLetter a :: uNt 3 :: uNt 7 ::
            (bitCode i).map uBit).map EncodedCFG.decodeSymbol =
            ((List.take m (side (domino P i)) ++ [a]).map Sum.inl).map Symbol.terminal ++
              Symbol.nonterminal 3 :: (([] : List (α ⊕ Bool)).map Symbol.terminal ++
                Symbol.nonterminal 7 :: ((bitCode i).map Sum.inr).map Symbol.terminal) := by
          simp [Function.comp_def]
        change _ ∈ evalForm _ (List.map _ _)
        rw [e]
        exact mem_evalForm_two.mpr ⟨_, letters_mem y, _,
          codes_mem fun j hj ↦ hlt' j (List.mem_reverse.mp hj), by simp⟩

theorem univVal_zero_le {w : List (α ⊕ Bool)} (hw : w ∈ univVal P 0) :
    w ∈ languageFrom (univGrammar P).toCFG (0 : ℕ) := by
  rcases hw with (⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨u, v, b, a, rfl⟩ | ⟨u, v, rfl⟩) |
    ⟨x, I, hne, hlt, hx, rfl⟩ | ⟨x, I, hne, hlt, hx, rfl⟩
  · refine mem_languageFrom_of_rule (e := (0, [uNt 3]))
      (mem_rules_of_mem_baseRules (by simp [baseRules])) ?_
    change _ ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 3 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal)
    exact mem_evalForm_one.mpr ⟨_, letters_mem x, by simp⟩
  · refine mem_languageFrom_of_rule (e := (0, [uNt 3, uBit false, uNt 5]))
      (mem_rules_of_mem_baseRules (by simp [baseRules])) ?_
    change _ ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 3 ::
      ([Sum.inr false].map Symbol.terminal ++ Symbol.nonterminal 5 ::
        ([] : List (α ⊕ Bool)).map Symbol.terminal))
    exact mem_evalForm_two.mpr ⟨_, letters_mem x, _, bits_mem y, by simp⟩
  · refine mem_languageFrom_of_rule (e := (0, [uNt 6, uBit b, uLetter a, uNt 6]))
      (mem_rules_of_mem_baseRules (mem_baseRules_letter _ a (by cases b <;> simp))) ?_
    change _ ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 6 ::
      ([Sum.inr b, Sum.inl a].map Symbol.terminal ++ Symbol.nonterminal 6 ::
        ([] : List (α ⊕ Bool)).map Symbol.terminal))
    exact mem_evalForm_two.mpr ⟨_, any_mem u, _, any_mem v, by simp⟩
  · refine mem_languageFrom_of_rule (e := (0, uNt 6 :: (bitCode P.length).map uBit ++ [uNt 6]))
      (mem_rules_of_mem_baseRules (by simp [baseRules])) ?_
    simp only [EncodedCFG.decodeRule, List.map_cons, List.map_append, decodeSymbol_uNt,
      map_decodeSymbol_uBit, List.map_nil]
    change _ ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 6 ::
      (((bitCode P.length).map Sum.inr).map Symbol.terminal ++ Symbol.nonterminal 6 ::
        ([] : List (α ⊕ Bool)).map Symbol.terminal))
    exact mem_evalForm_two.mpr ⟨_, any_mem u, _, any_mem v, by simp⟩
  · refine mem_languageFrom_of_rule (e := (0, [uNt 1]))
      (mem_rules_of_mem_baseRules (by simp [baseRules])) ?_
    change _ ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 1 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal)
    refine mem_evalForm_one.mpr ⟨_, mismatch_mem (fun e he ↦ ?_) I hne hlt x hx, by simp⟩
    simp [univGrammar, he]
  · refine mem_languageFrom_of_rule (e := (0, [uNt 2]))
      (mem_rules_of_mem_baseRules (by simp [baseRules])) ?_
    change _ ∈ evalForm _ (([] : List (α ⊕ Bool)).map Symbol.terminal ++ Symbol.nonterminal 2 ::
      ([] : List (α ⊕ Bool)).map Symbol.terminal)
    refine mem_evalForm_one.mpr ⟨_, mismatch_mem (fun e he ↦ ?_) I hne hlt x hx, by simp⟩
    simp [univGrammar, he]

/-- **The language of the universality grammar.** Let $\alpha$ be a finite alphabet with decidable
equality, let $P$ be a list of dominoes over $\alpha$ of length $m$, and for $i < m$ let $t_i$ and
$b_i$ be the top and bottom words of the domino of $P$ at position $i$, counting from $0$. Read the
bit $\mathrm{true}$ as the separator $|$ and the bit $\mathrm{false}$ as $1$, and let $c(i)$ be the
unary code of $i$: the bit $|$ followed by $i$ bits $1$. The language of the universality grammar
of $P$ equals the intended language of its start nonterminal $0$: a word over
$\alpha \oplus \mathrm{Bool}$ belongs to it exactly when at least one of the following holds: it
consists of letters from $\alpha$ only (possibly none); it is a word of letters followed by a
nonempty word of bits whose first bit is $1$; some bit is immediately followed by a letter; it
contains $c(m)$ as a contiguous factor; or it equals $x\, c(i_n) \cdots c(i_1)$ for a word $x$
over $\alpha$ and indices $i_1, \dots, i_n < m$ with $n \ge 1$ such that
$x \ne t_{i_1} \cdots t_{i_n}$ or $x \ne b_{i_1} \cdots b_{i_n}$. -/
theorem language_univGrammar (P : List (Domino α)) :
    (univGrammar P).language = univVal P 0 :=
  le_antisymm (language_le_of_valuation (isValuation_univVal P)) fun _ hw ↦ univVal_zero_le hw

end Complete

/-! ### The language is the complement of the intersection of the list languages -/

section Complement

/-- **No right symbol directly precedes a left symbol in a left-then-right word.** Let $\alpha$
and $\beta$ be types and consider words over the disjoint union $\alpha \sqcup \beta$. For all
words $u, v$ over $\alpha \sqcup \beta$, all $b \in \beta$ and $a \in \alpha$, all words $X$ over
$\alpha$ and all words $Y$ over $\beta$, we have $u\,b\,a\,v \ne X\,Y$: a word over $\alpha$
followed by a word over $\beta$ never has a symbol of $\beta$ immediately followed by a symbol of
$\alpha$. -/
theorem append_inr_inl_ne {β : Type*} (u v : List (α ⊕ β)) (b : β) (a : α) :
    ∀ (X : List α) (Y : List β),
      u ++ Sum.inr b :: Sum.inl a :: v ≠ X.map Sum.inl ++ Y.map Sum.inr := by
  induction u with
  | nil =>
    intro X Y h
    cases X with
    | cons x X => simp at h
    | nil =>
      cases Y with
      | nil => simp at h
      | cons y Y =>
        cases Y with
        | nil => simp at h
        | cons y' Y => simp at h
  | cons s u ih =>
    intro X Y h
    cases X with
    | nil =>
      have : Sum.inl a ∈ Y.map (Sum.inr (α := α)) := by
        rw [← List.nil_append (Y.map Sum.inr), ← List.map_nil (f := Sum.inl), ← h]
        simp
      simp at this
    | cons x X =>
      simp only [List.cons_append, List.map_cons, List.cons.injEq] at h
      exact ih X Y h.2

/-- **A bit inside a word of letters followed by bits starts a suffix of the bits.** Let $\alpha$
and $\beta$ be types, call the elements of $\alpha$ letters and those of $\beta$ bits, and regard
words over $\alpha$ and over $\beta$ as words over the disjoint union $\alpha \oplus \beta$. If
$u\,b\,z = X\,Y$ for words $u, z$ over $\alpha \oplus \beta$, a bit $b$, a word $X$ of letters and a
word $Y$ of bits, then there are words $Y_1, Y_2$ of bits with $Y = Y_1 Y_2$ and $b\,z = Y_2$. -/
theorem exists_suffix_of_inr {β : Type*} {u z : List (α ⊕ β)} {b : β} :
    ∀ {X : List α} {Y : List β}, u ++ Sum.inr b :: z = X.map Sum.inl ++ Y.map Sum.inr →
      ∃ Y₁ Y₂, Y = Y₁ ++ Y₂ ∧ Sum.inr b :: z = Y₂.map Sum.inr := by
  induction u with
  | nil =>
    intro X Y h
    cases X with
    | cons x X => simp at h
    | nil => exact ⟨[], Y, rfl, by simpa using h⟩
  | cons s u ih =>
    intro X Y h
    cases X with
    | nil =>
      cases Y with
      | nil => simp at h
      | cons y Y =>
        simp only [List.cons_append, List.map_nil, List.nil_append, List.map_cons,
          List.cons.injEq] at h
        obtain ⟨Y₁, Y₂, rfl, h₂⟩ := ih (X := []) (Y := Y) (by simpa using h.2)
        exact ⟨y :: Y₁, Y₂, rfl, h₂⟩
    | cons x X =>
      simp only [List.cons_append, List.map_cons, List.cons.injEq] at h
      exact ih h.2

theorem exists_eq_replicate_append {j : ℕ} {Y B : List Bool} {r : List Bool}
    (h : Y ++ true :: r = List.replicate j false ++ B) :
    ∃ Y', Y = List.replicate j false ++ Y' ∧ Y' ++ true :: r = B := by
  induction j generalizing Y with
  | zero => exact ⟨Y, rfl, by simpa using h⟩
  | succ j ih =>
    cases Y with
    | nil => simp [List.replicate_succ] at h
    | cons y Y =>
      simp only [List.cons_append, List.replicate_succ, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨Y', rfl, h'⟩ := ih h
      exact ⟨Y', rfl, h'⟩

/-- **Codes of indices below $k$ contain no code of $k$.** Let $k \in \mathbb{N}$ and let
$J = (j_1, \dots, j_n)$ be a finite sequence of natural numbers with $j_1, \dots, j_n < k$. Write
$c(i) = \mathbf{t}\,\mathbf{f}^i$ for the unary code of $i$ and $c(J) = c(j_1) \cdots c(j_n)$. Then
there are no bit words $Y$ and $Z$ with $c(J) = Y\,c(k)\,Z$. -/
theorem bitCodes_ne_append_bitCode {k : ℕ} :
    ∀ {J : List ℕ}, (∀ j ∈ J, j < k) → ∀ Y Z : List Bool, bitCodes J ≠ Y ++ bitCode k ++ Z := by
  intro J
  induction J with
  | nil => intro _ Y Z h; simp [bitCode] at h
  | cons j J ih =>
    intro hJ Y Z h
    have hj : j < k := hJ j List.mem_cons_self
    cases Y with
    | nil =>
      simp only [bitCodes_cons, bitCode, List.nil_append, List.cons_append, List.cons.injEq,
        true_and] at h
      have := congrArg (List.drop j) h
      rw [List.drop_left' (by simp),
        List.drop_append_of_le_length (by simp; omega), List.drop_replicate] at this
      obtain ⟨n, hn⟩ : ∃ n, k - j = n + 1 := ⟨k - j - 1, by omega⟩
      rw [hn] at this
      have hhead := head?_bitCodes J
      rw [this] at hhead
      simp [List.replicate_succ] at hhead
    | cons y Y =>
      simp only [bitCodes_cons, bitCode, List.cons_append, List.cons.injEq,
        List.append_assoc] at h
      obtain ⟨-, h⟩ := h
      obtain ⟨Y', -, h'⟩ := exists_eq_replicate_append h.symm
      exact ih (fun i hi ↦ hJ i (List.mem_cons_of_mem _ hi)) Y' Z
        (by rw [← h']; simp [bitCode])

/-- **Malformed words are in no list language.** Let $P$ be a list of dominoes and $s$ a map from
dominoes to words (in use, the top or the bottom). Write the code of an index $i$ as the bits
$|\,1^i$, where $|$ stands for the bit true and $1$ for the bit false. A word over letters and
bits that is malformed with respect to $|P|$ (it has no bits, its first bit is a $1$, a bit is
followed by a letter, or it contains the factor $|\,1^{|P|}$) does not belong to the list
language of $s$ for $P$. -/
theorem not_mem_listLang_of_malformed {side : Domino α → List α} {P : List (Domino α)}
    {w : List (α ⊕ Bool)} (hw : w ∈ malformedLang P.length) : w ∉ listLang side P := by
  rintro ⟨I, hne, hlt, rfl⟩
  have hne' : I.reverse ≠ [] := by simpa using hne
  obtain ⟨j, J, hJ⟩ := List.exists_cons_of_ne_nil hne'
  rcases hw with ⟨x, hx⟩ | ⟨x, y, hx⟩ | ⟨u, v, b, a, hx⟩ | ⟨u, v, hx⟩
  · have := (eq_of_map_inl_append_map_inr (B := ([] : List Bool))
      (by simpa [listWord] using hx.symm)).2
    rw [hJ] at this
    simp at this
  · have := (eq_of_map_inl_append_map_inr (B := false :: y)
      (by simpa [listWord] using hx.symm)).2
    rw [hJ] at this
    simp at this
  · exact append_inr_inl_ne u v b a _ _ hx.symm
  · obtain ⟨Y₁, Y₂, hY, h₂⟩ := exists_suffix_of_inr (b := true)
      (z := ((List.replicate P.length false).map Sum.inr ++ v)) (u := u)
      (by simpa [listWord, bitCode] using hx.symm)
    have h₂' : (bitCode P.length).map Sum.inr ++ v = Y₂.map Sum.inr := by
      simpa [bitCode] using h₂
    obtain ⟨l₁, l₂, rfl, hl₁, -⟩ := List.map_eq_append_iff.mp h₂'.symm
    have hl : l₁ = bitCode P.length :=
      List.map_injective_iff.mpr (fun _ _ h ↦ Sum.inr_injective h) hl₁
    subst hl
    exact bitCodes_ne_append_bitCode (fun j hj ↦ hlt j (List.mem_reverse.mp hj)) Y₁ l₂
      (by rw [hY, List.append_assoc])

/-- **Mismatched words are not in the list language.** Let $P$ be a list of dominoes and $s$ a map
from dominoes to words (in use, the top or the bottom). No word of the mismatch language of $s$
for $P$ belongs to the list language of $s$ for $P$. -/
theorem not_mem_listLang_of_mismatch {side : Domino α → List α} {P : List (Domino α)}
    {w : List (α ⊕ Bool)} (hw : w ∈ mismatchLang side P) : w ∉ listLang side P := by
  obtain ⟨x, I, -, -, hx, rfl⟩ := hw
  rintro ⟨I', -, -, h⟩
  obtain ⟨rfl, hy⟩ := eq_of_map_inl_append_map_inr h
  obtain rfl := List.reverse_injective (bitCodes_injective hy)
  exact hx rfl

theorem letters_bits_or_adj {β : Type*} (w : List (α ⊕ β)) :
    (∃ (x : List α) (y : List β), w = x.map Sum.inl ++ y.map Sum.inr) ∨
      ∃ (u v : List (α ⊕ β)) (b : β) (a : α), w = u ++ Sum.inr b :: Sum.inl a :: v := by
  induction w with
  | nil => exact Or.inl ⟨[], [], rfl⟩
  | cons s w ih =>
    rcases ih with ⟨x, y, rfl⟩ | ⟨u, v, b, a, rfl⟩
    · rcases s with a | b
      · exact Or.inl ⟨a :: x, y, rfl⟩
      · cases x with
        | nil => exact Or.inl ⟨[], b :: y, rfl⟩
        | cons a x => exact Or.inr ⟨[], _, b, a, rfl⟩
    · exact Or.inr ⟨s :: u, v, b, a, rfl⟩

theorem exists_eq_replicate_append_bitCodes (y : List Bool) :
    ∃ n J, y = List.replicate n false ++ bitCodes J := by
  induction y with
  | nil => exact ⟨0, [], rfl⟩
  | cons b y ih =>
    obtain ⟨n, J, rfl⟩ := ih
    cases b
    · exact ⟨n + 1, J, rfl⟩
    · exact ⟨0, n :: J, rfl⟩

/-- **Every word is malformed or well formed.** Let $k \in \mathbb{N}$ and let $w$ be a word over
$\alpha \oplus \mathrm{Bool}$. Then $w$ is malformed with bound $k$, or
$w = x\, c(j_1) \cdots c(j_n)$ for a word $x$ over $\alpha$ and a nonempty sequence of indices
$j_1, \dots, j_n < k$, where $c(j)$ is the unary code of $j$: the bit $\mathrm{true}$ followed by
$j$ bits $\mathrm{false}$. -/
theorem malformed_or_wellFormed (k : ℕ) (w : List (α ⊕ Bool)) :
    w ∈ malformedLang k ∨ ∃ (x : List α) (J : List ℕ), J ≠ [] ∧ (∀ j ∈ J, j < k) ∧
      w = x.map Sum.inl ++ (bitCodes J).map Sum.inr := by
  rcases letters_bits_or_adj w with ⟨x, y, rfl⟩ | ⟨u, v, b, a, rfl⟩
  · obtain ⟨n, J, rfl⟩ := exists_eq_replicate_append_bitCodes y
    cases n with
    | succ n =>
      exact Or.inl (Or.inr (Or.inl ⟨x, List.replicate n false ++ bitCodes J,
        by simp [List.replicate_succ]⟩))
    | zero =>
      rcases eq_or_ne J [] with rfl | hJ
      · exact Or.inl (Or.inl ⟨x, by simp⟩)
      · by_cases hlt : ∀ j ∈ J, j < k
        · exact Or.inr ⟨x, J, hJ, hlt, by simp⟩
        · simp only [not_forall, not_lt] at hlt
          obtain ⟨j, hj, hkj⟩ := hlt
          obtain ⟨J₁, J₂, rfl⟩ := List.append_of_mem hj
          refine Or.inl (Or.inr (Or.inr (Or.inr ⟨x.map Sum.inl ++ (bitCodes J₁).map Sum.inr,
            (List.replicate (j - k) false ++ bitCodes J₂).map Sum.inr, ?_⟩)))
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
          rw [Nat.add_sub_cancel_left]
          simp only [List.replicate_zero, List.nil_append, bitCodes_append, bitCodes_cons, bitCode,
            List.replicate_add, List.map_append, List.map_cons, List.append_assoc,
            List.cons_append]
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨u, v, b, a, rfl⟩)))

theorem mem_univVal_zero_iff {P : List (Domino α)} {w : List (α ⊕ Bool)} :
    w ∈ univVal P 0 ↔ ¬(w ∈ listLang Prod.fst P ∧ w ∈ listLang Prod.snd P) := by
  constructor
  · rintro (h | h | h) ⟨h₁, h₂⟩
    · exact not_mem_listLang_of_malformed h h₁
    · exact not_mem_listLang_of_mismatch h h₁
    · exact not_mem_listLang_of_mismatch h h₂
  · intro h
    rcases malformed_or_wellFormed P.length w with hm | ⟨x, J, hJ, hlt, rfl⟩
    · exact Or.inl hm
    · have hne : J.reverse ≠ [] := by simpa using hJ
      have hlt' : ∀ i ∈ J.reverse, i < P.length := fun i hi ↦ hlt i (List.mem_reverse.mp hi)
      by_cases h₁ : x = flat Prod.fst P J.reverse
      · by_cases h₂ : x = flat Prod.snd P J.reverse
        · exact absurd ⟨⟨J.reverse, hne, hlt', by simp [listWord, h₁]⟩,
            ⟨J.reverse, hne, hlt', by simp [listWord, h₂]⟩⟩ h
        · exact Or.inr (Or.inr ⟨x, J.reverse, hne, hlt', h₂, by simp⟩)
      · exact Or.inr (Or.inl ⟨x, J.reverse, hne, hlt', h₁, by simp⟩)

/-- **The universality grammar generates every word exactly when PCP has no solution.** Let
$\alpha$ be a finite alphabet with decidable equality and let $P$ be a list of dominoes over
$\alpha$. The universality grammar of $P$ generates every word over $\alpha \oplus \mathrm{Bool}$
if and only if the Post correspondence problem $P$ has no solution. -/
theorem forall_mem_language_univGrammar_iff [Fintype α] [DecidableEq α] (P : List (Domino α)) :
    (∀ w, w ∈ (univGrammar P).language) ↔ ¬PCP P := by
  rw [pcp_iff_exists_mem_listLang, language_univGrammar]
  simp only [mem_univVal_zero_iff, not_exists]

end Complement

/-! ### The many-one reduction -/

section Computable

variable [Fintype α] [DecidableEq α] [Primcodable α]

theorem primrec_bitCode : Primrec bitCode := by
  refine (Primrec.list_cons.comp (Primrec.const true)
    (Primrec.list_map Primrec.list_range (Primrec.const false).to₂)).of_eq fun k ↦ ?_
  simp only [bitCode, List.cons.injEq, true_and]
  exact List.eq_replicate_iff.mpr ⟨by simp, by simp⟩

omit [Fintype α] [DecidableEq α] in
theorem primrec_codeSyms : Primrec fun i : ℕ ↦ (bitCode i).map (uBit (α := α)) :=
  Primrec.list_map primrec_bitCode ((Primrec.dom_finite uBit).comp Primrec.snd).to₂

omit [Fintype α] [DecidableEq α] in
theorem primrec_uLetter : Primrec (uLetter (α := α)) := Primrec.sumInr.comp Primrec.sumInl

omit [DecidableEq α] in
theorem primrec_baseRules : Primrec (baseRules (α := α)) := by
  have hD : Primrec fun k : ℕ ↦ ((0 : ℕ), uNt 6 :: (bitCode k).map (uBit (α := α)) ++ [uNt 6]) :=
    Primrec.pair (Primrec.const 0) (Primrec.list_append.comp
      (Primrec.list_cons.comp (Primrec.const _) primrec_codeSyms) (Primrec.const _))
  have hC : Primrec fun k : ℕ ↦ (List.range k).map fun i ↦
      ((7 : ℕ), (bitCode i).map (uBit (α := α)) ++ [uNt 7]) :=
    Primrec.list_map Primrec.list_range (Primrec.pair (Primrec.const 7)
      (Primrec.list_append.comp (primrec_codeSyms.comp Primrec.snd) (Primrec.const _))).to₂
  exact (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.const [(3, []), (5, []), (6, []), (7, []), (5, [uBit true, uNt 5]),
      (5, [uBit false, uNt 5]), (6, [uBit true, uNt 6]), (6, [uBit false, uNt 6]), (0, [uNt 3]),
      (0, [uNt 3, uBit false, uNt 5])])
    (Primrec.list_cons.comp hD (Primrec.const [(0, [uNt 1]), (0, [uNt 2])])))
    (Primrec.const (allLetters.flatMap (fun a ↦ [(3, [uLetter a, uNt 3]), (4, [uLetter a, uNt 3]),
      (6, [uLetter a, uNt 6]), (0, [uNt 6, uBit true, uLetter a, uNt 6]),
      (0, [uNt 6, uBit false, uLetter a, uNt 6])])))) hC).of_eq fun k ↦ rfl

theorem primrec_mismatchRules {side : Domino α → List α} (hside : Primrec side) (A : ℕ) :
    Primrec (mismatchRules side A) := by
  have hdom : Primrec₂ (domino (α := α)) := Primrec.list_getD _
  -- the side word of the `i`-th domino, for `q = (P, i)`
  have hw : Primrec fun q : List (Domino α) × ℕ ↦ side (domino q.1 q.2) :=
    hside.comp (hdom.comp Primrec.fst Primrec.snd)
  have hcode : Primrec fun q : List (Domino α) × ℕ ↦ (bitCode q.2).map (uBit (α := α)) :=
    primrec_codeSyms.comp Primrec.snd
  have hR1 : Primrec fun q : List (Domino α) × ℕ ↦
      (A, (side (domino q.1 q.2)).map uLetter ++ uNt A :: (bitCode q.2).map (uBit (α := α))) :=
    Primrec.pair (Primrec.const A) (Primrec.list_append.comp
      (Primrec.list_map hw (primrec_uLetter.comp Primrec.snd).to₂)
      (Primrec.list_cons.comp (Primrec.const _) hcode))
  have hR2 : Primrec fun q : List (Domino α) × ℕ ↦
      (A, (side (domino q.1 q.2)).map uLetter ++ uNt 4 :: (bitCode q.2).map (uBit (α := α))) :=
    Primrec.pair (Primrec.const A) (Primrec.list_append.comp
      (Primrec.list_map hw (primrec_uLetter.comp Primrec.snd).to₂)
      (Primrec.list_cons.comp (Primrec.const _) hcode))
  -- the prefix of length `m`, for `r = (q, m)`
  have hpre : Primrec fun r : (List (Domino α) × ℕ) × ℕ ↦
      ((side (domino r.1.1 r.1.2)).take r.2).map (uLetter (α := α)) :=
    Primrec.list_map (Primrec.list_take.comp Primrec.snd (hw.comp Primrec.fst))
      (primrec_uLetter.comp Primrec.snd).to₂
  have hR3 : Primrec fun r : (List (Domino α) × ℕ) × ℕ ↦
      (A, ((side (domino r.1.1 r.1.2)).take r.2).map uLetter ++ uNt 7 ::
        (bitCode r.1.2).map (uBit (α := α))) :=
    Primrec.pair (Primrec.const A) (Primrec.list_append.comp hpre
      (Primrec.list_cons.comp (Primrec.const _) (hcode.comp Primrec.fst)))
  have hnext : Primrec fun r : (List (Domino α) × ℕ) × ℕ ↦
      ((side (domino r.1.1 r.1.2)).drop r.2).take 1 :=
    Primrec.list_take.comp (Primrec.const 1)
      (Primrec.list_drop.comp Primrec.snd (hw.comp Primrec.fst))
  -- the stop production for the letter `a`, for `t = ((r, c), a)`
  have hR4 : Primrec fun t : (((List (Domino α) × ℕ) × ℕ) × α) × α ↦
      (A, ((side (domino t.1.1.1.1 t.1.1.1.2)).take t.1.1.2).map uLetter ++
        uLetter t.2 :: uNt 3 :: uNt 7 :: (bitCode t.1.1.1.2).map (uBit (α := α))) :=
    Primrec.pair (Primrec.const A) (Primrec.list_append.comp (hpre.comp (Primrec.fst.comp
      Primrec.fst)) (Primrec.list_cons.comp (primrec_uLetter.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.const _) (Primrec.list_cons.comp (Primrec.const _)
          (hcode.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))))
  have hstop : Primrec fun s : ((List (Domino α) × ℕ) × ℕ) × α ↦ (others s.2).map fun a ↦
      (A, ((side (domino s.1.1.1 s.1.1.2)).take s.1.2).map uLetter ++
        uLetter a :: uNt 3 :: uNt 7 :: (bitCode s.1.1.2).map (uBit (α := α))) :=
    Primrec.list_map ((Primrec.dom_finite others).comp Primrec.snd) hR4.to₂
  have hinner : Primrec fun r : (List (Domino α) × ℕ) × ℕ ↦
      (A, ((side (domino r.1.1 r.1.2)).take r.2).map uLetter ++ uNt 7 ::
        (bitCode r.1.2).map (uBit (α := α))) ::
      (((side (domino r.1.1 r.1.2)).drop r.2).take 1).flatMap fun c ↦ (others c).map fun a ↦
        (A, ((side (domino r.1.1 r.1.2)).take r.2).map uLetter ++
          uLetter a :: uNt 3 :: uNt 7 :: (bitCode r.1.2).map (uBit (α := α))) :=
    Primrec.list_cons.comp hR3 (Primrec.list_flatMap hnext hstop.to₂)
  have hg : Primrec fun q : List (Domino α) × ℕ ↦
      (A, (side (domino q.1 q.2)).map uLetter ++ uNt A :: (bitCode q.2).map (uBit (α := α))) ::
      (A, (side (domino q.1 q.2)).map uLetter ++ uNt 4 :: (bitCode q.2).map (uBit (α := α))) ::
      (List.range (side (domino q.1 q.2)).length).flatMap fun m ↦
        (A, ((side (domino q.1 q.2)).take m).map uLetter ++ uNt 7 ::
          (bitCode q.2).map (uBit (α := α))) ::
        (((side (domino q.1 q.2)).drop m).take 1).flatMap fun c ↦ (others c).map fun a ↦
          (A, ((side (domino q.1 q.2)).take m).map uLetter ++
            uLetter a :: uNt 3 :: uNt 7 :: (bitCode q.2).map (uBit (α := α))) :=
    Primrec.list_cons.comp hR1 (Primrec.list_cons.comp hR2
      (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp hw)) hinner.to₂))
  exact Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) hg.to₂

theorem primrec_univGrammar : Primrec (univGrammar (α := α)) :=
  EncodedCFG.primrec₂_mk.comp (Primrec.const 0) (Primrec.list_append.comp
    (Primrec.list_append.comp (primrec_baseRules.comp Primrec.list_length)
      (primrec_mismatchRules Primrec.fst 1)) (primrec_mismatchRules Primrec.snd 2))

omit [Fintype α] in
/-- **The complement of PCP many-one reduces to universality of context-free grammars.** Let
$\alpha$ be a finite alphabet with decidable equality and a primitive recursive encoding. There
is a computable map sending each PCP instance $P$ (a list of dominoes over $\alpha$) to an
encoded context-free grammar $G_P$ over the alphabet $\alpha \oplus \mathrm{Bool}$ (the letters
of $\alpha$ together with two bits) such that $P$ has no PCP solution if and only if $G_P$
generates every word over $\alpha \oplus \mathrm{Bool}$. -/
theorem manyOneReducible_not_pcp_univ [Finite α] :
    ManyOneReducible (fun P : List (Domino α) ↦ ¬PCP P) fun g : EncodedCFG (α ⊕ Bool) ↦
      ∀ w, w ∈ g.language :=
  let _ := Fintype.ofFinite α
  ⟨univGrammar, primrec_univGrammar.to_comp, fun P ↦ (forall_mem_language_univGrammar_iff P).symm⟩

end Computable

end Cslib.Decidability.Grammar
