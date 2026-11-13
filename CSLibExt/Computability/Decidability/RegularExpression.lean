/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular expressions as data: membership is decidable
-/
module

public import CSLibExt.Computability.Decidability.ContextFree
public import CSLibExt.Computability.Decidability.ContextFreeRegular
public import CSLibExt.Computability.Languages.ContextFree.CYK
public import Mathlib.Computability.RegularExpressions

/-!
# Regular expressions as data: membership is decidable

Mathlib's `RegularExpression α` is an inductive type without a `Primcodable` instance, so it
cannot be the input of a computable function. `Cslib.Language.EncodedRegex α` is a concrete
encoding: a list of nodes (`RegexNode`), each a constant or an operator whose arguments are node
indices, read with the last node as the root. Every list is accepted and the semantics is total:
an argument that is not the index of an earlier node (a forward or self reference, or an index
past the end) reads as `0`, and the empty list denotes `0`. Encodings produced by `flatten` only
refer to earlier nodes.

* `EncodedRegex.regexAt e k`, `EncodedRegex.toRegex e`: the regular expression at node `k` and at
  the root (an argument that is not an earlier node reads as `0`).
* `EncodedRegex.flatten r`: the encoding of a regular expression, with
  `EncodedRegex.toRegex_flatten : (flatten r).toRegex = r`.
* `EncodedRegex.toGrammar e`: an encoded context-free grammar with one nonterminal per node
  (`plus` gives two unit productions, `comp` a binary one, `star` the productions `k → ε` and
  `k → i k`); `EncodedRegex.language_toGrammar` proves that it generates the language of the
  expression.
* `EncodedRegex.memB_iff`, `EncodedRegex.tm2Decidable_mem_matches`: **Sipser, Theorem 4.3**
  (A_REX), membership is decidable by a multi-stack machine, through the A_CFG decider
  `EncodedCFG.memLanguageB`.
* `EncodedRegex.isEmptyB_iff`, `EncodedRegex.tm2Decidable_matches_eq_zero`: emptiness (E_REX),
  through the E_CFG decider `EncodedCFG.isEmptyB`.
* `EncodedRegex.infiniteB_iff`, `EncodedRegex.tm2Decidable_matches_infinite`: infiniteness, by
  one left-to-right pass over the nodes computing three flags per node (`flags`): the language
  is nonempty, has a nonempty word, is infinite (`flagsOK_flags`). The pass is quadratic in the
  number of nodes (list appends and lookups), with no enumeration of words.
* `EncodedRegex.subsetB_iff`, `EncodedRegex.tm2Decidable_matches_le`: inclusion in the language
  of an encoded DFA, through the CFG ⊆ DFA decider `EncodedCFG.subsetB`.
-/

@[expose] public section

namespace Cslib.Language

open Cslib.Decidability

/-- **Regular-expression node.** A node of an encoded regular expression over an alphabet
$\alpha$ is one of six kinds: zero, epsilon, a letter $a \in \alpha$, a sum with arguments
$i, j \in \mathbb{N}$, a product (concatenation) with arguments $i, j \in \mathbb{N}$, or a star
with argument $i \in \mathbb{N}$, where the arguments are indices of nodes. -/
inductive RegexNode (α : Type*) where
  | zero
  | epsilon
  | char (a : α)
  | plus (i j : ℕ)
  | comp (i j : ℕ)
  | star (i : ℕ)

/-- **Encoded regular expressions.** An encoded regular expression over an alphabet $\alpha$ is a
list of regular-expression nodes, each a constant ($0$, $1$ or a letter) or an operator (sum,
concatenation or star) whose arguments are node indices; the last node is the root. Any list is
allowed: in the semantics, an argument that is not the index of an earlier node reads as $0$,
and the empty list denotes $0$. -/
structure EncodedRegex (α : Type*) where
  /-- The nodes. -/
  nodes : List (RegexNode α)

namespace EncodedRegex

variable {α : Type*}

/-! ## Semantics -/

/-- **Node at an index.** For an encoded regular expression $e$ and a natural number $k$, the
node of $e$ at index $k$ is the entry at position $k$ (counting from $0$) of its list of
nodes, or the zero node when $k$ is at least the length of the list. -/
def node (e : EncodedRegex α) (k : ℕ) : RegexNode α :=
  e.nodes.getD k .zero

/-- **Regular expression at a node.** For an encoded regular expression $e$ and $k \in \mathbb{N}$,
the regular expression at node $k$ is defined by recursion on $k$ from the node of $e$ at index
$k$ (a zero node when $k$ is past the end): a zero node gives $0$, an epsilon node gives $1$, a
node for a letter $a$ gives $a$, and a sum, product or star node gives the sum, product or star
of the regular expressions at its arguments, where an argument that is not smaller than $k$
reads as $0$. -/
def regexAt (e : EncodedRegex α) (k : ℕ) : RegularExpression α :=
  match e.node k with
  | .zero => 0
  | .epsilon => 1
  | .char a => .char a
  | .plus i j => (if _ : i < k then e.regexAt i else 0) + (if _ : j < k then e.regexAt j else 0)
  | .comp i j => (if _ : i < k then e.regexAt i else 0) * (if _ : j < k then e.regexAt j else 0)
  | .star i => .star (if _ : i < k then e.regexAt i else 0)
termination_by k

/-- **The regular expression denoted by an encoding.** An encoded regular expression $e$ with $n$
nodes denotes the regular expression at its node $n - 1$, the last node. For $n = 0$ this is the
expression at node $0$, which lies past the end of the list and is the empty expression $0$. -/
def toRegex (e : EncodedRegex α) : RegularExpression α :=
  e.regexAt (e.nodes.length - 1)

section NodeCases

variable {e : EncodedRegex α} {k : ℕ}

theorem regexAt_of_zero (h : e.node k = .zero) : e.regexAt k = 0 := by
  rw [regexAt, h]

theorem regexAt_of_epsilon (h : e.node k = .epsilon) : e.regexAt k = 1 := by
  rw [regexAt, h]

theorem regexAt_of_char {a : α} (h : e.node k = .char a) : e.regexAt k = .char a := by
  rw [regexAt, h]

theorem regexAt_of_plus {i j : ℕ} (h : e.node k = .plus i j) :
    e.regexAt k = (if i < k then e.regexAt i else 0) + (if j < k then e.regexAt j else 0) := by
  rw [regexAt, h]
  simp only [dite_eq_ite]

theorem regexAt_of_comp {i j : ℕ} (h : e.node k = .comp i j) :
    e.regexAt k = (if i < k then e.regexAt i else 0) * (if j < k then e.regexAt j else 0) := by
  rw [regexAt, h]
  simp only [dite_eq_ite]

theorem regexAt_of_star {i : ℕ} (h : e.node k = .star i) :
    e.regexAt k = .star (if i < k then e.regexAt i else 0) := by
  rw [regexAt, h]
  simp only [dite_eq_ite]

end NodeCases

theorem node_of_le {e : EncodedRegex α} {k : ℕ} (hk : e.nodes.length ≤ k) : e.node k = .zero :=
  List.getD_eq_default _ _ hk

theorem node_append {l m : List (RegexNode α)} {k : ℕ} (hk : k < l.length) :
    (⟨l ++ m⟩ : EncodedRegex α).node k = (⟨l⟩ : EncodedRegex α).node k :=
  List.getD_append _ _ _ _ hk

/-- **Appending nodes does not change earlier expressions.** Let $l$ and $m$ be lists of
regular-expression nodes and let $k$ be smaller than the length of $l$. Then the regular
expression at node $k$ of the encoding with nodes $l$ followed by $m$ equals the regular
expression at node $k$ of the encoding with nodes $l$. -/
theorem regexAt_append {l m : List (RegexNode α)} {k : ℕ} (hk : k < l.length) :
    (⟨l ++ m⟩ : EncodedRegex α).regexAt k = (⟨l⟩ : EncodedRegex α).regexAt k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      have hc : ∀ i, (if _ : i < k then (⟨l ++ m⟩ : EncodedRegex α).regexAt i else 0) =
          (if _ : i < k then (⟨l⟩ : EncodedRegex α).regexAt i else 0) := fun i => by
        split_ifs with hi
        exacts [ih i hi (hi.trans hk), rfl]
      rw [regexAt, regexAt, node_append hk]
      cases (⟨l⟩ : EncodedRegex α).node k with
      | zero | epsilon | char a => rfl
      | plus i j => simp only [hc]
      | comp i j => simp only [hc]
      | star i => simp only [hc]

/-! ## Every regular expression has an encoding -/

/-- **Postorder encoding after a prefix.** For a regular expression $r$ and a list $l$ of nodes,
the nodes of $r$ are appended after $l$ in postorder, by recursion on $r$. For $0$, $1$ and a
letter $a$, append the single node $0$, $1$ or $a$. For a sum $s + t$ (respectively a
concatenation $st$), append the nodes of $s$ after $l$, giving $l_1$, then the nodes of $t$ after
$l_1$, giving $l_2$, then a sum (respectively concatenation) node with arguments $|l_1| - 1$ and
$|l_2| - 1$. For a star $s^*$, append the nodes of $s$ after $l$, giving $l_1$, then a star node
with argument $|l_1| - 1$. The root of $r$ is the last node. -/
def flattenAux : RegularExpression α → List (RegexNode α) → List (RegexNode α)
  | .zero, l => l ++ [.zero]
  | .epsilon, l => l ++ [.epsilon]
  | .char a, l => l ++ [.char a]
  | .plus r s, l =>
      let l₁ := flattenAux r l
      let l₂ := flattenAux s l₁
      l₂ ++ [.plus (l₁.length - 1) (l₂.length - 1)]
  | .comp r s, l =>
      let l₁ := flattenAux r l
      let l₂ := flattenAux s l₁
      l₂ ++ [.comp (l₁.length - 1) (l₂.length - 1)]
  | .star r, l =>
      let l₁ := flattenAux r l
      l₁ ++ [.star (l₁.length - 1)]

/-- **Encoding of a regular expression.** The encoding of a regular expression $r$ is the list of
nodes obtained by appending the nodes of $r$ in postorder after the empty list, so that the root
of $r$ is the last node. -/
def flatten (r : RegularExpression α) : EncodedRegex α :=
  ⟨flattenAux r []⟩

theorem prefix_flattenAux (r : RegularExpression α) (l : List (RegexNode α)) :
    l <+: flattenAux r l := by
  induction r generalizing l with
  | zero | epsilon | char a => exact List.prefix_append _ _
  | plus r s ihr ihs | comp r s ihr ihs =>
      exact (ihr l).trans ((ihs _).trans (List.prefix_append _ _))
  | star r ihr => exact (ihr l).trans (List.prefix_append _ _)

theorem length_flattenAux_pos (r : RegularExpression α) (l : List (RegexNode α)) :
    l.length < (flattenAux r l).length := by
  induction r generalizing l with
  | zero | epsilon | char a => simp [flattenAux]
  | plus r s ihr ihs | comp r s ihr ihs =>
      have := ihr l
      have := ihs (flattenAux r l)
      simp only [flattenAux, List.length_append, List.length_singleton]
      omega
  | star r ihr =>
      have := ihr l
      simp only [flattenAux, List.length_append, List.length_singleton]
      omega

theorem node_last (l : List (RegexNode α)) (n : RegexNode α) :
    (⟨l ++ [n]⟩ : EncodedRegex α).node l.length = n := by
  simp [node]

theorem regexAt_flattenAux (r : RegularExpression α) (l : List (RegexNode α)) :
    (⟨flattenAux r l⟩ : EncodedRegex α).regexAt ((flattenAux r l).length - 1) = r := by
  induction r generalizing l with
  | zero => exact regexAt_of_zero (by simp [flattenAux, node])
  | epsilon => exact regexAt_of_epsilon (by simp [flattenAux, node])
  | char a => exact regexAt_of_char (by simp [flattenAux, node])
  | plus r s ihr ihs =>
      have h₁ := length_flattenAux_pos r l
      have h₂ := length_flattenAux_pos s (flattenAux r l)
      obtain ⟨m, hm⟩ := prefix_flattenAux s (flattenAux r l)
      have hr := ihr l
      have hs := ihs (flattenAux r l)
      simp only [flattenAux]
      generalize flattenAux r l = l₁ at *
      generalize flattenAux s l₁ = l₂ at *
      rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
        regexAt_of_plus (node_last _ _), ite_eq_left (show l₁.length - 1 < l₂.length by omega),
        ite_eq_left (show l₂.length - 1 < l₂.length by omega), regexAt_append (by omega),
        regexAt_append (by omega), hs, ← hm, regexAt_append (by omega), hr]
      rfl
  | comp r s ihr ihs =>
      have h₁ := length_flattenAux_pos r l
      have h₂ := length_flattenAux_pos s (flattenAux r l)
      obtain ⟨m, hm⟩ := prefix_flattenAux s (flattenAux r l)
      have hr := ihr l
      have hs := ihs (flattenAux r l)
      simp only [flattenAux]
      generalize flattenAux r l = l₁ at *
      generalize flattenAux s l₁ = l₂ at *
      rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
        regexAt_of_comp (node_last _ _), ite_eq_left (show l₁.length - 1 < l₂.length by omega),
        ite_eq_left (show l₂.length - 1 < l₂.length by omega), regexAt_append (by omega),
        regexAt_append (by omega), hs, ← hm, regexAt_append (by omega), hr]
      rfl
  | star r ihr =>
      have h₁ := length_flattenAux_pos r l
      have hr := ihr l
      simp only [flattenAux]
      generalize flattenAux r l = l₁ at *
      rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
        regexAt_of_star (node_last _ _), ite_eq_left (show l₁.length - 1 < l₁.length by omega),
        regexAt_append (by omega), hr]

/-- **Every regular expression has an encoding.** For every regular expression $r$ over an
alphabet $\alpha$, the encoded regular expression obtained by flattening $r$ (listing the nodes of
its subexpressions in postorder, so that the root of $r$ is the last node) denotes $r$. -/
theorem toRegex_flatten (r : RegularExpression α) : (flatten r).toRegex = r :=
  regexAt_flattenAux r []

/-! ## Infiniteness by a structural pass

Three flags per node, computed from the flags of earlier nodes: the language is nonempty, it has
a nonempty word, and it is infinite. A product is infinite when one factor is infinite and the
other nonempty; a star is infinite exactly when its argument has a nonempty word. -/

/-- **Flags of the empty language.** The flag triple of the empty language is
$(\mathrm{false}, \mathrm{false}, \mathrm{false})$; the three flags of a language say whether it is
nonempty, whether it has a nonempty word, and whether it is infinite. This triple is also read for
an argument of a node that is not an earlier node. -/
def zeroFlags : Bool × Bool × Bool :=
  (false, false, false)

/-- **Flags of a sum.** For triples of booleans $b = (b_1, b_2, b_3)$ and
$c = (c_1, c_2, c_3)$, the flags of the sum are $(b_1 \lor c_1, b_2 \lor c_2, b_3 \lor c_3)$.

If $b$ and $c$ record whether languages $L$ and $M$ are nonempty, contain a nonempty word and
are infinite, then the flags of the sum record the same for their union $L \cup M$. -/
def plusFlags (b c : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (b.1 || c.1, b.2.1 || c.2.1, b.2.2 || c.2.2)

/-- **Flags of a concatenation.** For triples of Booleans $b = (b_1, b_2, b_3)$ and
$c = (c_1, c_2, c_3)$, the flags of the product are
$(b_1 \land c_1,\ (b_2 \land c_1) \lor (b_1 \land c_2),\ (b_3 \land c_1) \lor (b_1 \land c_3))$.

If $b$ and $c$ record whether languages $L$ and $M$ are nonempty, contain a nonempty word,
and are infinite, the result records the same for $LM$: in particular $LM$ is infinite when
one factor is infinite and the other nonempty. -/
def compFlags (b c : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (b.1 && c.1, b.2.1 && c.1 || b.1 && c.2.1, b.2.2 && c.1 || b.1 && c.2.2)

/-- **Flags of a star.** Given a triple of Booleans $(b_1, b_2, b_3)$, the flags of its star are
$(\mathrm{true}, b_2, b_2)$. Read as the flags (nonempty, has a nonempty word, infinite) of a
language, a star is always nonempty, and it has a nonempty word, and is infinite, exactly when
the argument has a nonempty word. -/
def starFlags (b : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (true, b.2.1, b.2.1)

/-- **Flags of the next node.** Given the list $A$ of flag triples of the nodes before it, the
flag triple of a node is $(\mathrm{false}, \mathrm{false}, \mathrm{false})$ for a zero node,
$(\mathrm{true}, \mathrm{false}, \mathrm{false})$ for an epsilon node and
$(\mathrm{true}, \mathrm{true}, \mathrm{false})$ for a letter node. For a sum, product or star
node it is the flags of a sum, product or star applied to the entries of $A$ at its arguments,
where an argument that is not an index of $A$ reads as
$(\mathrm{false}, \mathrm{false}, \mathrm{false})$. -/
def stepFlags (acc : List (Bool × Bool × Bool)) : RegexNode α → Bool × Bool × Bool
  | .zero => zeroFlags
  | .epsilon => (true, false, false)
  | .char _ => (true, true, false)
  | .plus i j => plusFlags (acc.getD i zeroFlags) (acc.getD j zeroFlags)
  | .comp i j => compFlags (acc.getD i zeroFlags) (acc.getD j zeroFlags)
  | .star i => starFlags (acc.getD i zeroFlags)

/-- **Flags of all nodes.** For a list of nodes $n_0, \dots, n_{m-1}$, the flags
$f_0, \dots, f_{m-1}$ are computed in one left-to-right pass: $f_k$ is the step flags of node
$n_k$ computed from the flags $f_0, \dots, f_{k-1}$ of the nodes before it. -/
def flags (l : List (RegexNode α)) : List (Bool × Bool × Bool) :=
  l.foldl (fun acc n => acc ++ [stepFlags acc n]) []

/-- **Flags of a language.** A triple of Booleans $(b_1, b_2, b_3)$ describes a language $L$ when
$b_1$ is true exactly when $L$ is nonempty, $b_2$ is true exactly when $L$ contains a nonempty
word, and $b_3$ is true exactly when $L$ is infinite. -/
def FlagsOK (b : Bool × Bool × Bool) (L : Language α) : Prop :=
  (b.1 = true ↔ ∃ w, w ∈ L) ∧ (b.2.1 = true ↔ ∃ w ∈ L, w ≠ []) ∧ (b.2.2 = true ↔ L.Infinite)

theorem flagsOK_zero : FlagsOK zeroFlags (0 : Language α) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [zeroFlags, Bool.false_eq_true, false_iff]
  · exact fun ⟨_, h⟩ => h
  · exact fun ⟨_, h, _⟩ => h
  · exact Set.not_infinite.2 Set.finite_empty

theorem flagsOK_one : FlagsOK (true, false, false) (1 : Language α) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Bool.false_eq_true, false_iff, true_iff]
  · exact ⟨[], (Language.mem_one _).2 rfl⟩
  · exact fun ⟨w, hw, hne⟩ => hne ((Language.mem_one _).1 hw)
  · exact Set.not_infinite.2 (Set.finite_singleton [])

theorem flagsOK_char (a : α) : FlagsOK (true, true, false) ({[a]} : Language α) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Bool.false_eq_true, false_iff, true_iff]
  · exact ⟨[a], rfl⟩
  · exact ⟨[a], rfl, List.cons_ne_nil _ _⟩
  · exact Set.not_infinite.2 (Set.finite_singleton [a])

theorem flagsOK_add {b c : Bool × Bool × Bool} {L M : Language α} (hL : FlagsOK b L)
    (hM : FlagsOK c M) : FlagsOK (plusFlags b c) (L + M) := by
  unfold plusFlags
  rw [Language.add_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Bool.or_eq_true, hL.1, hM.1]
    exact ⟨fun h => h.elim (fun ⟨w, hw⟩ => ⟨w, .inl hw⟩) fun ⟨w, hw⟩ => ⟨w, .inr hw⟩,
      fun ⟨w, hw⟩ => hw.elim (fun h => .inl ⟨w, h⟩) fun h => .inr ⟨w, h⟩⟩
  · rw [Bool.or_eq_true, hL.2.1, hM.2.1]
    exact ⟨fun h => h.elim (fun ⟨w, hw, hn⟩ => ⟨w, .inl hw, hn⟩)
      fun ⟨w, hw, hn⟩ => ⟨w, .inr hw, hn⟩,
      fun ⟨w, hw, hn⟩ => hw.elim (fun h => .inl ⟨w, h, hn⟩) fun h => .inr ⟨w, h, hn⟩⟩
  · rw [Bool.or_eq_true, hL.2.2, hM.2.2]
    exact Set.infinite_union.symm

theorem flagsOK_mul {b c : Bool × Bool × Bool} {L M : Language α} (hL : FlagsOK b L)
    (hM : FlagsOK c M) :
    FlagsOK (compFlags b c) (L * M) := by
  unfold compFlags
  have hne : (∃ w, w ∈ L * M) ↔ (∃ w, w ∈ L) ∧ ∃ w, w ∈ M := by
    simp only [Language.mem_mul]
    exact ⟨fun ⟨_, x, hx, y, hy, _⟩ => ⟨⟨x, hx⟩, y, hy⟩,
      fun ⟨⟨x, hx⟩, y, hy⟩ => ⟨_, x, hx, y, hy, rfl⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Bool.and_eq_true, hL.1, hM.1, hne]
  · rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, hL.1, hM.1, hL.2.1, hM.2.1]
    simp only [Language.mem_mul]
    constructor
    · rintro (⟨⟨x, hx, hxn⟩, y, hy⟩ | ⟨⟨x, hx⟩, y, hy, hyn⟩)
      · exact ⟨x ++ y, ⟨x, hx, y, hy, rfl⟩, by simp [hxn]⟩
      · exact ⟨x ++ y, ⟨x, hx, y, hy, rfl⟩, by simp [hyn]⟩
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, hn⟩
      by_cases hxn : x = []
      · exact .inr ⟨⟨x, hx⟩, y, hy, by simpa [hxn] using hn⟩
      · exact .inl ⟨⟨x, hx, hxn⟩, y, hy⟩
  · rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, hL.1, hM.1, hL.2.2, hM.2.2]
    constructor
    · rintro (⟨hLi, y, hy⟩ | ⟨⟨x, hx⟩, hMi⟩)
      · refine Set.Infinite.mono ?_ ((Set.infinite_image_iff
          ((List.append_left_injective y).injOn)).2 hLi)
        rintro _ ⟨x, hx, rfl⟩
        exact Language.mem_mul.2 ⟨x, hx, y, hy, rfl⟩
      · refine Set.Infinite.mono ?_ ((Set.infinite_image_iff
          ((List.append_right_injective x).injOn)).2 hMi)
        rintro _ ⟨y, hy, rfl⟩
        exact Language.mem_mul.2 ⟨x, hx, y, hy, rfl⟩
    · intro h
      obtain ⟨hLn, hMn⟩ := hne.1 h.nonempty
      by_cases hLi : L.Infinite
      · exact .inl ⟨hLi, hMn⟩
      by_cases hMi : M.Infinite
      · exact .inr ⟨hLn, hMi⟩
      refine absurd ((Set.not_infinite.1 hLi).image2 (· ++ ·) (Set.not_infinite.1 hMi)) ?_
      rw [← Language.mul_def]
      exact h

theorem flagsOK_kstar {b : Bool × Bool × Bool} {L : Language α} (hL : FlagsOK b L) :
    FlagsOK (starFlags b) (KStar.kstar L) := by
  unfold starFlags
  have hpos : (∃ w ∈ (KStar.kstar L), w ≠ []) ↔ ∃ w ∈ L, w ≠ [] := by
    constructor
    · rintro ⟨w, hw, hn⟩
      obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.1 hw
      by_contra hc
      push Not at hc
      exact hn (List.flatten_eq_nil_iff.2 fun y hy => hc y (hS y hy))
    · rintro ⟨w, hw, hn⟩
      exact ⟨w, Language.mem_kstar.2 ⟨[w], by simp, by simpa using hw⟩, hn⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [true_iff]
    exact ⟨[], Language.nil_mem_kstar L⟩
  · rw [hL.2.1, hpos]
  · rw [hL.2.1]
    constructor
    · rintro ⟨w, hw, hn⟩
      refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (List.replicate n w).flatten)
        (fun m n hmn => ?_) fun n => Language.mem_kstar.2 ⟨List.replicate n w, rfl, fun y hy => ?_⟩
      · have h := congrArg List.length hmn
        simp only [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul] at h
        exact Nat.eq_of_mul_eq_mul_right (List.length_pos_of_ne_nil hn) h
      · rw [List.eq_of_mem_replicate hy]
        exact hw
    · intro h
      by_contra hc
      refine absurd ?_ h
      refine (Set.finite_singleton ([] : List α)).subset fun x hx => ?_
      obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.1 hx
      push Not at hc
      exact List.flatten_eq_nil_iff.2 fun y hy => hc y (hS y hy)

theorem length_flags (l : List (RegexNode α)) : (flags l).length = l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l n ih =>
      rw [flags, List.foldl_append, ← flags]
      simp [ih]

theorem flags_append_singleton (l : List (RegexNode α)) (n : RegexNode α) :
    flags (l ++ [n]) = flags l ++ [stepFlags (flags l) n] := by
  rw [flags, List.foldl_append, ← flags]
  rfl

/-- **Correctness of the flag pass.** For a list $l$ of nodes and a natural number $k$, let $f_k$
be the entry at position $k$ of the flags of $l$, or the zero flags
$(\mathrm{false}, \mathrm{false}, \mathrm{false})$ if $k$ is at least the length of $l$. Then
$f_k$ describes the language of the regular expression at node $k$ of the encoding $l$ when $k$
is less than the length of $l$, and describes the empty language otherwise. -/
theorem flagsOK_flags (l : List (RegexNode α)) :
    ∀ k, FlagsOK ((flags l).getD k zeroFlags)
      (if k < l.length then (⟨l⟩ : EncodedRegex α).regexAt k else 0).matches' := by
  induction l using List.reverseRecOn with
  | nil =>
      intro k
      have h0 : (flags ([] : List (RegexNode α))).getD k zeroFlags = zeroFlags := rfl
      simp only [h0, List.length_nil, Nat.not_lt_zero, ↓reduceIte]
      exact flagsOK_zero
  | append_singleton l n ih =>
      intro k
      rw [flags_append_singleton]
      rcases lt_trichotomy k l.length with hk | rfl | hk
      · have hk' : k < l.length + 1 := by omega
        rw [List.getD_append _ _ _ _ (by rwa [length_flags]), List.length_append,
          List.length_singleton]
        simp only [hk', ↓reduceIte, regexAt_append hk]
        simpa [hk] using ih k
      · rw [List.getD_append_right _ _ _ _ (by rw [length_flags]), length_flags, Nat.sub_self,
          List.length_append, List.length_singleton]
        simp only [Nat.lt_add_one, ↓reduceIte, List.getD_cons_zero]
        have hnode : (⟨l ++ [n]⟩ : EncodedRegex α).node l.length = n := by
          simp [node]
        have harg : ∀ i, (if i < l.length then (⟨l ++ [n]⟩ : EncodedRegex α).regexAt i
            else 0) = if i < l.length then (⟨l⟩ : EncodedRegex α).regexAt i else 0 := fun i => by
          split_ifs with hi
          exacts [regexAt_append hi, rfl]
        cases n with
        | zero => rw [regexAt_of_zero hnode]; exact flagsOK_zero
        | epsilon => rw [regexAt_of_epsilon hnode]; exact flagsOK_one
        | char a => rw [regexAt_of_char hnode]; exact flagsOK_char a
        | plus i j =>
            rw [regexAt_of_plus hnode, harg, harg, RegularExpression.matches'_add]
            exact flagsOK_add (ih i) (ih j)
        | comp i j =>
            rw [regexAt_of_comp hnode, harg, harg, RegularExpression.matches'_mul]
            exact flagsOK_mul (ih i) (ih j)
        | star i =>
            rw [regexAt_of_star hnode, harg, RegularExpression.matches'_star]
            exact flagsOK_kstar (ih i)
      · have hk' : ¬ k < l.length + 1 := by omega
        rw [List.getD_eq_default _ _ (by rw [List.length_append, length_flags]; simp; omega),
          List.length_append, List.length_singleton]
        simp only [hk', ↓reduceIte]
        exact flagsOK_zero

/-- **Infiniteness test for encoded regular expressions.** Let $e$ be an encoded regular
expression with nodes $n_0, \dots, n_{m-1}$, and let $f_0, \dots, f_{m-1}$ be the flags of all
nodes of $e$, the triples of Booleans computed in one left-to-right pass over the nodes. The
infiniteness test of $e$ is the third component of $f_{m-1}$, the flag triple of the last node
(the root); when $e$ has no nodes it is false.

The three flags of a node say whether its language is nonempty, contains a nonempty word and is
infinite, so the test returns true exactly when the language of $e$ is infinite. -/
def infiniteB (e : EncodedRegex α) : Bool :=
  ((flags e.nodes).getD (e.nodes.length - 1) zeroFlags).2.2

theorem infiniteB_iff {e : EncodedRegex α} : e.infiniteB = true ↔ e.toRegex.matches'.Infinite := by
  have h := (flagsOK_flags e.nodes (e.nodes.length - 1)).2.2
  rw [infiniteB, h, toRegex]
  rcases Nat.lt_or_ge (e.nodes.length - 1) e.nodes.length with hk | hk
  · simp only [hk, ↓reduceIte]
  · have hk' : ¬ e.nodes.length - 1 < e.nodes.length := by omega
    simp only [hk', ↓reduceIte, regexAt_of_zero (node_of_le hk)]

/-! ## The grammar of an encoded regular expression -/

/-- **Productions of a sum node.** For natural numbers $k$, $i$ and $j$, the productions of a
sum node $k$ with arguments $i$ and $j$ are the unit production $k \to i$ if $i < k$, followed
by the unit production $k \to j$ if $j < k$ (and nothing else). Nonterminals are node indices. -/
def plusRules (k i j : ℕ) : List (ℕ × List (ℕ ⊕ α)) :=
  (if i < k then [(k, [.inl i])] else []) ++ (if j < k then [(k, [.inl j])] else [])

/-- **Productions of a concatenation node.** For natural numbers $k$, $i$ and $j$, the
productions of a concatenation node $k$ with arguments $i$ and $j$ are the single production
$k \to i\,j$ (nonterminal $i$ followed by nonterminal $j$) when $i < k$ and $j < k$, and there
are none otherwise. -/
def compRules (k i j : ℕ) : List (ℕ × List (ℕ ⊕ α)) :=
  if i < k ∧ j < k then [(k, [.inl i, .inl j])] else []

/-- **Productions of a star node.** For natural numbers $k$ and $i$, the productions of a star
node $k$ with argument $i$ are $k \to \varepsilon$, followed by $k \to i\,k$ if $i < k$ (and
nothing else). Nonterminals are node indices. -/
def starRules (k i : ℕ) : List (ℕ × List (ℕ ⊕ α)) :=
  (k, []) :: (if i < k then [(k, [.inl i, .inl k])] else [])

/-- **Productions of a node.** For a natural number $k$ and a node $n$, the productions of
node $k$ are the following encoded productions, all with left-hand side $k$, where nonterminal
$i$ stands for node $i$: none if $n$ is the zero node; $k \to \varepsilon$ if $n$ is the
empty-word node; $k \to a$ if $n$ is the character $a$; if $n$ is a sum with arguments $i$ and
$j$, the unit production $k \to i$ when $i < k$ and the unit production $k \to j$ when
$j < k$; if $n$ is a product with arguments $i$ and $j$, the production $k \to i\,j$ when
$i < k$ and $j < k$; if $n$ is a star with argument $i$, the production $k \to \varepsilon$
together with $k \to i\,k$ when $i < k$. -/
def nodeRules (k : ℕ) : RegexNode α → List (ℕ × List (ℕ ⊕ α))
  | .zero => []
  | .epsilon => [(k, [])]
  | .char a => [(k, [.inr a])]
  | .plus i j => plusRules k i j
  | .comp i j => compRules k i j
  | .star i => starRules k i

/-- **The grammar of an encoded regular expression.** For an encoded regular expression $e$ with
$n$ nodes, its grammar is the encoded context-free grammar with start nonterminal $n - 1$
(truncated subtraction, so $0$ when $n = 0$), in which nonterminal $k$ stands for node $k$. Its
productions are, for each node $k < n$: none if node $k$ is $0$; $k \to \varepsilon$ if it is
$\varepsilon$; if it is the letter $a$, the production $k \to a$; if it is the sum of nodes $i$
and $j$, the productions $k \to i$ (when $i < k$) and $k \to j$ (when $j < k$); if it is the
product of nodes $i$ and $j$, the production $k \to i\,j$ (when $i < k$ and $j < k$); and if it
is the star of node $i$, the productions $k \to \varepsilon$ and $k \to i\,k$ (when $i < k$).
There are no other productions. -/
def toGrammar (e : EncodedRegex α) : EncodedCFG α :=
  ⟨e.nodes.length - 1, (List.range e.nodes.length).flatMap fun k => nodeRules k (e.node k)⟩

theorem fst_of_mem_nodeRules {k : ℕ} {n : RegexNode α} {x : ℕ × List (ℕ ⊕ α)}
    (hx : x ∈ nodeRules k n) : x.1 = k := by
  cases n with
  | zero => simp [nodeRules] at hx
  | epsilon | char a =>
      simp only [nodeRules, List.mem_singleton] at hx
      rw [hx]
  | plus i j =>
      simp only [nodeRules, plusRules, List.mem_append] at hx
      rcases hx with hx | hx <;> split_ifs at hx <;> simp_all
  | comp i j =>
      simp only [nodeRules, compRules] at hx
      split_ifs at hx <;> simp_all
  | star i =>
      simp only [nodeRules, starRules, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · split_ifs at hx <;> simp_all

theorem mem_rules_iff {e : EncodedRegex α} {k : ℕ} {x : ℕ × List (ℕ ⊕ α)} :
    x ∈ e.toGrammar.rules ∧ x.1 = k ↔ x ∈ nodeRules k (e.node k) := by
  simp only [toGrammar, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨⟨k', -, hx⟩, rfl⟩
    rwa [fst_of_mem_nodeRules hx]
  · intro hx
    refine ⟨⟨k, ?_, hx⟩, fst_of_mem_nodeRules hx⟩
    by_contra hk
    rw [node_of_le (not_lt.1 hk)] at hx
    simp [nodeRules] at hx

/-- **Language of a sentential form.** For an encoded regular expression $e$, the language of a
sentential form $X_1 \cdots X_n$ (terminals in $\alpha$, nonterminals in $\mathbb{N}$) is the
product $L_1 \cdots L_n$, where $L_i$ is $\{a\}$, the language of the one-letter word $a$, when
$X_i$ is the terminal $a$, and the language of the regular expression at node $k$ of $e$ when
$X_i$ is the nonterminal $k$. The empty form has language $\{\varepsilon\}$. -/
def formLang (e : EncodedRegex α) : List (Symbol α ℕ) → Language α
  | [] => 1
  | .terminal a :: u => {[a]} * e.formLang u
  | .nonterminal k :: u => (e.regexAt k).matches' * e.formLang u

theorem mem_formLang_one {e : EncodedRegex α} {k : ℕ} {w : List α} :
    w ∈ e.formLang [.nonterminal k] ↔ w ∈ (e.regexAt k).matches' := by
  simp [formLang]

theorem mem_formLang_two {e : EncodedRegex α} {i j : ℕ} {w : List α} :
    w ∈ e.formLang [.nonterminal i, .nonterminal j] ↔
      w ∈ (e.regexAt i).matches' * (e.regexAt j).matches' := by
  simp [formLang]

/-- **A production of a node only produces words of its language.** Let $e$ be an encoded
regular expression, $k$ a natural number and $x$ one of the productions of node $k$ built from
the node of $e$ at index $k$. If a word $w$ belongs to the language of the right-hand side of
$x$ (the concatenation, over its symbols, of $\{a\}$ for a terminal $a$ and of the language of
the regular expression at node $i$ for a nonterminal $i$), then $w$ belongs to the language of
the regular expression at node $k$. -/
theorem mem_matches_of_mem_nodeRules {e : EncodedRegex α} {k : ℕ} {x : ℕ × List (ℕ ⊕ α)}
    {w : List α} (hx : x ∈ nodeRules k (e.node k))
    (hw : w ∈ e.formLang (x.2.map EncodedCFG.decodeSymbol)) : w ∈ (e.regexAt k).matches' := by
  cases h : e.node k with
  | zero =>
      rw [h] at hx
      simp [nodeRules] at hx
  | epsilon =>
      rw [h] at hx
      simp only [nodeRules, List.mem_singleton] at hx
      subst hx
      rw [regexAt_of_epsilon h]
      simpa [formLang] using hw
  | char a =>
      rw [h] at hx
      simp only [nodeRules, List.mem_singleton] at hx
      subst hx
      rw [regexAt_of_char h]
      simpa [formLang, EncodedCFG.decodeSymbol] using hw
  | plus i j =>
      rw [h] at hx
      rw [regexAt_of_plus h, RegularExpression.matches'_add, Language.mem_add]
      simp only [nodeRules, plusRules, List.mem_append] at hx
      rcases hx with hx | hx
      · split_ifs at hx with hi
        · simp only [List.mem_singleton] at hx
          subst hx
          left
          rw [ite_eq_left hi]
          exact mem_formLang_one.1 hw
        · simp at hx
      · split_ifs at hx with hj
        · simp only [List.mem_singleton] at hx
          subst hx
          right
          rw [ite_eq_left hj]
          exact mem_formLang_one.1 hw
        · simp at hx
  | comp i j =>
      rw [h] at hx
      rw [regexAt_of_comp h, RegularExpression.matches'_mul]
      simp only [nodeRules, compRules] at hx
      split_ifs at hx with hij
      · simp only [List.mem_singleton] at hx
        subst hx
        rw [ite_eq_left hij.1, ite_eq_left hij.2]
        exact mem_formLang_two.1 hw
      · simp at hx
  | star i =>
      rw [h] at hx
      rw [regexAt_of_star h, RegularExpression.matches'_star]
      simp only [nodeRules, starRules, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp only [List.map_nil, formLang, Language.mem_one] at hw
        subst hw
        exact Language.nil_mem_kstar _
      · split_ifs at hx with hi
        · simp only [List.mem_singleton] at hx
          subst hx
          rw [ite_eq_left hi]
          obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.1 (mem_formLang_two.1 hw)
          rw [regexAt_of_star h, ite_eq_left hi, RegularExpression.matches'_star] at hv
          obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.1 hv
          rw [← List.flatten_cons]
          exact Language.join_mem_kstar fun y hy => by
            rcases List.mem_cons.1 hy with rfl | hy
            · exact hu
            · exact hL y hy
        · simp at hx

variable [DecidableEq α]

theorem yields_singleton_iff {e : EncodedRegex α} {k : ℕ} {w : List α} :
    Yields e.toGrammar.toCFG [.nonterminal k] w ↔
      ∃ x ∈ nodeRules k (e.node k),
        Yields e.toGrammar.toCFG (x.2.map EncodedCFG.decodeSymbol) w := by
  rw [yields_nonterminal_singleton_iff]
  constructor
  · rintro ⟨r, hr, hk, hw⟩
    obtain ⟨x, hx, rfl⟩ := EncodedCFG.mem_toCFG_rules.1 hr
    exact ⟨x, mem_rules_iff.1 ⟨hx, hk⟩, hw⟩
  · rintro ⟨x, hx, hw⟩
    obtain ⟨hx', hk⟩ := mem_rules_iff.2 hx
    exact ⟨EncodedCFG.decodeRule x, EncodedCFG.mem_toCFG_rules.2 ⟨x, hx', rfl⟩, hk, hw⟩

/-- **Soundness of the grammar of a regular expression.** Let $e$ be an encoded regular
expression. If a sentential form $u$ of the context-free grammar of $e$ yields a terminal word
$w$, then $w$ belongs to the language of $u$: the concatenation, over the symbols of $u$, of
$\{a\}$ for a terminal $a$ and of the language of the regular expression at node $k$ for a
nonterminal $k$. -/
theorem mem_formLang_of_yields {e : EncodedRegex α} {u : List (Symbol α e.toGrammar.toCFG.NT)}
    {w : List α}
    (h : Yields e.toGrammar.toCFG u w) : w ∈ e.formLang u := by
  induction h with
  | nil => exact (Language.mem_one _).2 rfl
  | terminal a _ ih => exact Language.mem_mul.2 ⟨[a], rfl, _, ih, rfl⟩
  | nonterminal hr _ _ ihout ihrest =>
      refine Language.mem_mul.2 ⟨_, ?_, _, ihrest, rfl⟩
      obtain ⟨x, hx, rfl⟩ := EncodedCFG.mem_toCFG_rules.1 hr
      exact mem_matches_of_mem_nodeRules (mem_rules_iff.1 ⟨hx, rfl⟩) ihout

/-- **Completeness of the grammar of an encoded regular expression.** Let $\alpha$ be an alphabet
with decidable equality, $e$ an encoded regular expression over $\alpha$ and $k$ a natural number.
Every word in the language of the regular expression at node $k$ of $e$ is yielded by the
sentential form consisting of the single nonterminal $k$ in the context-free grammar of $e$. -/
theorem yields_of_mem_matches {e : EncodedRegex α} :
    ∀ k {w : List α}, w ∈ (e.regexAt k).matches' → Yields e.toGrammar.toCFG [.nonterminal k] w := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w hw
    cases h : e.node k with
    | zero =>
        rw [regexAt_of_zero h, RegularExpression.matches'_zero] at hw
        exact absurd hw (Language.notMem_zero w)
    | epsilon =>
        rw [regexAt_of_epsilon h, RegularExpression.matches'_epsilon, Language.mem_one] at hw
        subst hw
        exact yields_singleton_iff.2 ⟨(k, []), by simp [h, nodeRules], Yields.nil⟩
    | char a =>
        rw [regexAt_of_char h, RegularExpression.matches'_char] at hw
        subst hw
        exact yields_singleton_iff.2 ⟨(k, [.inr a]), by simp [h, nodeRules],
          yields_terminal_singleton_iff.2 rfl⟩
    | plus i j =>
        rw [regexAt_of_plus h, RegularExpression.matches'_add, Language.mem_add] at hw
        rcases hw with hw | hw
        · by_cases hi : i < k
          · rw [ite_eq_left hi] at hw
            exact yields_singleton_iff.2 ⟨(k, [.inl i]), by simp [h, nodeRules, plusRules, hi],
              ih i hi hw⟩
          · rw [ite_eq_right hi, RegularExpression.matches'_zero] at hw
            exact absurd hw (Language.notMem_zero w)
        · by_cases hj : j < k
          · rw [ite_eq_left hj] at hw
            exact yields_singleton_iff.2 ⟨(k, [.inl j]), by simp [h, nodeRules, plusRules, hj],
              ih j hj hw⟩
          · rw [ite_eq_right hj, RegularExpression.matches'_zero] at hw
            exact absurd hw (Language.notMem_zero w)
    | comp i j =>
        rw [regexAt_of_comp h, RegularExpression.matches'_mul] at hw
        obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.1 hw
        by_cases hi : i < k
        · by_cases hj : j < k
          · rw [ite_eq_left hi] at hu
            rw [ite_eq_left hj] at hv
            exact yields_singleton_iff.2 ⟨(k, [.inl i, .inl j]),
              by simp [h, nodeRules, compRules, hi, hj],
              yields_pair_iff.2 ⟨u, v, rfl, ih i hi hu, ih j hj hv⟩⟩
          · rw [ite_eq_right hj, RegularExpression.matches'_zero] at hv
            exact absurd hv (Language.notMem_zero v)
        · rw [ite_eq_right hi, RegularExpression.matches'_zero] at hu
          exact absurd hu (Language.notMem_zero u)
    | star i =>
        rw [regexAt_of_star h, RegularExpression.matches'_star] at hw
        obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.1 hw
        induction L with
        | nil => exact yields_singleton_iff.2 ⟨(k, []), by simp [h, nodeRules, starRules],
            Yields.nil⟩
        | cons y L ihL =>
            have hy := hL y List.mem_cons_self
            by_cases hi : i < k
            · rw [ite_eq_left hi] at hy
              rw [List.flatten_cons]
              exact yields_singleton_iff.2 ⟨(k, [.inl i, .inl k]),
                by simp [h, nodeRules, starRules, hi],
                yields_pair_iff.2 ⟨y, L.flatten, rfl, ih i hi hy,
                  ihL (fun z hz => hL z (List.mem_cons_of_mem _ hz))
                    (Language.join_mem_kstar fun z hz => hL z (List.mem_cons_of_mem _ hz))⟩⟩
            · rw [ite_eq_right hi, RegularExpression.matches'_zero] at hy
              exact absurd hy (Language.notMem_zero y)

theorem yields_iff_mem_matches {e : EncodedRegex α} {k : ℕ} {w : List α} :
    Yields e.toGrammar.toCFG [.nonterminal k] w ↔ w ∈ (e.regexAt k).matches' :=
  ⟨fun h => mem_formLang_one.1 (mem_formLang_of_yields h), yields_of_mem_matches k⟩

/-- **The grammar generates the language of the expression.** For every encoded regular
expression $e$, the language of the context-free grammar of $e$ (one nonterminal per node, the
root as start symbol) equals the language of the regular expression that $e$ denotes. -/
theorem language_toGrammar (e : EncodedRegex α) : e.toGrammar.language = e.toRegex.matches' := by
  ext w
  rw [EncodedCFG.language, mem_language_iff_yields]
  exact yields_iff_mem_matches

/-- **Membership test for regular expressions.** For an encoded regular expression $e$ and a
word $w$, the test returns the answer of the membership test for encoded context-free grammars
on the word $w$ and the grammar of $e$, which has one nonterminal per node and the root as
start symbol. -/
def memB (e : EncodedRegex α) (w : List α) : Bool :=
  e.toGrammar.memLanguageB w

theorem memB_iff {e : EncodedRegex α} {w : List α} : e.memB w = true ↔ w ∈ e.toRegex.matches' := by
  rw [memB, EncodedCFG.memLanguageB_iff, language_toGrammar]

/-- **Emptiness test for regular expressions.** For an encoded regular expression $e$, the test
returns the answer of the emptiness test for encoded context-free grammars on the grammar of
$e$, which has one nonterminal per node and the root as start symbol. -/
def isEmptyB (e : EncodedRegex α) : Bool :=
  e.toGrammar.isEmptyB

omit [DecidableEq α] in
theorem isEmptyB_iff {e : EncodedRegex α} : e.isEmptyB = true ↔ e.toRegex.matches' = 0 := by
  classical
  rw [isEmptyB, EncodedCFG.isEmptyB_iff, language_toGrammar]

/-- **Inclusion test.** For an encoded regular expression $e$ and an encoded DFA $D$, the
inclusion test returns the Boolean computed by the CFG ⊆ DFA inclusion test on the grammar of
$e$ and the automaton $D$. -/
def subsetB (e : EncodedRegex α) (D : Cslib.Automata.EncodedDFA α) : Bool :=
  EncodedCFG.subsetB e.toGrammar D

theorem subsetB_iff {e : EncodedRegex α} {D : Cslib.Automata.EncodedDFA α} :
    e.subsetB D = true ↔ e.toRegex.matches' ≤ D.language := by
  rw [subsetB, EncodedCFG.subsetB_iff, language_toGrammar]

/-! ## Computability -/

section Computable

/-- **Regex nodes as a sum type.** The bijection between the nodes of encoded regular
expressions over $\alpha$ and $1 \oplus 1 \oplus \alpha \oplus (\mathbb{N} \times \mathbb{N}) \oplus
(\mathbb{N} \times \mathbb{N}) \oplus \mathbb{N}$, where $1$ is the one-point type, that sends the
zero node and the empty-word node to the first and second copies of $1$, a character node $a$
to $a$, a sum node with arguments $i, j$ to $(i, j)$ in the first copy of
$\mathbb{N} \times \mathbb{N}$, a product node with arguments $i, j$ to $(i, j)$ in the second,
and a star node with argument $i$ to $i$. -/
def nodeEquiv : RegexNode α ≃ Unit ⊕ Unit ⊕ α ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ where
  toFun
    | .zero => .inl ()
    | .epsilon => .inr (.inl ())
    | .char a => .inr (.inr (.inl a))
    | .plus i j => .inr (.inr (.inr (.inl (i, j))))
    | .comp i j => .inr (.inr (.inr (.inr (.inl (i, j)))))
    | .star i => .inr (.inr (.inr (.inr (.inr i))))
  invFun
    | .inl _ => .zero
    | .inr (.inl _) => .epsilon
    | .inr (.inr (.inl a)) => .char a
    | .inr (.inr (.inr (.inl p))) => .plus p.1 p.2
    | .inr (.inr (.inr (.inr (.inl p)))) => .comp p.1 p.2
    | .inr (.inr (.inr (.inr (.inr i)))) => .star i
  left_inv n := by cases n <;> rfl
  right_inv s := by rcases s with _ | _ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ <;> rfl

/-- **Encodings are lists of nodes.** The map sending an encoded regular expression over $\alpha$
to its list of nodes is a bijection onto the lists of regular-expression nodes over $\alpha$; its
inverse wraps a list of nodes as an encoding. -/
def equivList : EncodedRegex α ≃ List (RegexNode α) where
  toFun e := e.nodes
  invFun l := ⟨l⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Primcodable α]

instance instPrimcodableNode : Primcodable (RegexNode α) :=
  Primcodable.ofEquiv _ nodeEquiv

instance instPrimcodable : Primcodable (EncodedRegex α) :=
  Primcodable.ofEquiv _ equivList

omit [DecidableEq α] in
theorem primrec_nodes : Primrec (nodes (α := α)) :=
  Primrec.of_equiv (e := equivList)

omit [DecidableEq α] in
theorem primrec_node : Primrec₂ (node (α := α)) :=
  ((Primrec.list_getD (RegexNode.zero : RegexNode α)).comp (primrec_nodes.comp Primrec.fst)
    Primrec.snd).of_eq fun _ => rfl

omit [DecidableEq α] in
theorem primrec_plusRules :
    Primrec fun p : ℕ × ℕ × ℕ => plusRules (α := α) p.1 p.2.1 p.2.2 := by
  have hk : Primrec fun p : ℕ × ℕ × ℕ => p.1 := Primrec.fst
  have hi : Primrec fun p : ℕ × ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hj : Primrec fun p : ℕ × ℕ × ℕ => p.2.2 := Primrec.snd.comp Primrec.snd
  have unit : ∀ {f : ℕ × ℕ × ℕ → ℕ}, Primrec f →
      Primrec fun p : ℕ × ℕ × ℕ => if f p < p.1 then [(p.1, [(.inl (f p) : ℕ ⊕ α)])] else [] :=
    fun hf => Primrec.ite (Primrec.nat_lt.comp hf hk)
      (Primrec.list_cons.comp (Primrec.pair hk (Primrec.list_cons.comp (Primrec.sumInl.comp hf)
        (Primrec.const []))) (Primrec.const [])) (Primrec.const [])
  exact Primrec.list_append.comp (unit hi) (unit hj)

omit [DecidableEq α] in
theorem primrec_compRules :
    Primrec fun p : ℕ × ℕ × ℕ => compRules (α := α) p.1 p.2.1 p.2.2 := by
  have hk : Primrec fun p : ℕ × ℕ × ℕ => p.1 := Primrec.fst
  have hi : Primrec fun p : ℕ × ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hj : Primrec fun p : ℕ × ℕ × ℕ => p.2.2 := Primrec.snd.comp Primrec.snd
  exact Primrec.ite ((Primrec.nat_lt.comp hi hk).and (Primrec.nat_lt.comp hj hk))
    (Primrec.list_cons.comp (Primrec.pair hk (Primrec.list_cons.comp (Primrec.sumInl.comp hi)
      (Primrec.list_cons.comp (Primrec.sumInl.comp hj) (Primrec.const [])))) (Primrec.const []))
    (Primrec.const [])

omit [DecidableEq α] in
theorem primrec_starRules : Primrec₂ (starRules (α := α)) := by
  have hk : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have hi : Primrec fun p : ℕ × ℕ => p.2 := Primrec.snd
  exact Primrec.list_cons.comp (Primrec.pair hk (Primrec.const []))
    (Primrec.ite (Primrec.nat_lt.comp hi hk)
      (Primrec.list_cons.comp (Primrec.pair hk (Primrec.list_cons.comp (Primrec.sumInl.comp hi)
        (Primrec.list_cons.comp (Primrec.sumInl.comp hk) (Primrec.const []))))
        (Primrec.const []))
      (Primrec.const []))

omit [DecidableEq α] in
theorem primrec_nodeRules : Primrec₂ (nodeRules (α := α)) := by
  have k₂ : ∀ {β γ : Type _} [Primcodable β] [Primcodable γ],
      Primrec fun q : (ℕ × β) × γ => q.1.1 := Primrec.fst.comp Primrec.fst
  have h5 : Primrec₂ fun (k : ℕ) (s : (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun p => compRules (α := α) k p.1 p.2) (starRules k) s :=
    (Primrec.sumCasesOn Primrec.snd
      (primrec_compRules.comp (Primrec.pair k₂ Primrec.snd)).to₂
      (primrec_starRules.comp k₂ Primrec.snd).to₂).of_eq fun p => by
        rcases p with ⟨k, _ | _⟩ <;> rfl
  have h4 : Primrec₂ fun (k : ℕ) (s : (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun p => plusRules (α := α) k p.1 p.2)
        (Sum.elim (fun p => compRules k p.1 p.2) (starRules k)) s :=
    (Primrec.sumCasesOn Primrec.snd
      (primrec_plusRules.comp (Primrec.pair k₂ Primrec.snd)).to₂
      (h5.comp k₂ Primrec.snd).to₂).of_eq fun p => by
        rcases p with ⟨k, _ | _⟩ <;> rfl
  have h3 : Primrec₂ fun (k : ℕ) (s : α ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun a => [(k, [(.inr a : ℕ ⊕ α)])])
        (Sum.elim (fun p => plusRules k p.1 p.2)
          (Sum.elim (fun p => compRules k p.1 p.2) (starRules k))) s :=
    (Primrec.sumCasesOn Primrec.snd
      (Primrec.list_cons.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.sumInr.comp Primrec.snd) (Primrec.const [])))
        (Primrec.const [])).to₂
      (h4.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun p => by
        rcases p with ⟨k, _ | _⟩ <;> rfl
  have h2 : Primrec₂ fun (k : ℕ) (s : Unit ⊕ α ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun _ => [(k, ([] : List (ℕ ⊕ α)))])
        (Sum.elim (fun a => [(k, [(.inr a : ℕ ⊕ α)])])
          (Sum.elim (fun p => plusRules k p.1 p.2)
            (Sum.elim (fun p => compRules k p.1 p.2) (starRules k)))) s :=
    (Primrec.sumCasesOn Primrec.snd
      (Primrec.list_cons.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.const []))
        (Primrec.const [])).to₂
      (h3.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun p => by
        rcases p with ⟨k, _ | _⟩ <;> rfl
  have he : Primrec (nodeEquiv (α := α)) := Primrec.of_equiv
  exact (Primrec.sumCasesOn (he.comp Primrec.snd) (Primrec₂.const [])
    (h2.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun p => by
      obtain ⟨k, n⟩ := p
      cases n <;> rfl

omit [DecidableEq α] in
theorem primrec_toGrammar : Primrec (toGrammar (α := α)) :=
  EncodedCFG.primrec₂_mk.comp (Primrec.pred.comp (Primrec.list_length.comp primrec_nodes))
    (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp primrec_nodes))
      (primrec_nodeRules.comp Primrec.snd (primrec_node.comp Primrec.fst Primrec.snd)).to₂)

theorem primrec_memB : Primrec₂ (memB (α := α)) :=
  EncodedCFG.primrec_memLanguageB.comp (primrec_toGrammar.comp Primrec.fst) Primrec.snd

omit [DecidableEq α] in
/-- **Membership for regular expressions is decidable.** Let $\alpha$ be an alphabet with a
primitive recursive coding by natural numbers. The set of pairs $(e, w)$ of an encoded regular
expression $e$ over $\alpha$ and a word $w$ over $\alpha$ such that $w$ belongs to the language of
the regular expression denoted by $e$ is decidable by a multi-stack machine.

Source: Sipser, Introduction to the Theory of Computation, Theorem 4.3 ($A_{\mathsf{REX}}$). -/
theorem tm2Decidable_mem_matches :
    TM2Decidable fun p : EncodedRegex α × List α => p.2 ∈ p.1.toRegex.matches' := by
  classical
  exact tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_memB fun _ => memB_iff)

omit [DecidableEq α] in
theorem primrec_isEmptyB : Primrec (isEmptyB (α := α)) :=
  EncodedCFG.primrec_isEmptyB.comp primrec_toGrammar

omit [DecidableEq α] in
/-- **Emptiness of regular expressions is decidable.** For an alphabet $\alpha$ with a primitive
recursive encoding, the property of an encoded regular expression over $\alpha$ that the
language it denotes is empty (E_REX) is decidable by a multi-stack machine. -/
theorem tm2Decidable_matches_eq_zero :
    TM2Decidable fun e : EncodedRegex α => e.toRegex.matches' = 0 := by
  classical
  exact tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_isEmptyB fun _ => isEmptyB_iff)

omit [DecidableEq α] in
theorem primrec_plusFlags : Primrec₂ plusFlags :=
  Primrec.pair (Primrec.or.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.pair
      (Primrec.or.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.or.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

omit [DecidableEq α] in
theorem primrec_compFlags : Primrec₂ compFlags := by
  have b1 : Primrec fun p : (Bool × Bool × Bool) × (Bool × Bool × Bool) => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have b2 : Primrec fun p : (Bool × Bool × Bool) × (Bool × Bool × Bool) => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have b3 : Primrec fun p : (Bool × Bool × Bool) × (Bool × Bool × Bool) => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have c1 : Primrec fun p : (Bool × Bool × Bool) × (Bool × Bool × Bool) => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have c2 : Primrec fun p : (Bool × Bool × Bool) × (Bool × Bool × Bool) => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have c3 : Primrec fun p : (Bool × Bool × Bool) × (Bool × Bool × Bool) => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.pair (Primrec.and.comp b1 c1)
    (Primrec.pair (Primrec.or.comp (Primrec.and.comp b2 c1) (Primrec.and.comp b1 c2))
      (Primrec.or.comp (Primrec.and.comp b3 c1) (Primrec.and.comp b1 c3)))

omit [DecidableEq α] in
theorem primrec_starFlags : Primrec starFlags :=
  Primrec.pair (Primrec.const true)
    (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))

omit [DecidableEq α] in
theorem primrec_stepFlags : Primrec₂ (stepFlags (α := α)) := by
  have get : Primrec₂ fun (acc : List (Bool × Bool × Bool)) (i : ℕ) => acc.getD i zeroFlags :=
    Primrec.list_getD zeroFlags
  have pair₂ : ∀ {f : Bool × Bool × Bool → Bool × Bool × Bool → Bool × Bool × Bool},
      Primrec₂ f → ∀ {γ : Type _} [Primcodable γ],
      Primrec₂ fun (q : List (Bool × Bool × Bool) × γ) (p : ℕ × ℕ) =>
        f (q.1.getD p.1 zeroFlags) (q.1.getD p.2 zeroFlags) :=
    fun hf _ _ => hf.comp (get.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (get.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  have h5 : Primrec₂ fun (acc : List (Bool × Bool × Bool)) (s : (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun p => compFlags (acc.getD p.1 zeroFlags) (acc.getD p.2 zeroFlags))
        (fun i => starFlags (acc.getD i zeroFlags)) s :=
    (Primrec.sumCasesOn Primrec.snd (pair₂ primrec_compFlags)
      (primrec_starFlags.comp (get.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
      fun p => by rcases p with ⟨acc, _ | _⟩ <;> rfl
  have h4 : Primrec₂ fun (acc : List (Bool × Bool × Bool)) (s : (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun p => plusFlags (acc.getD p.1 zeroFlags) (acc.getD p.2 zeroFlags))
        (Sum.elim (fun p => compFlags (acc.getD p.1 zeroFlags) (acc.getD p.2 zeroFlags))
          (fun i => starFlags (acc.getD i zeroFlags))) s :=
    (Primrec.sumCasesOn Primrec.snd (pair₂ primrec_plusFlags)
      (h5.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
      fun p => by rcases p with ⟨acc, _ | _⟩ <;> rfl
  have h3 : Primrec₂ fun (acc : List (Bool × Bool × Bool)) (s : α ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun _ => (true, true, false))
        (Sum.elim (fun p => plusFlags (acc.getD p.1 zeroFlags) (acc.getD p.2 zeroFlags))
          (Sum.elim (fun p => compFlags (acc.getD p.1 zeroFlags) (acc.getD p.2 zeroFlags))
            (fun i => starFlags (acc.getD i zeroFlags)))) s :=
    (Primrec.sumCasesOn Primrec.snd (Primrec₂.const (true, true, false))
      (h4.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
      fun p => by rcases p with ⟨acc, _ | _⟩ <;> rfl
  have h2 : Primrec₂ fun (acc : List (Bool × Bool × Bool))
      (s : Unit ⊕ α ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun _ => (true, false, false))
        (Sum.elim (fun _ => (true, true, false))
          (Sum.elim (fun p => plusFlags (acc.getD p.1 zeroFlags) (acc.getD p.2 zeroFlags))
            (Sum.elim (fun p => compFlags (acc.getD p.1 zeroFlags) (acc.getD p.2 zeroFlags))
              (fun i => starFlags (acc.getD i zeroFlags))))) s :=
    (Primrec.sumCasesOn Primrec.snd (Primrec₂.const (true, false, false))
      (h3.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
      fun p => by rcases p with ⟨acc, _ | _⟩ <;> rfl
  have he : Primrec (nodeEquiv (α := α)) := Primrec.of_equiv
  exact (Primrec.sumCasesOn (he.comp Primrec.snd) (Primrec₂.const zeroFlags)
    (h2.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun p => by
      obtain ⟨acc, n⟩ := p
      cases n <;> rfl

omit [DecidableEq α] in
theorem primrec_flags : Primrec (flags (α := α)) :=
  (Primrec.list_foldl Primrec.id (Primrec.const [])
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (primrec_stepFlags.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) (Primrec.const []))).to₂).of_eq fun _ => rfl

omit [DecidableEq α] in
theorem primrec_infiniteB : Primrec (infiniteB (α := α)) :=
  (Primrec.snd.comp (Primrec.snd.comp ((Primrec.list_getD zeroFlags).comp
    (primrec_flags.comp primrec_nodes)
    (Primrec.pred.comp (Primrec.list_length.comp primrec_nodes))))).of_eq fun e => by
      simp only [infiniteB, Nat.pred_eq_sub_one]

theorem primrec_subsetB : Primrec₂ (subsetB (α := α)) :=
  EncodedCFG.primrec_subsetB.comp (primrec_toGrammar.comp Primrec.fst) Primrec.snd

omit [DecidableEq α] in
/-- **Infiniteness of regular expressions is decidable.** For an alphabet $\alpha$ with a
primitive recursive encoding, the property of an encoded regular expression over $\alpha$ that
the language it denotes is infinite is decidable by a multi-stack machine. -/
theorem tm2Decidable_matches_infinite :
    TM2Decidable fun e : EncodedRegex α => e.toRegex.matches'.Infinite := by
  classical
  exact tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_infiniteB fun _ => infiniteB_iff)

/-- **Inclusion of a regular language in a DFA language is decidable.** Let $\alpha$ be an
alphabet with decidable equality and a primitive recursive coding by natural numbers. The set of
pairs $(e, D)$ of an encoded regular expression $e$ over $\alpha$ and an encoded DFA $D$ over
$\alpha$ such that the language of the regular expression denoted by $e$ is contained in the
language of $D$ is decidable by a multi-stack machine. -/
theorem tm2Decidable_matches_le :
    TM2Decidable fun p : EncodedRegex α × Cslib.Automata.EncodedDFA α =>
      p.1.toRegex.matches' ≤ p.2.language :=
  tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_subsetB fun _ => subsetB_iff)

end Computable

end EncodedRegex

end Cslib.Language
