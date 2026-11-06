/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Relation
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Keyword substitutions on binary words and partial sums of `m`-step Fibonacci numbers

Statements from Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav
Sood, *A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci
Numbers*, Journal of Integer Sequences 28 (2025), Article 25.6.6 (arXiv
`2503.11055v1`, Sections 2.1 and 3.2 for the definitions).

Conventions.

* A binary word of length `n` is `u : Fin n → Bool`; a keyword is
  `a : Fin (m + 1) → Bool`, and `!a` is its letterwise negation.
* Letter positions are `0`-indexed: the paper's simple map `φ_i` (`i ≥ 1`) is
  `keywordSimpleMap a (i - 1)`, and the paper's interval `⟦1, n⟧` of indices is `Fin n`.
* The `m`-step Fibonacci numbers enter as a function `F : ℕ → ℕ` with the paper's
  defining conditions `F 0 = 1`, `F k = 2 ^ (k - 1)` for `1 ≤ k ≤ m - 1`, and
  `F k = F (k - 1) + ⋯ + F (k - m)` for `k ≥ m`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Applicability of a keyword.** Let $a = a_0 a_1 \cdots a_m$ be a binary keyword of length
$m + 1$ and $u = u_0 u_1 \cdots u_{n-1}$ a binary word of length $n$. The keyword $a$ is
applicable to $u$ at the ($0$-indexed) letter $i$ when $i + m < n$ and the subword
$u_i u_{i+1} \cdots u_{i+m}$ of $u$ equals $a$ or the letterwise negation of $a$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Section 2.1 (definition of
substitutions involving the keyword). -/
def KeywordApplicable {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ) (u : Fin n → Bool) :
    Prop :=
  ∃ h : i + m < n,
    (∀ t : Fin (m + 1), u ⟨i + t, by have := t.isLt; omega⟩ = a t) ∨
      (∀ t : Fin (m + 1), u ⟨i + t, by have := t.isLt; omega⟩ = !a t)

open Classical in
/-- **Simple map.** Let $a$ be a keyword, a binary word of length $m + 1$, and let
$i \in \mathbb{N}$. The simple map $\varphi_i$ sends a binary word $u$ of length $n$ to the word
obtained by negating the letters of $u$ at positions $i, \dots, i + m$ (positions counted from
$0$) if $a$ is applicable to $u$ at letter $i$, that is, if $i + m < n$ and the subword of $u$ at
positions $i, \dots, i + m$ equals $a$ or its letterwise negation $\neg a$; otherwise
$\varphi_i(u) = u$.

The paper counts letters from $1$, so its simple map $\varphi_i$ is $\varphi_{i-1}$ in this
numbering.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Section 2.1 (simple maps). -/
noncomputable def keywordSimpleMap {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ)
    (u : Fin n → Bool) : Fin n → Bool :=
  if KeywordApplicable a i u then
    fun j => if i ≤ j.val ∧ j.val ≤ i + m then !u j else u j
  else u

/-- **A simple map that is not applicable is the identity.** Let $a$ be a keyword and $u$ a binary
word. If $a$ is not applicable to $u$ at letter $i$, then the simple map $\varphi_i$ of $a$ leaves
$u$ unchanged: $\varphi_i(u) = u$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Section 2.1 (simple maps). -/
theorem keywordSimpleMap_of_not_applicable {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ)
    (u : Fin n → Bool) (h : ¬ KeywordApplicable a i u) : keywordSimpleMap a i u = u := by
  simp [keywordSimpleMap, h]

/-- **An applicable simple map negates its window.** Let $a$ be a keyword of length $m + 1$ and $u$
a binary word of length $n$, and suppose that $a$ is applicable to $u$ at letter $i$. Then the
simple map $\varphi_i$ of $a$ negates the letters of $u$ at positions $i, \dots, i + m$ and leaves
every other letter unchanged: for every position $j$, $\varphi_i(u)_j = \neg u_j$ if
$i \le j \le i + m$, and $\varphi_i(u)_j = u_j$ otherwise.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Section 2.1 (simple maps). -/
theorem keywordSimpleMap_apply_of_applicable {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ)
    (u : Fin n → Bool) (h : KeywordApplicable a i u) (j : Fin n) :
    keywordSimpleMap a i u j = if i ≤ j.val ∧ j.val ≤ i + m then !u j else u j := by
  simp [keywordSimpleMap, h]

/-- **Keyword equivalence of binary words.** Let $a$ be a binary keyword of length $m + 1$.
Two binary words $u$ and $v$ of length $n$ satisfy $u \sim_a v$ when some finite composition
of simple maps of $a$, possibly the empty composition, sends $u$ to $v$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.1 (equivalence relation induced by the keyword). -/
def KeywordEquiv {m n : ℕ} (a : Fin (m + 1) → Bool) : (Fin n → Bool) → (Fin n → Bool) → Prop :=
  Relation.ReflTransGen fun u v => ∃ i : ℕ, keywordSimpleMap a i u = v

/-- **Reflexivity of keyword equivalence.** For every binary keyword $a$ and every binary word
$u$, we have $u \sim_a u$: the empty composition of simple maps sends $u$ to itself.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.1 (equivalence relation induced by the keyword). -/
theorem keywordEquiv_refl {m n : ℕ} (a : Fin (m + 1) → Bool) (u : Fin n → Bool) :
    KeywordEquiv a u u :=
  Relation.ReflTransGen.refl

/-- **Substitution graph.** Let $a$ be a keyword, a binary word of length $m + 1$, and let
$n \ge 0$. The substitution graph $\mathcal{G}_n^{(a)}$ is the simple graph on the binary words of
length $n$ in which distinct words $u$ and $v$ are adjacent when $\varphi_i(u) = v$ or
$\varphi_i(v) = u$ for some $i \in \mathbb{N}$, where $\varphi_i$ is the simple map of $a$ at
letter $i$. Equivalently, $u$ and $v$ are adjacent when one is obtained from the other by
replacing an occurrence of $a$ by $\neg a$ or an occurrence of $\neg a$ by $a$, where $\neg a$ is
the letterwise negation of $a$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 3.2 (graph structure within equivalence classes). -/
def keywordGraph {m : ℕ} (a : Fin (m + 1) → Bool) (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel fun u v => ∃ i : ℕ, keywordSimpleMap a i u = v

/-- **Adjacency in the keyword substitution graph.** Let $a$ be a binary keyword and let $u$
and $v$ be binary words of length $n$. Then $u$ and $v$ are adjacent in the graph
$\mathcal{G}_n^{(a)}$ if and only if $u \ne v$ and some simple map $\varphi_i$ of $a$ sends $u$
to $v$ or sends $v$ to $u$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 3.2 (graph structure within equivalence classes). -/
theorem keywordGraph_adj {m n : ℕ} (a : Fin (m + 1) → Bool) (u v : Fin n → Bool) :
    (keywordGraph a n).Adj u v ↔
      u ≠ v ∧ ((∃ i : ℕ, keywordSimpleMap a i u = v) ∨ ∃ i : ℕ, keywordSimpleMap a i v = u) :=
  SimpleGraph.fromRel_adj _ _ _

/-- **Action of a list of simple maps.** Let $a$ be a keyword and, for $j \in \mathbb{N}$, let
$\varphi_j$ be the simple map of $a$ at letter $j$. A list $[j_1, \dots, j_r]$ of natural numbers
acts on a binary word $u$ of length $n$ by
$u \mapsto \varphi_{j_r}(\cdots(\varphi_{j_1}(u))\cdots)$: the head of the list acts first, and
the empty list acts as the identity.

The paper writes this list as $(\varphi_{j_r}, \dots, \varphi_{j_1})$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.2 (action by lists of simple maps). -/
noncomputable def keywordListApply {m n : ℕ} (a : Fin (m + 1) → Bool) :
    List ℕ → (Fin n → Bool) → Fin n → Bool
  | [], u => u
  | j :: l, u => keywordListApply a l (keywordSimpleMap a j u)

/-- **Lists of simple maps acting completely.** Let $a$ be a binary keyword and $u$ a binary
word. A list $[j_1, \dots, j_r]$ of indices acts completely on $u$ when applying the simple maps
$\varphi_{j_1}, \varphi_{j_2}, \dots, \varphi_{j_r}$ of $a$ in this order changes the word at
every step: with $u_0 = u$ and $u_q = \varphi_{j_q}(u_{q-1})$, we have $u_q \ne u_{q-1}$ for
$1 \le q \le r$. In particular the empty list acts completely on every word.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.2 (action by lists of simple maps). -/
def KeywordActsCompletely {m n : ℕ} (a : Fin (m + 1) → Bool) :
    List ℕ → (Fin n → Bool) → Prop
  | [], _ => True
  | j :: l, u => keywordSimpleMap a j u ≠ u ∧ KeywordActsCompletely a l (keywordSimpleMap a j u)

/-- **The empty list of simple maps acts trivially.** For every keyword $a$ and every binary word
$u$, applying the empty list of simple maps of $a$ to $u$ returns $u$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.2 (action by lists of simple maps). -/
theorem keywordListApply_nil {m n : ℕ} (a : Fin (m + 1) → Bool) (u : Fin n → Bool) :
    keywordListApply a [] u = u := rfl

/-- **Complete action of a one-element list.** For a binary keyword $a$, an index $j$ and a
binary word $u$, the one-element list $[j]$ acts completely on $u$ if and only if the simple map
$\varphi_j$ of $a$ changes $u$, that is, $\varphi_j(u) \ne u$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.2 (action by lists of simple maps). -/
theorem keywordActsCompletely_singleton {m n : ℕ} (a : Fin (m + 1) → Bool) (j : ℕ)
    (u : Fin n → Bool) :
    KeywordActsCompletely a [j] u ↔ keywordSimpleMap a j u ≠ u := by
  simp [KeywordActsCompletely]

/-- **Keyword classes are counted by partial sums of $m$-step Fibonacci numbers.** Let
$m, n \ge 1$ and let $F_0, F_1, F_2, \dots$ be the $m$-step Fibonacci numbers: $F_0 = 1$,
$F_k = 2^{k-1}$ for $1 \le k \le m - 1$, and $F_k = F_{k-1} + F_{k-2} + \dots + F_{k-m}$ for
$k \ge m$. Then for every binary keyword $a$ of length $m + 1$, the number of equivalence
classes of the relation $\sim_a$ on binary words of length $n$ is $F_0 + F_1 + \dots + F_n$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Theorem 1
(`jis-2025-25.6.6-thm-1`). -/
public theorem_wanted card_quot_keywordEquiv_eq_sum_mStepFibonacci
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (F : ℕ → ℕ) (hF0 : F 0 = 1)
    (hFinit : ∀ k, 1 ≤ k → k ≤ m - 1 → F k = 2 ^ (k - 1))
    (hFrec : ∀ k, m ≤ k → F k = ∑ t ∈ Finset.Icc 1 m, F (k - t))
    (a : Fin (m + 1) → Bool) :
    Nat.card (Quot (KeywordEquiv (n := n) a)) = ∑ j ∈ Finset.range (n + 1), F j

/-- **Keyword equivalence is stable under concatenation.** Let $a$ be a binary keyword, let $u$
and $v$ be binary words of length $n$, and let $w$ be a binary word of length $n'$. Writing $xy$
for the concatenation of words $x$ and $y$, we have $u \sim_a v$ if and only if
$uw \sim_a vw$, and $u \sim_a v$ if and only if $wu \sim_a wv$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Lemma 6
(`jis-2025-25.6.6-lem-6`). -/
public theorem_wanted keywordEquiv_append_iff {m n n' : ℕ} (a : Fin (m + 1) → Bool)
    (u v : Fin n → Bool) (w : Fin n' → Bool) :
    (KeywordEquiv a u v ↔ KeywordEquiv a (Fin.append u w) (Fin.append v w)) ∧
      (KeywordEquiv a u v ↔ KeywordEquiv a (Fin.append w u) (Fin.append w v))

/-- **Parity of the smallest index in a non-commuting list.** Let $a$ be a binary keyword of
length $m + 1$, let $n$ and $i$ be natural numbers with $i < n$, and for each index $k$ let
$\varphi_k$ be the simple map of $a$ at letter $k$ on binary words of length $n$. Let
$l = [j_1, \dots, j_r]$ be a list of indices that are all greater than $i$, and let
$\varphi_l = \varphi_{j_r} \circ \dots \circ \varphi_{j_1}$ be the map that applies
$\varphi_{j_1}$ first. Suppose that $\varphi_i \circ \varphi_l \ne \varphi_l \circ \varphi_i$
as maps on words of length $n$, and that the list $[i, j_1, \dots, j_r, i]$, applied from left
to right, acts completely on some word of length $n$ (each map in turn changes the word). Then
every entry $j$ of $l$ with $j \le j'$ for all entries $j'$ of $l$ occurs an even number of
times in $l$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Lemma 8
(`jis-2025-25.6.6-lem-8`). -/
public theorem_wanted even_count_min_of_keywordActsCompletely {m n : ℕ}
    (a : Fin (m + 1) → Bool) (i : ℕ) (hi : i < n) (l : List ℕ) (hl : ∀ j ∈ l, i < j)
    (hcomm : (fun u : Fin n → Bool => keywordSimpleMap a i (keywordListApply a l u)) ≠
      fun u => keywordListApply a l (keywordSimpleMap a i u))
    (hacts : ∃ x : Fin n → Bool, KeywordActsCompletely a (i :: (l ++ [i])) x) :
    ∀ j ∈ l, (∀ j' ∈ l, j ≤ j') → Even (l.count j)

/-- **Recurrence for partial sums of $m$-step Fibonacci numbers.** Let $m \ge 1$ and let
$F : \mathbb{N} \to \mathbb{N}$ satisfy $F(0) = 1$, $F(k) = 2^{k-1}$ for $1 \le k \le m - 1$,
and $F(k) = F(k-1) + \cdots + F(k-m)$ for $k \ge m$ (the $m$-step Fibonacci numbers). Then a
real sequence $(S_n)_{n \ge 0}$ satisfies $S_n = F(0) + F(1) + \cdots + F(n)$ for all $n$ if
and only if $S_n = 2^n$ for $0 \le n \le m$ and $S_n = 2 S_{n-1} - S_{n-m-1}$ for $n \ge m + 1$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Lemma 9
(`jis-2025-25.6.6-lem-9`). -/
public theorem_wanted sum_mStepFibonacci_iff_recurrence
    (m : ℕ) (hm : 1 ≤ m) (F : ℕ → ℕ) (hF0 : F 0 = 1)
    (hFinit : ∀ k, 1 ≤ k → k ≤ m - 1 → F k = 2 ^ (k - 1))
    (hFrec : ∀ k, m ≤ k → F k = ∑ t ∈ Finset.Icc 1 m, F (k - t)) (S : ℕ → ℝ) :
    (∀ n, S n = ∑ j ∈ Finset.range (n + 1), (F j : ℝ)) ↔
      ((∀ n, n ≤ m → S n = 2 ^ n) ∧ ∀ n, m + 1 ≤ n → S n = 2 * S (n - 1) - S (n - m - 1))

/-- **Keywords with equally many singleton classes.** Let $a$ and $b$ be binary keywords of
length $m + 1$. The relations $\sim_a$ and $\sim_b$ have the same number of one-element
equivalence classes on binary words of length $n$ for every $n \ge 0$ if and only if, for every
$i$ with $1 \le i \le m + 1$, the following holds for $a$ exactly when it holds for $b$: the
prefix of length $i$ of the keyword equals its suffix of length $i$ or the letterwise negation
of that suffix.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Proposition 10
(`jis-2025-25.6.6-prop-10`). -/
public theorem_wanted card_singleton_classes_eq_iff {m : ℕ} (a b : Fin (m + 1) → Bool) :
    (∀ n : ℕ, Nat.card {u : Fin n → Bool // ∀ v, KeywordEquiv a u v → v = u} =
        Nat.card {u : Fin n → Bool // ∀ v, KeywordEquiv b u v → v = u}) ↔
      ∀ i, 1 ≤ i → i ≤ m + 1 →
        (((List.ofFn a).take i = (List.ofFn a).drop (m + 1 - i) ∨
            (List.ofFn a).take i = ((List.ofFn a).drop (m + 1 - i)).map not) ↔
          ((List.ofFn b).take i = (List.ofFn b).drop (m + 1 - i) ∨
            (List.ofFn b).take i = ((List.ofFn b).drop (m + 1 - i)).map not))

/-- **When two simple maps commute.** Let $a$ be a keyword of length $m + 1$ and let $n$ be a
natural number. Let $i < j$ be natural numbers with $j + m < n$, and put $\Delta = j - i$. The
simple maps $\varphi_i$ and $\varphi_j$ of $a$ on binary words of length $n$ satisfy
$\varphi_i \circ \varphi_j = \varphi_j \circ \varphi_i$ if and only if $\Delta \ge m + 1$, or the
prefix of $a$ of length $m + 1 - \Delta$ differs both from the suffix of $a$ of length
$m + 1 - \Delta$ and from the letterwise negation of that suffix.

In the paper's numbering, which counts letters from $1$, the hypothesis reads $i < j \le n - m$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Proposition 12
(`jis-2025-25.6.6-prop-12`). -/
public theorem_wanted keywordSimpleMap_comm_iff {m n : ℕ} (a : Fin (m + 1) → Bool)
    (i j : ℕ) (hij : i < j) (hj : j + m < n) :
    (keywordSimpleMap (n := n) a i ∘ keywordSimpleMap a j =
        keywordSimpleMap a j ∘ keywordSimpleMap a i) ↔
      (((List.ofFn a).take (m + 1 - (j - i)) ≠ (List.ofFn a).drop (j - i) ∧
          (List.ofFn a).take (m + 1 - (j - i)) ≠ ((List.ofFn a).drop (j - i)).map not) ∨
        m + 1 ≤ j - i)

/-- **Keyword symmetries of the substitution graph.** Let $a = a_0 a_1 \cdots a_m$ be a keyword of
length $m + 1$ and let $n \ge 0$. Write $\neg a$ for the letterwise negation of $a$,
$\rho(a) = a_m a_{m-1} \cdots a_0$ for its reversal, and $\bar a$ for its seminegation, which keeps
$a_t$ for even $t$ and negates $a_t$ for odd $t$. Then the substitution graphs satisfy
$\mathcal{G}_n^{(a)} = \mathcal{G}_n^{(\neg a)}$, and $\mathcal{G}_n^{(a)}$ is isomorphic both to
$\mathcal{G}_n^{(\rho(a))}$ and to $\mathcal{G}_n^{(\bar a)}$.

In the paper's numbering, which counts letters from $1$, the seminegation negates the letters in
even positions. The paper states this for $n \ge 1$; it also holds at $n = 0$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Proposition 15
(`jis-2025-25.6.6-prop-15`). -/
public theorem_wanted keywordGraph_neg_rev_seminegation {m : ℕ} (a : Fin (m + 1) → Bool)
    (n : ℕ) :
    keywordGraph a n = keywordGraph (fun t => !a t) n ∧
      Nonempty (keywordGraph a n ≃g keywordGraph (fun t => a t.rev) n) ∧
      Nonempty (keywordGraph a n ≃g
        keywordGraph (fun t => if t.val % 2 = 0 then a t else !a t) n)

/-- **Intertwining bijections preserve distances in the substitution graph.** Let $a$ and $b$ be
keywords of length $m + 1$, and write $\varphi_i^{(a)}$ and $\varphi_i^{(b)}$ for the simple maps
of $a$ and $b$ at letter $i$ on binary words of length $n$. Let $f$ be a bijection of the set of
binary words of length $n$ and $\sigma$ a permutation of the positions $\{0, \dots, n - 1\}$, and
suppose that $f(\varphi_i^{(a)}(u)) = \varphi_{\sigma(i)}^{(b)}(f(u))$ for every word $u$ and
every position $i$. Then for all words $u$ and $v$ of length $n$, the extended graph distance
(possibly $\infty$) between $u$ and $v$ in the substitution graph $\mathcal{G}_n^{(a)}$ equals the
extended graph distance between $f(u)$ and $f(v)$ in $\mathcal{G}_n^{(b)}$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Lemma 16
(`jis-2025-25.6.6-lem-16`). -/
public theorem_wanted keywordGraph_edist_eq_of_intertwining {m n : ℕ}
    (a b : Fin (m + 1) → Bool) (f : (Fin n → Bool) ≃ (Fin n → Bool)) (σ : Equiv.Perm (Fin n))
    (hf : ∀ (u : Fin n → Bool) (i : Fin n),
      f (keywordSimpleMap a i u) = keywordSimpleMap b (σ i) (f u))
    (u v : Fin n → Bool) :
    (keywordGraph a n).edist u v = (keywordGraph b n).edist (f u) (f v)

/-- **The substitution graph is bipartite.** For every keyword $a$ of length $m + 1$ and every
$n \ge 0$, the substitution graph $\mathcal{G}_n^{(a)}$ on binary words of length $n$ is
bipartite.

The paper states this for $n \ge 1$; it also holds at $n = 0$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Proposition 17
(`jis-2025-25.6.6-prop-17`). -/
public theorem_wanted keywordGraph_isBipartite {m : ℕ} (a : Fin (m + 1) → Bool) (n : ℕ) :
    (keywordGraph a n).IsBipartite

end

end MetaMathlibExt
