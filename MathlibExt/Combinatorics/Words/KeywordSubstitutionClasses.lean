/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.ModEq

/-!
# Keyword substitutions on binary words

A substitution exchanges a nonempty binary keyword with its letterwise negation.
The substitution graph is bipartite: the parity of the ones at positions divisible by
the keyword length changes across each edge.

We index positions from zero, so the paper's simple map at letter `i + 1` is
`keywordSimpleMap a i`.

## References

* Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
  *A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
  Journal of Integer Sequences 28 (2025), Article 25.6.6.
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

-- The last multiple of the keyword length at or before the right endpoint is in the window.
private theorem existsUnique_window_multiple {i m n : ℕ} (h : i + m < n) :
    ∃! j : Fin n, (m + 1) ∣ j.val ∧ i ≤ j.val ∧ j.val ≤ i + m := by
  let k := (m + 1) * ((i + m) / (m + 1))
  have hdiv := Nat.mod_add_div (i + m) (m + 1)
  have hmod := Nat.mod_lt (i + m) (show 0 < m + 1 by omega)
  have hk : i ≤ k ∧ k ≤ i + m := by dsimp [k]; omega
  have hd : m + 1 ∣ k := Nat.dvd_mul_right ..
  refine ⟨⟨k, lt_of_le_of_lt hk.2 h⟩, ⟨hd, hk⟩, ?_⟩
  rintro j ⟨hj, hjl, hjr⟩
  apply Fin.ext
  have heq := (Nat.modEq_zero_iff_dvd.mpr hj).trans (Nat.modEq_zero_iff_dvd.mpr hd).symm
  exact heq.eq_of_abs_lt (abs_lt.mpr (by omega))

/-- **The substitution graph is bipartite.** For every keyword $a$ of length $m + 1$ and every
$n \ge 0$, the substitution graph $\mathcal{G}_n^{(a)}$ on binary words of length $n$ is
bipartite.

The paper states this for $n \ge 1$; it also holds at $n = 0$.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Proposition 17
(`jis-2025-25.6.6-prop-17`). -/
theorem keywordGraph_isBipartite {m : ℕ} (a : Fin (m + 1) → Bool) (n : ℕ) :
    (keywordGraph a n).IsBipartite := by
  let positions := Finset.univ.filter fun j : Fin n => m + 1 ∣ j.val
  let color (u : Fin n → Bool) : Fin 2 := ∑ j ∈ positions, if u j then 1 else 0
  have changes (i : ℕ) (u : Fin n → Bool) (hne : keywordSimpleMap a i u ≠ u) :
      color (keywordSimpleMap a i u) ≠ color u := by
    have ha : KeywordApplicable a i u := by
      by_contra h
      exact hne (keywordSimpleMap_of_not_applicable a i u h)
    obtain ⟨k, ⟨hd, hwin⟩, hunique⟩ := existsUnique_window_multiple ha.choose
    have hk : k ∈ positions := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
    unfold color
    rw [ne_eq, Finset.sum_eq_sum_iff_single hk]
    · rw [keywordSimpleMap_apply_of_applicable a i u ha, ite_eq_left hwin]
      cases u k <;> decide
    · intro j hj hjk
      have hout : ¬ (i ≤ j.val ∧ j.val ≤ i + m) :=
        fun hw => hjk (hunique j ⟨(Finset.mem_filter.mp hj).2, hw⟩)
      rw [keywordSimpleMap_apply_of_applicable a i u ha, ite_eq_right hout]
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro u v huv
  obtain ⟨hne, ⟨i, rfl⟩ | ⟨i, rfl⟩⟩ := (keywordGraph_adj a u v).mp huv
  · exact (changes i u hne.symm).symm
  · exact changes i v hne

end

end MetaMathlibExt
