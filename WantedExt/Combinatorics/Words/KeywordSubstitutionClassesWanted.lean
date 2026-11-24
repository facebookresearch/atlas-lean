/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Words.KeywordGraphDistance
public import MathlibExt.NumberTheory.Recurrences.MStepFibonacciPartialSums

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

end

end MetaMathlibExt
