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

/-- The keyword `a` is applicable to the word `u` at (`0`-indexed) letter `i`: the
subword of `u` of length `m + 1` starting at letter `i` exists and equals `a` or its
negation.

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
/-- The simple map `φ_i`: if the keyword `a` is applicable to `u` at letter `i`, negate
the letters `i, …, i + m` of `u` (replacing `a` by `!a` or vice versa); otherwise
return `u` unchanged.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Section 2.1 (simple maps). -/
noncomputable def keywordSimpleMap {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ)
    (u : Fin n → Bool) : Fin n → Bool :=
  if KeywordApplicable a i u then
    fun j => if i ≤ j.val ∧ j.val ≤ i + m then !u j else u j
  else u

/-- A simple map whose keyword is not applicable leaves the word unchanged.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Section 2.1 (simple maps). -/
theorem keywordSimpleMap_of_not_applicable {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ)
    (u : Fin n → Bool) (h : ¬ KeywordApplicable a i u) : keywordSimpleMap a i u = u := by
  simp [keywordSimpleMap, h]

/-- An applicable simple map negates exactly the letters `i, …, i + m`.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Section 2.1 (simple maps). -/
theorem keywordSimpleMap_apply_of_applicable {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ)
    (u : Fin n → Bool) (h : KeywordApplicable a i u) (j : Fin n) :
    keywordSimpleMap a i u j = if i ≤ j.val ∧ j.val ≤ i + m then !u j else u j := by
  simp [keywordSimpleMap, h]

/-- The equivalence relation `∼_a` on words of length `n`: `u ∼_a v` when some finite
composition of simple maps sends `u` to `v` (the empty composition included).

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.1 (equivalence relation induced by the keyword). -/
def KeywordEquiv {m n : ℕ} (a : Fin (m + 1) → Bool) : (Fin n → Bool) → (Fin n → Bool) → Prop :=
  Relation.ReflTransGen fun u v => ∃ i : ℕ, keywordSimpleMap a i u = v

/-- Every word is equivalent to itself (the empty composition).

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.1 (equivalence relation induced by the keyword). -/
theorem keywordEquiv_refl {m n : ℕ} (a : Fin (m + 1) → Bool) (u : Fin n → Bool) :
    KeywordEquiv a u u :=
  Relation.ReflTransGen.refl

/-- The graph `𝒢_n^(a)` on words of length `n`: `u` and `v` are adjacent when one is
obtained from the other by a single actual substitution `a ↦ !a` or `!a ↦ a`.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 3.2 (graph structure within equivalence classes). -/
def keywordGraph {m : ℕ} (a : Fin (m + 1) → Bool) (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel fun u v => ∃ i : ℕ, keywordSimpleMap a i u = v

/-- Adjacency in `𝒢_n^(a)`.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 3.2 (graph structure within equivalence classes). -/
theorem keywordGraph_adj {m n : ℕ} (a : Fin (m + 1) → Bool) (u v : Fin n → Bool) :
    (keywordGraph a n).Adj u v ↔
      u ≠ v ∧ ((∃ i : ℕ, keywordSimpleMap a i u = v) ∨ ∃ i : ℕ, keywordSimpleMap a i v = u) :=
  SimpleGraph.fromRel_adj _ _ _

/-- The action of a list of simple maps, the head acting first: the paper's list
`(φ_(j_r), …, φ_(j_1))` is `[j_1, …, j_r]` here.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.2 (action by lists of simple maps). -/
noncomputable def keywordListApply {m n : ℕ} (a : Fin (m + 1) → Bool) :
    List ℕ → (Fin n → Bool) → Fin n → Bool
  | [], u => u
  | j :: l, u => keywordListApply a l (keywordSimpleMap a j u)

/-- A list of simple maps acts completely on `u` when each map performs an actual
substitution.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.2 (action by lists of simple maps). -/
def KeywordActsCompletely {m n : ℕ} (a : Fin (m + 1) → Bool) :
    List ℕ → (Fin n → Bool) → Prop
  | [], _ => True
  | j :: l, u => keywordSimpleMap a j u ≠ u ∧ KeywordActsCompletely a l (keywordSimpleMap a j u)

/-- The empty list acts as the identity.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.2 (action by lists of simple maps). -/
theorem keywordListApply_nil {m n : ℕ} (a : Fin (m + 1) → Bool) (u : Fin n → Bool) :
    keywordListApply a [] u = u := rfl

/-- A one-element list acts completely exactly when its map performs a substitution.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6,
Section 2.2 (action by lists of simple maps). -/
theorem keywordActsCompletely_singleton {m n : ℕ} (a : Fin (m + 1) → Bool) (j : ℕ)
    (u : Fin n → Bool) :
    KeywordActsCompletely a [j] u ↔ keywordSimpleMap a j u ≠ u := by
  simp [KeywordActsCompletely]

/-- Main theorem: for `n, m ≥ 1` and every keyword `a` of length `m + 1`, the number of
`∼_a`-classes of binary words of length `n` is `F_0^(m) + F_1^(m) + ⋯ + F_n^(m)`.

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

/-- Equivalence is stable under appending or prepending a common word: for words
`u, v` of length `n` and `w` of length `n'`, `u ∼_a v ↔ u ⊕ w ∼_a v ⊕ w` and
`u ∼_a v ↔ w ⊕ u ∼_a w ⊕ v` (`⊕` is concatenation, `Fin.append`).

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Lemma 6
(`jis-2025-25.6.6-lem-6`). -/
public theorem_wanted keywordEquiv_append_iff {m n n' : ℕ} (a : Fin (m + 1) → Bool)
    (u v : Fin n → Bool) (w : Fin n' → Bool) :
    (KeywordEquiv a u v ↔ KeywordEquiv a (Fin.append u w) (Fin.append v w)) ∧
      (KeywordEquiv a u v ↔ KeywordEquiv a (Fin.append w u) (Fin.append w v))

/-- Parity of the smallest index: fix a letter `i` and a list `l = [j_1, …, j_r]` of
simple-map indices with (i) every `j_q > i`, (ii) `φ_i ∘ l ≠ l ∘ φ_i` as maps, and
(iii) some word on which `(φ_i, l, φ_i)` acts completely.  Then the smallest index
`j` of `l` occurs an even number of times in `l`.

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

/-- Recurrence characterization of the partial sums: for `m ≥ 1` and a real sequence
`S`, `S_n = F_0^(m) + ⋯ + F_n^(m)` for all `n` if and only if `S_n = 2 ^ n` for
`0 ≤ n ≤ m` and `S_n = 2 S_(n-1) - S_(n-m-1)` for `n ≥ m + 1`.

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

/-- Equal numbers of singleton classes: for keywords `a, b` of length `m + 1`, the
relations `∼_a` and `∼_b` have the same number of size-`1` classes on words of every
length `n` if and only if, for every `1 ≤ i ≤ m + 1`, the length-`i` prefix of `a`
equals the length-`i` suffix of `a` or its negation exactly when the same holds
for `b`.

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

/-- Commutation of simple maps: for letters `i < j` with `j + m < n` (the paper's
`i < j ≤ n - m`, `1`-indexed) and `Δ = j - i`, `φ_i ∘ φ_j = φ_j ∘ φ_i` if and only if
the length-`(m + 1 - Δ)` prefix of `a` is neither the length-`(m + 1 - Δ)` suffix of `a`
nor its negation, or the lines of action are disjoint (`Δ ≥ m + 1`).

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

/-- Keyword symmetries of the substitution graph: `𝒢_n^(a) = 𝒢_n^(!a)`, and
`𝒢_n^(a)` is isomorphic to `𝒢_n^(ρ a)` (reversed keyword) and to `𝒢_n^(ā)`
(seminegation: negate the letters in the paper's even positions, i.e. odd
`0`-indexed positions).  The paper states this for `n ≥ 1`; it also holds at `n = 0`.

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

/-- A sufficient condition for distance preservation: if bijections `f` of words and
`σ` of indices satisfy `f ∘ φ_i^(a) = φ_(σ i)^(b) ∘ f` for every index `i`, then
`d^(a)(u, v) = d^(b)(f u, f v)` for all words `u, v`, where `d` is the (extended)
graph distance in `𝒢_n`.

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

/-- The substitution graph `𝒢_n^(a)` is bipartite.  The paper states this for `n ≥ 1`;
it also holds at `n = 0`.

Source: Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood,
*A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*,
Journal of Integer Sequences 28 (2025), Article 25.6.6, Proposition 17
(`jis-2025-25.6.6-prop-17`). -/
public theorem_wanted keywordGraph_isBipartite {m : ℕ} (a : Fin (m + 1) → Bool) (n : ℕ) :
    (keywordGraph a n).IsBipartite

end

end MetaMathlibExt
