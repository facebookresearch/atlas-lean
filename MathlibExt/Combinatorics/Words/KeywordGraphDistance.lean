/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import MathlibExt.Combinatorics.Words.KeywordSubstitutionClasses

/-!
# Distances in keyword substitution graphs

A bijection that intertwines the simple maps up to a permutation of positions preserves
extended graph distances.
-/

namespace MetaMathlibExt

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
public theorem keywordGraph_edist_eq_of_intertwining {m n : ℕ}
    (a b : Fin (m + 1) → Bool) (f : (Fin n → Bool) ≃ (Fin n → Bool)) (σ : Equiv.Perm (Fin n))
    (hf : ∀ (u : Fin n → Bool) (i : Fin n),
      f (keywordSimpleMap a i u) = keywordSimpleMap b (σ i) (f u))
    (u v : Fin n → Bool) :
    (keywordGraph a n).edist u v = (keywordGraph b n).edist (f u) (f v) := by
  -- A substitution between distinct words must start inside the word.
  have bounded (c : Fin (m + 1) → Bool) {x y : Fin n → Bool} (hne : x ≠ y) :
      (∃ i : ℕ, keywordSimpleMap c i x = y) ↔ ∃ i : Fin n, keywordSimpleMap c i x = y := by
    constructor
    · rintro ⟨i, hi⟩
      have ha : KeywordApplicable c i x := by
        by_contra h
        exact hne ((keywordSimpleMap_of_not_applicable c i x h).symm.trans hi)
      exact ⟨⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i m) ha.choose⟩, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i.val, hi⟩
  have step {x y : Fin n → Bool} (hne : x ≠ y) :
      (∃ i : ℕ, keywordSimpleMap a i x = y) ↔ ∃ j : ℕ, keywordSimpleMap b j (f x) = f y := by
    rw [bounded a hne, bounded b (f.injective.ne hne)]
    exact σ.exists_congr fun i => by rw [← hf, f.injective.eq_iff]
  let iso : keywordGraph a n ≃g keywordGraph b n :=
    { toEquiv := f
      map_rel_iff' := by
        intro x y
        rw [keywordGraph_adj, keywordGraph_adj, f.injective.ne_iff]
        exact and_congr_right fun hne => ((step hne).or (step hne.symm)).symm }
  exact (iso.edist_eq u v).symm

end MetaMathlibExt
