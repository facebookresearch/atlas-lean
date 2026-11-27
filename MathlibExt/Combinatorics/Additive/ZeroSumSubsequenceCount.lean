/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin

/-!
# Counting zero-sum subsequences

The Alford–Granville–Pomerance bound counts subsequences with product one and length
in a prescribed interval determined by the Davenport constant.
-/

namespace MetaMathlibExt

open Finset

-- The source's strict bound `t < r` is kept in the statement.
set_option linter.unusedVariables false in
/-- **Alford–Granville–Pomerance count of zero-sum subsequences.** Let $G$ be an abelian group
and let $n$ be the least natural number $m$ such that every sequence of $m$ elements of $G$ has a
nonempty subsequence with product $1$ (the Davenport constant of $G$). Let $r$ and $t$ be natural
numbers with $n < t < r$. Then for every sequence $s_1, \dots, s_r$ of elements of $G$, the number
$M$ of sets $S \subseteq \{1, \dots, r\}$ with $t - n \le |S| \le t$ and $\prod_{i \in S} s_i = 1$
satisfies $\binom{r}{t} \le \binom{r}{n} M$.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Proposition 1 (`integers-2024-A97-prop-1`), quoting Alford, Granville,
and Pomerance, Theorem 2.1. -/
public theorem choose_le_choose_mul_card_prod_eq_one {G : Type*} [CommGroup G]
    [DecidableEq G] (n : ℕ)
    (hn : IsLeast {m : ℕ | ∀ s : Fin m → G, ∃ S : Finset (Fin m), S.Nonempty ∧
      ∏ i ∈ S, s i = 1} n)
    (r t : ℕ) (hrt : t < r) (htn : n < t) (s : Fin r → G) :
    r.choose t ≤ r.choose n *
      (Finset.univ.filter fun S : Finset (Fin r) =>
        t - n ≤ S.card ∧ S.card ≤ t ∧ ∏ i ∈ S, s i = 1).card := by
  let good := Finset.univ.filter fun S : Finset (Fin r) =>
    t - n ≤ S.card ∧ S.card ≤ t ∧ ∏ i ∈ S, s i = 1
  let U : Finset (Fin r) := univ
  suffices (U.powersetCard t).card ≤ (U.powersetCard n ×ˢ good).card by
    simpa only [card_product, card_powersetCard, card_univ, Fintype.card_fin, U, good] using this
  apply card_le_card_of_surjOn (fun p : Finset (Fin r) × Finset (Fin r) => p.1 ∪ p.2)
  intro T hT
  have hTcard := (mem_powersetCard.mp (mem_coe.mp hT)).2
  -- Take a largest product-one subset of T.
  let candidates := T.powerset.filter fun S => ∏ i ∈ S, s i = 1
  have hempty : ∅ ∈ candidates := by simp [candidates]
  obtain ⟨S, hS, hmax⟩ := exists_max_image candidates card ⟨∅, hempty⟩
  obtain ⟨hSp, hSprod⟩ := mem_filter.mp hS
  have hST := mem_powerset.mp hSp
  -- A remainder of size at least n would contain another product-one subset.
  have hrem : (T \ S).card < n := by
    by_contra! hlarge
    obtain ⟨V, hV, hVcard⟩ := exists_subset_card_eq hlarge
    let e : Fin n ↪ Fin r := (V.equivFinOfCardEq hVcard).symm.toEmbedding.trans
      (Function.Embedding.subtype _)
    obtain ⟨W, hW, hWprod⟩ := hn.1 (s ∘ e)
    change (∏ i ∈ W, s (e i)) = 1 at hWprod
    have hWrem : W.map e ⊆ T \ S := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := mem_map.mp hi
      exact hV ((V.equivFinOfCardEq hVcard).symm j).property
    have hdisj : Disjoint (W.map e) S := sdiff_disjoint.mono_left hWrem
    have hmem : W.map e ∪ S ∈ candidates := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (union_subset (hWrem.trans sdiff_subset) hST), ?_⟩
      rw [prod_union hdisj, prod_map, hWprod, hSprod, one_mul]
    have hbound := hmax _ hmem
    rw [card_union_of_disjoint hdisj, card_map] at hbound
    have hpos := card_pos.mpr hW
    omega
  have hScard := card_le_card hST
  have hSmin : t - n ≤ S.card := by
    rw [card_sdiff_of_subset hST, hTcard] at hrem
    omega
  -- Enlarge the remainder to n indices inside T. Its union with S recovers T.
  obtain ⟨R, hremR, hRT, hRcard⟩ :=
    exists_subsuperset_card_eq sdiff_subset hrem.le (hTcard ▸ htn.le)
  refine ⟨(R, S), mem_coe.mpr <| mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · exact mem_powersetCard.mpr ⟨subset_univ _, hRcard⟩
  · exact mem_filter.mpr ⟨mem_univ _, hSmin, hScard.trans_eq hTcard, hSprod⟩
  · exact (union_subset hRT hST).antisymm
      (sdiff_union_of_subset hST ▸ union_subset_union hremR Subset.rfl)

end MetaMathlibExt
