/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset

import Mathlib.Data.Finset.Prod

/-!
# Counting fixed-size subsets with a prescribed overlap

Given finsets $A \subseteq U$ and natural numbers $k \le n$, split an $n$-element subset of $U$
with $k$ elements in $A$ into its intersection with $A$ and its difference from $A$.
These two pieces can be chosen independently and their union recovers the subset.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, 3rd ed.,
  John Wiley & Sons (1968), §II.6, pp. 43–44, counting argument for (6.1).
* Generalizes the former `ProbabilityTheory.count_overlap` in
  `MathlibExt.Probability.Statistics.UStatistic` to allow the subset size to differ from $|A|$.
-/

public section

namespace Finset

/-- **Fixed-size subsets with a prescribed overlap.** Let $A \subseteq U$ be finsets in a type with
decidable equality, and let $k \le n$ be natural numbers. The number of subsets $S \subseteq U$
with $|S| = n$ and $|S \cap A| = k$ is $\binom{|A|}{k}\binom{|U|-|A|}{n-k}$. -/
theorem card_filter_powersetCard_inter_eq_choose {α : Type*} [DecidableEq α]
    {A U : Finset α} (hAU : A ⊆ U) {n k : ℕ} (hk : k ≤ n) :
    ((U.powersetCard n).filter fun S => (S ∩ A).card = k).card =
      A.card.choose k * (U.card - A.card).choose (n - k) := by
  rw [← card_sdiff_of_subset hAU, ← card_powersetCard k A,
    ← card_powersetCard (n - k) (U \ A), ← card_product]
  have inter_union {B C : Finset α} (hB : B ⊆ A) (hC : C ⊆ U \ A) : (B ∪ C) ∩ A = B := by
    have hCA : Disjoint C A := disjoint_of_subset_left hC disjoint_sdiff_self_left
    rw [union_inter_distrib_right, inter_eq_left.mpr hB, disjoint_iff_inter_eq_empty.mp hCA,
      union_empty]
  refine card_bij' (fun S _ => (S ∩ A, S \ A)) (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨hSU, hSn⟩, hSk⟩ := hS
    refine mem_product.mpr ⟨mem_powersetCard.mpr ⟨inter_subset_right, hSk⟩,
      mem_powersetCard.mpr ⟨sdiff_subset_sdiff_left A hSU, ?_⟩⟩
    rw [card_sdiff, inter_comm A S, hSn, hSk]
  · intro p hp
    simp only [mem_product, mem_powersetCard] at hp
    obtain ⟨⟨hB, hBk⟩, ⟨hC, hCk⟩⟩ := hp
    have hAC : Disjoint A p.2 := disjoint_of_subset_right hC disjoint_sdiff_self_right
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨union_subset (hB.trans hAU)
      (hC.trans sdiff_subset), ?_⟩, (inter_union hB hC).symm ▸ hBk⟩
    rw [card_union_of_disjoint (disjoint_of_subset_left hB hAC), hBk, hCk, Nat.add_sub_of_le hk]
  · intro S _
    exact (union_comm _ _).trans (sdiff_union_inter S A)
  · intro p hp
    simp only [mem_product, mem_powersetCard] at hp
    obtain ⟨⟨hB, _⟩, ⟨hC, _⟩⟩ := hp
    have hCA : Disjoint p.2 A := disjoint_of_subset_left hC disjoint_sdiff_self_left
    exact Prod.ext (inter_union hB hC) (by
      rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.mpr hB, empty_union, hCA.sdiff_eq_left])

end Finset
