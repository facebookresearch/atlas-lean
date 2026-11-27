/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.CompletePartialOrder
public import MathlibExt.Combinatorics.Additive.Basis
public import MathlibExt.Combinatorics.Additive.UpperDensitySumsetPartition

/-!
# An asymptotic basis admitting no bounded-gap splitting

This module defines bounded gaps and proves the existence of an asymptotic additive basis
of order two for which no partition has two sumsets with bounded gaps.

Sources: T. F. Bloom, Erdős Problems, Problem #741; B. Alexeev, M. Putterman, M. Sawhney,
M. Sellke and G. Valiant, *Short proofs in combinatorics and number theory*,
arXiv:2603.29961 (2026), Theorem 3.1.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted

open scoped Pointwise

/-- **Sets with bounded gaps.** A set $S \subseteq \mathbb{N}$ has bounded gaps (is syndetic) if
there is a natural number $g$ such that for every natural number $n$ some $s \in S$ satisfies
$n \le s < n + g$. -/
def HasBoundedGaps (S : Set ℕ) : Prop :=
  ∃ g : ℕ, ∀ n : ℕ, ∃ s ∈ S, n ≤ s ∧ s < n + g

/-- **Erdős Problem 741, bounded-gaps question.** This proposition asserts that there is a set
$A \subseteq \mathbb{N}$ that is an asymptotic additive basis of order $2$ (all but finitely many
natural numbers are sums of two elements of $A$) such that for all disjoint sets
$A_1, A_2 \subseteq \mathbb{N}$ with $A_1 \cup A_2 = A$, the sumsets
$A_1 + A_1 = \{a + b : a, b \in A_1\}$ and $A_2 + A_2$ do not both have bounded gaps. -/
def basisWithoutBoundedGapSplit : Prop :=
  ∃ A : Set ℕ, A.IsAsymptoticAddBasisOfOrder 2 ∧
    ∀ A₁ A₂ : Set ℕ, Disjoint A₁ A₂ → A₁ ∪ A₂ = A →
      ¬ (HasBoundedGaps (A₁ + A₁) ∧ HasBoundedGaps (A₂ + A₂))

private def candidate : Set ℕ :=
  {n | ∀ k : ℕ, 6 * 100 ^ k ≤ n → n ≤ 13 * 100 ^ k → n = 10 * 100 ^ k}

private lemma scale_separation {j k : ℕ} (h : j < k) :
    100 * 100 ^ j ≤ 100 ^ k := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 100) h
  simpa [pow_succ, Nat.mul_comm] using hp

private lemma gap_mem (k n : ℕ) (hl : 100 ^ k ≤ n) (hu : n < 6 * 100 ^ k) :
    n ∈ candidate := by
  intro j hjl hju
  by_cases h : j < k
  · have hp := scale_separation h
    have hpos := Nat.pow_pos (by decide : 0 < 100) (n := j)
    omega
  · have hp := Nat.pow_le_pow_right (by decide : 0 < 100) (by omega : k ≤ j)
    omega

private lemma center_mem (k : ℕ) : 10 * 100 ^ k ∈ candidate := by
  intro j hjl hju
  rcases lt_trichotomy j k with h | rfl | h
  · have hp := scale_separation h
    have hpos := Nat.pow_pos (by decide : 0 < 100) (n := j)
    omega
  · rfl
  · have hp := scale_separation h
    have hpos := Nat.pow_pos (by decide : 0 < 100) (n := k)
    omega

private lemma zero_mem : 0 ∈ candidate := by
  intro k hk _
  have hpos := Nat.pow_pos (by decide : 0 < 100) (n := k)
  omega

private lemma candidate_basis (n : ℕ) : n ∈ candidate + candidate := by
  classical
  by_cases hn : n ∈ candidate
  · exact ⟨n, hn, 0, zero_mem, Nat.add_zero _⟩
  · change ¬ ∀ k : ℕ, 6 * 100 ^ k ≤ n → n ≤ 13 * 100 ^ k → n = 10 * 100 ^ k at hn
    push Not at hn
    obtain ⟨k, hl, hu, _⟩ := hn
    have hpos := Nat.pow_pos (by decide : 0 < 100) (n := k)
    by_cases h : n < 11 * 100 ^ k
    · exact ⟨n / 2, gap_mem k _ (by omega) (by omega),
        (n + 1) / 2, gap_mem k _ (by omega) (by omega), by dsimp; omega⟩
    · exact ⟨10 * 100 ^ k, center_mem k,
        n - 10 * 100 ^ k, gap_mem k _ (by omega) (by omega), by dsimp; omega⟩

private lemma rigid_sum (k a b : ℕ) (ha : a ∈ candidate) (hb : b ∈ candidate)
    (hl : 12 * 100 ^ k ≤ a + b) (hu : a + b ≤ 13 * 100 ^ k) :
    a = 10 * 100 ^ k ∨ b = 10 * 100 ^ k := by
  by_cases h : 6 * 100 ^ k ≤ a
  · exact Or.inl (ha k h (by omega))
  · exact Or.inr (hb k (by omega) (by omega))

private lemma candidate_no_split (A₁ A₂ : Set ℕ) (hd : Disjoint A₁ A₂)
    (he : A₁ ∪ A₂ = candidate) :
    ¬ (HasBoundedGaps (A₁ + A₁) ∧ HasBoundedGaps (A₂ + A₂)) := by
  rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩
  let k := g₁ + g₂
  have hp : k < 100 ^ k := Nat.lt_pow_self (by decide : 1 < 100)
  obtain ⟨s, ⟨a, ha, b, hb, rfl⟩, hl, hu⟩ := h₁ (12 * 100 ^ k)
  obtain ⟨t, ⟨c, hc, d, hd', rfl⟩, hl', hu'⟩ := h₂ (12 * 100 ^ k)
  have hsub₁ : A₁ ⊆ candidate := by
    rw [← he]
    exact Set.subset_union_left
  have hsub₂ : A₂ ⊆ candidate := by
    rw [← he]
    exact Set.subset_union_right
  have hc₁ : 10 * 100 ^ k ∈ A₁ := by
    rcases rigid_sum k a b (hsub₁ ha) (hsub₁ hb) hl (by dsimp [k] at *; omega) with h | h
    · simpa [h] using ha
    · simpa [h] using hb
  have hc₂ : 10 * 100 ^ k ∈ A₂ := by
    rcases rigid_sum k c d (hsub₂ hc) (hsub₂ hd') hl' (by dsimp [k] at *; omega) with h | h
    · simpa [h] using hc
    · simpa [h] using hd'
  exact Set.disjoint_left.mp hd hc₁ hc₂

/-- **An asymptotic basis of order 2 admitting no bounded-gap splitting.** There is a set
$A \subseteq \mathbb{N}$ that is an asymptotic additive basis of order $2$ (all but finitely many
natural numbers are sums of two elements of $A$) such that for all disjoint sets
$A_1, A_2 \subseteq \mathbb{N}$ with $A_1 \cup A_2 = A$, the sumsets
$A_1 + A_1 = \{a + b : a, b \in A_1\}$ and $A_2 + A_2$ do not both have bounded gaps, where a set
$S \subseteq \mathbb{N}$ has bounded gaps if for some $g \in \mathbb{N}$ every interval
$[n, n + g)$ with $n \in \mathbb{N}$ meets $S$.

Source: T. F. Bloom, Erdős Problems, Problem #741, https://www.erdosproblems.com/741 (status SOLVED
(LEAN)); resolution: B. Alexeev, M. Putterman, M. Sawhney, M. Sellke and G. Valiant, Short proofs in
combinatorics and number theory, arXiv:2603.29961 (2026); erdosproblems.com/741 (DeepMind), Theorem
3.1 of arXiv:2603.29961 (proof due to an internal OpenAI model): there is A ⊂ ℕ, a basis of order 2
with [4, ∞) ⊆ A + A, such that for every partition A = A₁ ⊔ A₂ one of A₁ + A₁, A₂ + A₂ does not have
bounded gaps; erdosproblems.com/741: DeepMind gave a positive answer to the upper-density question
(proof sketched in the comments), https://arxiv.org/abs/2603.29961.
-/
public theorem basisWithoutBoundedGapSplit_holds : basisWithoutBoundedGapSplit := by
  refine ⟨candidate, ?_, candidate_no_split⟩
  apply Filter.Eventually.of_forall
  intro n
  simpa only [two_nsmul] using candidate_basis n

end MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted
