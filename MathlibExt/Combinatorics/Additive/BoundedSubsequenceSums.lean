/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.BoundedSubsetSums

/-!
# Bounded subsequence sums when zero is a term

Padding with zeros identifies bounded subsequence sums with a generalized sumset of fixed length.
-/

namespace MetaMathlibExt

namespace boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_mem

/-- Encode a submultiset by the multiplicity it selects at each distinct term. -/
private theorem mem_boundedSubsequenceSums_iff {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {k : ℕ} (a : Fin k → G) (ha : Function.Injective a) (t : Fin k → ℕ) (α β : ℕ) (x : G) :
    x ∈ boundedSubsequenceSums α β (repetitionSequence a t) ↔
      ∃ s : Fin k → ℕ, (∀ i, s i ≤ t i) ∧ α ≤ ∑ i, s i ∧
        (∑ i, s i) + β ≤ ∑ i, t i ∧ ∑ i, s i • a i = x := by
  have hcount (u : Fin k → ℕ) (i : Fin k) : (repetitionSequence a u).count (a i) = u i := by
    simp [repetitionSequence, Multiset.count_sum', Multiset.count_replicate, ha.eq_iff]
  have hsum (u : Fin k → ℕ) : (repetitionSequence a u).sum = ∑ i, u i • a i := by
    simp [repetitionSequence, Multiset.sum_sum]
  simp only [boundedSubsequenceSums, Multiset.mem_toFinset, Multiset.mem_map,
    Multiset.mem_filter, Multiset.mem_powerset, card_repetitionSequence]
  constructor
  · rintro ⟨T, ⟨hT, hlo, hhi⟩, rfl⟩
    let s (i : Fin k) := T.count (a i)
    have hs : repetitionSequence a s = T := by
      ext y
      by_cases hy : ∃ i, a i = y
      · obtain ⟨i, rfl⟩ := hy
        exact hcount s i
      · have hnone : ∀ i, a i ≠ y := fun i hi => hy ⟨i, hi⟩
        have hz (u : Fin k → ℕ) : (repetitionSequence a u).count y = 0 := by
          simp [repetitionSequence, Multiset.count_sum', Multiset.count_replicate, hnone]
        have : T.count y ≤ 0 := by simpa only [hz] using Multiset.count_le_of_le y hT
        rw [hz, Nat.eq_zero_of_le_zero this]
    refine ⟨s, fun i => (Multiset.count_le_of_le (a i) hT).trans (hcount t i).le, ?_⟩
    rw [← hs, card_repetitionSequence] at hlo hhi
    exact ⟨hlo, hhi, (hsum s).symm.trans (congrArg Multiset.sum hs)⟩
  · rintro ⟨s, hs, hlo, hhi, rfl⟩
    refine ⟨repetitionSequence a s, ⟨?_, ?_, ?_⟩, hsum s⟩
    · exact Finset.sum_le_sum fun i _ => (Multiset.replicate_le_replicate (a i)).2 (hs i)
    · rwa [card_repetitionSequence]
    · rwa [card_repetitionSequence]

end boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_mem

open boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_mem in
set_option linter.unusedVariables false in
/-- **Bounded subsequence sums as a generalized h-fold sumset when zero is a term.** Let $G$ be
an abelian group, let $m$ be a natural number, let $a_1, \dots, a_m$ be distinct nonzero elements
of $G$, and put $a_0 = 0$. Let $t_0, \dots, t_m$ be positive integers, let $\mathcal{A}$ be the
sequence in which each $a_i$ occurs $t_i$ times, and let $h = t_0 + \dots + t_m$ be its length.
If $\alpha, \beta$ are natural numbers with $\alpha \ge 1$, $\beta \le h - 1$ and
$\alpha + \beta \le h$, then $\Sigma^\beta_\alpha(\mathcal{A})$, the set of sums of subsequences
of $\mathcal{A}$ with at least $\alpha$ and at most $h - \beta$ terms, equals the generalized
$(h - \beta)$-fold sumset $(h - \beta)^{(\bar r)} A$ of $A = (a_0, a_1, \dots, a_m)$ with
$\bar r = (h - \alpha - \beta + t_0, t_1, \dots, t_m)$, that is, the set of sums
$\sum_{j=0}^{m} s_j a_j$ with $0 \le s_j \le r_j$ for all $j$ and $\sum_j s_j = h - \beta$.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Lemma 5 (`integers-2024-A116-lem-5`). -/
public theorem boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_mem
    {G : Type*} [AddCommGroup G] [DecidableEq G] {m : ℕ} (b : Fin m → G)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0) (t : Fin (m + 1) → ℕ) (ht : ∀ i, 0 < t i)
    (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α) (hβ : β + 1 ≤ h) (hαβ : α + β ≤ h) :
    boundedSubsequenceSums α β (repetitionSequence (Fin.cons 0 b : Fin (m + 1) → G) t) =
      generalizedHFoldSumset (Fin.cons 0 b : Fin (m + 1) → G)
        (Fin.cons (h - α - β + t 0) (Fin.tail t) : Fin (m + 1) → ℕ) (h - β) := by
  have ha : Function.Injective (Fin.cons 0 b : Fin (m + 1) → G) :=
    Fin.cons_injective_of_injective (by simpa using hb0) hb
  ext x
  rw [mem_boundedSubsequenceSums_iff _ ha, ← hh]
  simp only [generalizedHFoldSumset, Finset.mem_image, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨s, hs, hlo, hhi, rfl⟩
    rw [Fin.sum_univ_succ s] at hlo hhi
    -- Pad the selected nonzero terms to length h - β.
    refine ⟨Fin.cons (h - β - ∑ i : Fin m, s i.succ) (Fin.tail s), ⟨?_, ?_⟩, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => hs j.succ) i
      simp only [Fin.cons_zero]
      have := hs 0
      omega
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      omega
    · simp [Fin.sum_univ_succ, Fin.tail]
  · rintro ⟨s, ⟨hs, hlen⟩, rfl⟩
    rw [Fin.sum_univ_succ s] at hlen
    have hzero : s 0 ≤ h - α - β + t 0 := hs 0
    -- Keep as many of the chosen zeros as the original sequence contains.
    refine ⟨Fin.cons (min (s 0) (t 0)) (Fin.tail s), ?_, ?_, ?_, ?_⟩
    · intro i
      exact Fin.cases (min_le_right ..) (fun j => hs j.succ) i
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      omega
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      omega
    · simp [Fin.sum_univ_succ, Fin.tail]

end MetaMathlibExt
