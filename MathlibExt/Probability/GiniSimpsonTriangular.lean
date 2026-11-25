/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DiversityStatistics
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Qify

/-!
# A triangular-number lower bound for the number of Gini–Simpson values

We bound the number of distinct sums of squared type counts by counting samples with
one distinguished type, some pairs, and singletons filling the remaining places.
-/

public section

namespace MathlibExt.Probability.DiversityStatisticsWanted

private lemma finite_square_sums (N : ℕ) :
    {s : ℕ | ∃ l : List ℕ, l.sum = N ∧ (l.map (fun a => a ^ 2)).sum = s}.Finite := by
  apply (Set.finite_Iic (N ^ 2)).subset
  rintro _ ⟨l, rfl, rfl⟩
  change (l.map (fun a => a ^ 2)).sum ≤ l.sum ^ 2
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    nlinarith only [ih, Nat.zero_le (a * l.sum)]

private lemma choose_two_step (a : ℕ) : (a + 1).choose 2 = a.choose 2 + a := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

-- For j < a the pair count lies between a.choose 2 and (a+1).choose 2, excluding
-- the upper endpoint. Thus the pair count determines both a and j.
private lemma pair_count_lt {a b j : ℕ} (hj : j < a) (hab : a < b) :
    a.choose 2 + j < b.choose 2 := by
  calc
    a.choose 2 + j < (a + 1).choose 2 := by
      rw [choose_two_step]
      exact Nat.add_lt_add_left hj _
    _ ≤ b.choose 2 := Nat.choose_le_choose 2 hab

private lemma realize_square_sum {N a j : ℕ} (h : a + 2 * j ≤ N) :
    ∃ l : List ℕ, l.sum = N ∧ (l.map (fun a => a ^ 2)).sum = N + 2 * (a.choose 2 + j) := by
  let u := N - (a + 2 * j)
  have hu : a + 2 * j + u = N := by dsimp [u]; omega
  refine ⟨a :: (List.replicate j 2 ++ List.replicate u 1), ?_, ?_⟩
  · simpa [List.sum_replicate, nsmul_eq_mul, mul_comm, add_assoc] using hu
  · simp only [List.map_cons, List.map_append, List.map_replicate, List.sum_cons,
      List.sum_append, List.sum_replicate, nsmul_eq_mul, one_pow, mul_one]
    qify at hu ⊢
    rw [Nat.cast_choose_two]
    linarith

-- At total cost t+1 = a+2j, precisely j = 0, ..., ⌊t/3⌋ satisfy j < a.
private def familyCount (N : ℕ) : ℕ := ∑ t ∈ Finset.range N, (t / 3 + 1)

private lemma familyCount_le (N : ℕ) : familyCount N ≤ giniSimpsonCount N := by
  let indices := (Finset.range N).sigma (fun t => Finset.range (t / 3 + 1))
  let part (p : Σ _ : ℕ, ℕ) := p.1 + 1 - 2 * p.2
  let value (p : Σ _ : ℕ, ℕ) := N + 2 * ((part p).choose 2 + p.2)
  have bounds (p) (hp : p ∈ indices) : p.2 < part p ∧ part p + 2 * p.2 = p.1 + 1 ∧
      p.1 + 1 ≤ N := by
    simp only [indices, Finset.mem_sigma, Finset.mem_range] at hp
    dsimp [part]
    omega
  calc
    familyCount N = (indices : Set (Σ _ : ℕ, ℕ)).ncard := by
      simp only [Set.ncard_coe_finset, indices, Finset.card_sigma, Finset.card_range, familyCount]
    _ ≤ giniSimpsonCount N := by
      refine Set.ncard_le_ncard_of_injOn value ?_ ?_ (finite_square_sums N)
      · intro p hp
        obtain ⟨_, heq, hle⟩ := bounds p hp
        exact realize_square_sum (heq.le.trans hle)
      · intro p hp q hq heq
        obtain ⟨hpj, hpt, _⟩ := bounds p hp
        obtain ⟨hqj, hqt, _⟩ := bounds q hq
        dsimp only [value] at heq
        have ha : part p = part q := by
          rcases lt_trichotomy (part p) (part q) with h | h | h
          · have := pair_count_lt hpj h
            omega
          · exact h
          · have := pair_count_lt hqj h
            omega
        rw [ha] at heq hpt
        have hj : p.2 = q.2 := by omega
        have ht : p.1 = q.1 := by omega
        exact Sigma.ext ht (heq_of_eq hj)

-- Beyond the m-th triangular number, each new cost contributes at least m choices.
private lemma triangular_slope (m : ℕ) : m ≤ (m + 1).choose 2 / 3 + 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [choose_two_step (m + 1)]
    match m with
    | 0 | 1 => decide
    | m + 2 => omega

private lemma familyCount_add (m r : ℕ) :
    familyCount ((m + 1).choose 2) + m * r ≤ familyCount ((m + 1).choose 2 + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    unfold familyCount at ih ⊢
    rw [Nat.mul_succ, ← Nat.add_assoc, ← Nat.add_assoc, Finset.sum_range_succ]
    have := triangular_slope m
    omega

private lemma triangular_family_bound (m : ℕ) (hm : 0 < m) :
    (1 / 3 : ℚ) * m * ((m : ℚ) ^ 2 - 1) + 1 ≤ familyCount ((m + 1).choose 2) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [familyCount, Nat.choose]
  | succ m hm ih =>
    have h := familyCount_add m (m + 1)
    rw [choose_two_step (m + 1)]
    qify at h ⊢
    linarith

/-- **Triangular-number lower bound on the number of Gini–Simpson values.** Let $\gamma(N)$ be the
number of distinct values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$
of natural numbers with $a_1 + \dots + a_k = N$ (for $N \ge 1$, the number of possible values of the
Gini–Simpson index across samples of size $N$). Let $m$ and $r$ be natural numbers with $r \le m$,
and let $N = \binom{m+1}{2} + r$. Then
$$\tfrac{1}{3} m (m^2 + 3r - 1) + 1 \le \gamma(N).$$

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 5. -/
theorem giniSimpsonCount_ge_triangular (N m r : ℕ)
    (hN : N = (m + 1) * m / 2 + r) (hr : r ≤ m) :
    (1 / 3) * (m : ℚ) * ((m : ℚ) ^ 2 + 3 * r - 1) + 1 ≤
      (giniSimpsonCount N : ℚ) := by
  by_cases hm : m = 0
  · subst m
    have hr0 : r = 0 := by omega
    subst r
    norm_num at hN
    subst N
    have h := (Set.ncard_pos (finite_square_sums 0)).mpr ⟨0, [], rfl, rfl⟩
    change 1 ≤ giniSimpsonCount 0 at h
    norm_num
    exact_mod_cast h
  · have ht : (m + 1).choose 2 = (m + 1) * m / 2 := by simp [Nat.choose_two_right]
    rw [← ht] at hN
    subst N
    have hbase := triangular_family_bound m (by omega)
    have hstep := familyCount_add m r
    have hcount := familyCount_le ((m + 1).choose 2 + r)
    qify at hstep hcount
    linarith

end MathlibExt.Probability.DiversityStatisticsWanted
