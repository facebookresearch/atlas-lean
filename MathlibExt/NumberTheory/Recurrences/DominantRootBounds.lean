/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.BigOperators

@[expose] public section

namespace MetaMathlibExt

-- Helper: geometric lower bound with base 19/10: the partial sums exceed 3m for m ≥ 4.
-- Proved by induction from m = 4; the step uses (19/10)^m ≥ (19/10)^4 > 3.
private lemma aux_sum_gt (m : ℕ) (hm : 4 ≤ m) :
    3 * (m : ℝ) < ∑ i ∈ Finset.range m, ((19 : ℝ) / 10) ^ i := by
  have hL1 : (1 : ℝ) ≤ 19 / 10 := by norm_num
  have hL4 : (3 : ℝ) < ((19 : ℝ) / 10) ^ 4 := by norm_num
  have hbase : (3 : ℝ) * 4 < ∑ i ∈ Finset.range 4, ((19 : ℝ) / 10) ^ i := by
    norm_num [Finset.sum_range_succ]
  induction m, hm using Nat.le_induction with
  | base => simpa using hbase
  | succ n hn ih =>
    have hpow : ((19 : ℝ) / 10) ^ 4 ≤ ((19 : ℝ) / 10) ^ n :=
      pow_le_pow_right₀ hL1 (by omega)
    have h3 : (3 : ℝ) < ((19 : ℝ) / 10) ^ n := lt_of_lt_of_le hL4 hpow
    have hsplit : ∑ i ∈ Finset.range (n + 1), ((19 : ℝ) / 10) ^ i
        = (∑ i ∈ Finset.range n, ((19 : ℝ) / 10) ^ i) + ((19 : ℝ) / 10) ^ n := by
      rw [Finset.sum_range_succ]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hsplit, hcast]
    linarith

/--
**Bounds on the dominant root of the k-generalized Fibonacci polynomial.** Let $k$ be a natural
number and let $\alpha > 1$ be a real number with $\alpha^k = \sum_{i=0}^{k-1} \alpha^i$. Then
$2 - 1/k < \alpha < 2$, and if $k \ge 4$, moreover $2 - 1/(3k) < \alpha < 2$.

Source: G. P. B. Dresden and Z. Du, *A Simplified Binet Formula for k-Generalized
Fibonacci Numbers*, Journal of Integer Sequences 17 (2014), Article 14.4.7, Lemma `La`,
line 350,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Dresden/dresden6.tex>.
Proves `Wanted` entry `dominant_root_bounds_k_generalized_fibonacci`.
-/
theorem dominant_root_bounds_k_generalized_fibonacci
    (k : ℕ)
    (α : ℝ)
    (hα : 1 < α)
    (hroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    (2 - 1 / (k : ℝ) < α ∧ α < 2) ∧
      (4 ≤ k → 2 - 1 / (3 * (k : ℝ)) < α ∧ α < 2) := by
  have hαpos : (0 : ℝ) < α := by linarith
  -- k = 0 is impossible: α^0 = 1 but the sum is empty = 0.
  by_cases hk0 : k = 0
  · subst hk0
    simp at hroot
  -- k = 1 is impossible: α^1 = α but the sum is α^0 = 1, contradicting 1 < α.
  by_cases hk1 : k = 1
  · subst hk1
    simp at hroot
    linarith
  -- Hence k ≥ 2.
  have hk2 : 2 ≤ k := by omega
  have hkposR : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact Nat.cast_pos.mpr this
  -- Geometric sum identity: S * (α - 1) = α^k - 1.
  have hgeom : (∑ i ∈ Finset.range k, α ^ i) * (α - 1) = α ^ k - 1 :=
    geom_sum_mul α k
  -- Key equation: α^k * (2 - α) = 1.
  have hkey : α ^ k * (2 - α) = 1 := by
    have hS : (∑ i ∈ Finset.range k, α ^ i) = α ^ k := hroot.symm
    rw [hS] at hgeom
    linear_combination -hgeom
  have hpowpos : (0 : ℝ) < α ^ k := pow_pos hαpos k
  -- Upper bound α < 2.
  have hαlt2 : α < 2 := by
    have h2 : (0 : ℝ) < 2 - α := pos_of_mul_pos_right (hkey ▸ zero_lt_one) (le_of_lt hpowpos)
    linarith
  -- Explicit form α = 2 - 1 / α^k.
  have hαeq : α = 2 - 1 / α ^ k := by
    field_simp
    linear_combination -hkey
  -- Each power is at least 1.
  have honele : ∀ i ∈ Finset.range k, (1 : ℝ) ≤ α ^ i := fun i _ => one_le_pow₀ (le_of_lt hα)
  -- Strict at i = 1 (which lies in range k since k ≥ 2).
  have hstrict : ∃ i ∈ Finset.range k, (1 : ℝ) < α ^ i := by
    refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
    simpa using hα
  have hsumgt : (k : ℝ) < α ^ k := by
    have hlt : ∑ _i ∈ Finset.range k, (1 : ℝ) < ∑ i ∈ Finset.range k, α ^ i :=
      Finset.sum_lt_sum honele hstrict
    rw [hroot]
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hlt
  -- First lower bound 2 - 1/k < α.
  have hlow1 : 2 - 1 / (k : ℝ) < α := by
    have hdiv : 1 / α ^ k < 1 / (k : ℝ) :=
      one_div_lt_one_div_of_lt hkposR hsumgt
    rw [hαeq]
    linarith
  refine ⟨⟨hlow1, hαlt2⟩, fun hk4 => ⟨?_, hαlt2⟩⟩
  -- Stronger bound for 4 ≤ k: it suffices to show 3k < α^k.
  have hk4R : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
  have h3kpos : (0 : ℝ) < 3 * (k : ℝ) := by linarith
  suffices h3k : 3 * (k : ℝ) < α ^ k by
    have hdiv : 1 / α ^ k < 1 / (3 * (k : ℝ)) :=
      one_div_lt_one_div_of_lt h3kpos h3k
    rw [hαeq]
    linarith
  -- Bootstrap step 1: α > 7/4.
  have hα74 : (7 : ℝ) / 4 < α := by
    have h1k : 1 / (k : ℝ) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hk4R
    linarith
  -- Bootstrap step 2: α^k > 715/64 (sum of the first four terms with base 7/4).
  have h715 : ((715 : ℝ) / 64) < α ^ k := by
    have h74nn : (0 : ℝ) ≤ 7 / 4 := by norm_num
    have hle : ∀ i ∈ Finset.range 4, ((7 : ℝ) / 4) ^ i ≤ α ^ i := by
      intro i _
      exact pow_le_pow_left₀ h74nn (le_of_lt hα74) i
    have hlt1 : ((7 : ℝ) / 4) ^ 1 < α ^ 1 := by
      simpa using hα74
    have hstrict4 : ∃ i ∈ Finset.range 4, ((7 : ℝ) / 4) ^ i < α ^ i := by
      exact ⟨1, Finset.mem_range.mpr (by norm_num), hlt1⟩
    have hsum4lt : ∑ i ∈ Finset.range 4, ((7 : ℝ) / 4) ^ i
        < ∑ i ∈ Finset.range 4, α ^ i :=
      Finset.sum_lt_sum hle hstrict4
    have hval : ∑ i ∈ Finset.range 4, ((7 : ℝ) / 4) ^ i = 715 / 64 := by
      norm_num [Finset.sum_range_succ]
    have hsub : ∑ i ∈ Finset.range 4, α ^ i ≤ ∑ i ∈ Finset.range k, α ^ i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_subset_range.mpr hk4
      · intro i _ _
        exact le_of_lt (pow_pos hαpos i)
    rw [hval] at hsum4lt
    rw [hroot]
    linarith
  -- Bootstrap step 3: α > 19/10.
  have hα1910 : (19 : ℝ) / 10 < α := by
    have hdiv : 1 / α ^ k < 1 / (715 / 64) :=
      one_div_lt_one_div_of_lt (by norm_num) h715
    have h64 : (1 : ℝ) / (715 / 64) = 64 / 715 := by norm_num
    rw [hαeq]
    have hbound : (2 : ℝ) - 1 / (715 / 64) = 1366 / 715 := by norm_num
    have h1910 : (19 : ℝ) / 10 < 1366 / 715 := by norm_num
    linarith
  -- Finish: compare against the 19/10 geometric sum, which exceeds 3k.
  have hLnn : (0 : ℝ) ≤ 19 / 10 := by norm_num
  have hterm : ∀ i ∈ Finset.range k, ((19 : ℝ) / 10) ^ i ≤ α ^ i := by
    intro i _
    exact pow_le_pow_left₀ hLnn (le_of_lt hα1910) i
  have hsumL : ∑ i ∈ Finset.range k, ((19 : ℝ) / 10) ^ i ≤ ∑ i ∈ Finset.range k, α ^ i :=
    Finset.sum_le_sum hterm
  have haux := aux_sum_gt k hk4
  rw [← hroot] at hsumL
  linarith

end MetaMathlibExt
