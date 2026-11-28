/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Tail of the sum of inverse prime squares

The reciprocal squares of the primes above `n` sum to `O(1 / (n * log n))`.
-/

namespace MetaMathlibExt

open Finset Filter Real

/-- A linear bound for the prime count above `n` controls the reciprocal squares in
`(n, 2 ^ k * n]`. Doubling the lower endpoint halves the bound for the remaining tail. -/
private theorem sum_inv_sq_le_of_primeCounting_le (k : ℕ) {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 ≤ a) (hπ : ∀ m ≥ n, (m.primeCounting : ℝ) ≤ a * m)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ n < p ∧ p ≤ 2 ^ k * n) :
    ∑ p ∈ s, 1 / (p : ℝ) ^ 2 ≤ 4 * a / n := by
  induction k generalizing n s with
  | zero =>
    have he : s = ∅ := eq_empty_iff_forall_notMem.mpr fun p hp ↦ by
      simpa using (hs p hp).2.1.trans_le (hs p hp).2.2
    simp [he, show 0 ≤ 4 * a / (n : ℝ) by positivity]
  | succ k ih =>
    let lo := s.filter (· ≤ 2 * n)
    let hi := s.filter (¬ · ≤ 2 * n)
    have hcard : (lo.card : ℝ) ≤ a * (2 * n) := by
      have hsub : lo ⊆ (2 * n).primesLE := fun p hp ↦
        Nat.mem_primesLE.mpr ⟨(mem_filter.mp hp).2, (hs p (mem_filter.mp hp).1).1⟩
      have hc := card_le_card hsub
      rw [Nat.primesLE_card_eq_primeCounting] at hc
      exact_mod_cast (Nat.cast_le (α := ℝ).mpr hc).trans (hπ (2 * n) (by omega))
    have hlow : ∑ p ∈ lo, 1 / (p : ℝ) ^ 2 ≤ 2 * a / n := calc
      _ ≤ ∑ _p ∈ lo, 1 / (n : ℝ) ^ 2 := by
        refine sum_le_sum fun p hp ↦ ?_
        gcongr
        exact_mod_cast (hs p (mem_filter.mp hp).1).2.1.le
      _ = lo.card / (n : ℝ) ^ 2 := by simp [div_eq_mul_inv]
      _ ≤ a * (2 * n) / (n : ℝ) ^ 2 := by gcongr
      _ = _ := by field_simp
    have hhigh := ih (n := 2 * n) (by omega) (fun m hm ↦ hπ m (by omega)) hi
      (fun p hp ↦ by
        obtain ⟨hp, hp'⟩ := mem_filter.mp hp
        exact ⟨(hs p hp).1, lt_of_not_ge hp', by simpa [pow_succ, mul_assoc] using (hs p hp).2.2⟩)
    rw [← sum_filter_add_sum_filter_not s (· ≤ 2 * n)]
    refine (add_le_add hlow hhigh).trans_eq ?_
    push_cast
    ring

/-- **Tail of the sum of inverse prime squares.** As the natural number $n$ tends to infinity,
the sum $\sum_{p > n,\ p \text{ prime}} 1/p^2$ of the inverse squares of the primes greater
than $n$ is $O(1/(n \log n))$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 8 (`lem:psquared_sum_est`). -/
public theorem tsum_inv_sq_primes_gt_isBigO :
    (fun n : ℕ => ∑' p : {p : ℕ // p.Prime ∧ n < p}, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2)
      =O[Filter.atTop] (fun n : ℕ => 1 / ((n : ℝ) * Real.log n)) := by
  let C := log 4 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hπ : ∀ᶠ m : ℕ in atTop, (m.primeCounting : ℝ) ≤ C * m / log m := by
    simpa [C] using tendsto_natCast_atTop_atTop.eventually
      (Chebyshev.eventually_primeCounting_le one_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hπ
  apply Asymptotics.IsBigO.of_bound (4 * C)
  filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 1] with n hn hn₁
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn₁
  have hlog := log_pos hn'
  rw [Real.norm_of_nonneg (tsum_nonneg fun _ ↦ by positivity), Real.norm_of_nonneg (by positivity)]
  have hlinear (m : ℕ) (hm : n ≤ m) : (m.primeCounting : ℝ) ≤ C / log n * m := calc
    _ ≤ C * m / log m := hN m (hn.trans hm)
    _ ≤ C * m / log n := by gcongr
    _ = _ := by ring
  apply Real.tsum_le_of_sum_le (fun _ ↦ by positivity)
  intro s
  let t := s.map (Function.Embedding.subtype _)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (t.sup id) (by decide : 1 < (2 : ℕ))
  have h := sum_inv_sq_le_of_primeCounting_le k (by omega : 0 < n) (by positivity) hlinear t
    (fun p hp ↦ by
      have hle := (Finset.le_sup (f := id) hp).trans hk.le
      obtain ⟨q, _, rfl⟩ := mem_map.mp hp
      exact ⟨q.property.1, q.property.2, hle.trans (Nat.le_mul_of_pos_right _ (by omega))⟩)
  simpa [t, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end MetaMathlibExt
