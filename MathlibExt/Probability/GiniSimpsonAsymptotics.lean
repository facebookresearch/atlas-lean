/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DiversityStatistics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Qify

/-!
# Asymptotics of the number of Gini–Simpson values

The number of distinct sums of squared type counts at sample size `N` is asymptotic to
`N ^ 2 / 2`. We realize a whole interval of pair counts using two triangular numbers
and a remainder supplied by types of size two.
-/

public section

namespace MathlibExt.Probability.DiversityStatisticsWanted

-- Consecutive triangular numbers up to m.choose 2 have gaps of at most m.
private lemma split_pair_count {k m : ℕ} (hk : k ≤ m.choose 2) :
    ∃ a r : ℕ, a ≤ m ∧ r ≤ m ∧ k = a.choose 2 + r := by
  induction m with
  | zero =>
    exact ⟨0, 0, le_rfl, le_rfl, by simpa using hk⟩
  | succ m ih =>
    by_cases h : k ≤ m.choose 2
    · obtain ⟨a, r, ha, hr, heq⟩ := ih h
      exact ⟨a, r, by omega, by omega, heq⟩
    · rw [Nat.choose_succ_succ, Nat.choose_one_right] at hk
      change k ≤ m + m.choose 2 at hk
      exact ⟨m, k - m.choose 2, by omega, by omega, by omega⟩

-- Use blocks of sizes a and b for the triangular summands, s pairs for the remainder,
-- and singletons for the unused sample.
private lemma realize_pair_count {k m B N : ℕ} (hk : k ≤ m.choose 2)
    (hm : m ≤ B.choose 2) (hN : m + 3 * B ≤ N) :
    ∃ l : List ℕ, l.sum = N ∧ (l.map (fun a => a ^ 2)).sum = N + 2 * k := by
  obtain ⟨a, r, ha, hr, hkr⟩ := split_pair_count hk
  obtain ⟨b, s, hb, hs, hrs⟩ := split_pair_count (hr.trans hm)
  let u := N - (a + b + 2 * s)
  have hu : a + b + 2 * s + u = N := by dsimp [u]; omega
  refine ⟨a :: b :: (List.replicate s 2 ++ List.replicate u 1), ?_, ?_⟩
  · simpa [List.sum_replicate, nsmul_eq_mul, mul_comm, add_assoc] using hu
  · simp only [List.map_cons, List.map_append, List.map_replicate, List.sum_cons,
      List.sum_append, List.sum_replicate, nsmul_eq_mul, one_pow, mul_one]
    rw [hkr, hrs]
    qify at hu ⊢
    rw [Nat.cast_choose_two, Nat.cast_choose_two]
    linarith

private lemma lower_count {m B N : ℕ} (hm : m ≤ B.choose 2) (hN : m + 3 * B ≤ N) :
    m.choose 2 + 1 ≤ giniSimpsonCount N := by
  let values := {s : ℕ | ∃ l : List ℕ, l.sum = N ∧ (l.map (fun a => a ^ 2)).sum = s}
  have hfin : values.Finite := by
    apply (Set.finite_Iic (N ^ 2)).subset
    rintro _ ⟨l, hl, rfl⟩
    rw [← hl]
    clear hl
    change (l.map (fun a => a ^ 2)).sum ≤ l.sum ^ 2
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      nlinarith only [ih, Nat.zero_le (a * l.sum)]
  have hsub : (fun k => N + 2 * k) '' Set.Iic (m.choose 2) ⊆ values := by
    rintro _ ⟨k, hk, rfl⟩
    exact realize_pair_count hk hm hN
  have hinj : Function.Injective (fun k : ℕ => N + 2 * k) := by
    intro a b h
    dsimp at h
    omega
  simpa only [values, giniSimpsonCount, Set.ncard_image_of_injective _ hinj,
    Set.ncard_Iic_nat] using Set.ncard_le_ncard hsub hfin

-- At sample size (t + 3)² there is room for the first block of size at most t² + 1
-- and for the correction of size at most 3(2t + 2).
private lemma lower_count_sq {t N : ℕ} (hN : (t + 3) ^ 2 ≤ N) :
    t ^ 4 ≤ 2 * giniSimpsonCount N := by
  have hm : t ^ 2 + 1 ≤ (2 * t + 2).choose 2 := by
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by decide)]
    rw [show 2 * t + 2 - 1 = 2 * t + 1 by omega]
    nlinarith
  have hc := lower_count hm (N := N) (by nlinarith)
  qify at hc ⊢
  rw [Nat.cast_choose_two] at hc
  push_cast at hc
  nlinarith

/-- **Asymptotics of the number of Gini–Simpson values.** Let $\gamma(N)$ be the number of distinct
values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$ of natural numbers
with $a_1 + \dots + a_k = N$ (for $N \ge 1$, the number of possible values of the Gini–Simpson index
across samples of size $N$). Then $\gamma(N) / N^2 \to 1/2$ as $N \to \infty$, that is, $\gamma(N)
\sim \tfrac{1}{2} N^2$.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 7. -/
theorem giniSimpsonCount_asymp :
    Filter.Tendsto
      (fun N : ℕ => (giniSimpsonCount N : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (1 / 2)) := by
  let t (N : ℕ) := N.sqrt - 3
  have hsqrt : Filter.Tendsto Nat.sqrt Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_atTop.mpr fun k => ⟨k ^ 2, fun _ hn => Nat.le_sqrt'.mpr hn⟩
  have ht : Filter.Tendsto t Filter.atTop Filter.atTop :=
    (Filter.tendsto_sub_atTop_nat 3).comp hsqrt
  have hlim := ((tendsto_natCast_div_add_atTop (4 : ℝ)).comp ht).pow 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun N => (((t N : ℝ) / (t N + 4)) ^ 4) / 2) (h := fun _ => 1 / 2)
  · simpa using hlim.div_const 2
  · exact tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop 9] with N hN
    have ht3 : t N + 3 = N.sqrt := Nat.sub_add_cancel (Nat.le_sqrt'.mpr hN)
    have hlo : (t N + 3) ^ 2 ≤ N := ht3 ▸ Nat.sqrt_le' N
    have hhi : N ≤ (t N + 4) ^ 2 := by
      have heq : t N + 4 = N.sqrt.succ := by omega
      rw [heq]
      exact (Nat.lt_succ_sqrt' N).le
    have hc : (t N : ℝ) ^ 4 ≤ 2 * giniSimpsonCount N := by
      exact_mod_cast lower_count_sq hlo
    have hi : (N : ℝ) ≤ ((t N : ℝ) + 4) ^ 2 := by exact_mod_cast hhi
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      (t N : ℝ) ^ 4 * (N : ℝ) ^ 2 ≤
          (2 * giniSimpsonCount N : ℝ) * (((t N : ℝ) + 4) ^ 2) ^ 2 := by gcongr
      _ = _ := by ring
  · filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hu := (Rat.cast_le (K := ℝ)).mpr (giniSimpsonCount_le N)
    push_cast at hu
    have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
    apply (div_le_iff₀ (by positivity)).mpr
    linarith

end MathlibExt.Probability.DiversityStatisticsWanted
