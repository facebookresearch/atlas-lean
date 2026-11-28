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
private lemma realize_given_split {a b s k N : ℕ} (hk : k = a.choose 2 + b.choose 2 + s)
    (hN : a + b + 2 * s ≤ N) :
    ∃ l : List ℕ, l.sum = N ∧ (l.map (fun a => a ^ 2)).sum = N + 2 * k := by
  let u := N - (a + b + 2 * s)
  have hu : a + b + 2 * s + u = N := by dsimp [u]; omega
  refine ⟨a :: b :: (List.replicate s 2 ++ List.replicate u 1), ?_, ?_⟩
  · simpa [List.sum_replicate, nsmul_eq_mul, mul_comm, add_assoc] using hu
  · simp only [List.map_cons, List.map_append, List.map_replicate, List.sum_cons,
      List.sum_append, List.sum_replicate, nsmul_eq_mul, one_pow, mul_one]
    rw [hk]
    qify at hu ⊢
    rw [Nat.cast_choose_two, Nat.cast_choose_two]
    linarith

private lemma realize_pair_count {k m B N : ℕ} (hk : k ≤ m.choose 2)
    (hm : m ≤ B.choose 2) (hN : m + 3 * B ≤ N) :
    ∃ l : List ℕ, l.sum = N ∧ (l.map (fun a => a ^ 2)).sum = N + 2 * k := by
  obtain ⟨a, r, ha, hr, hkr⟩ := split_pair_count hk
  obtain ⟨b, s, hb, hs, hrs⟩ := split_pair_count (hr.trans hm)
  exact realize_given_split (a := a) (b := b) (s := s) (by omega) (by omega)

private lemma lower_count_of_realizations {K N : ℕ}
    (h : ∀ k ≤ K, ∃ l : List ℕ, l.sum = N ∧ (l.map (fun a => a ^ 2)).sum = N + 2 * k) :
    K + 1 ≤ giniSimpsonCount N := by
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
  have hsub : (fun k => N + 2 * k) '' Set.Iic K ⊆ values := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have hinj : Function.Injective (fun k : ℕ => N + 2 * k) := by
    intro a b h
    dsimp at h
    omega
  simpa only [values, giniSimpsonCount, Set.ncard_image_of_injective _ hinj,
    Set.ncard_Iic_nat] using Set.ncard_le_ncard hsub hfin

private lemma lower_count {m B N : ℕ} (hm : m ≤ B.choose 2) (hN : m + 3 * B ≤ N) :
    m.choose 2 + 1 ≤ giniSimpsonCount N :=
  lower_count_of_realizations fun _ hk => realize_pair_count hk hm hN

-- The largest block with triangular pair count at most k.
private def greedyBlockSize (k : ℕ) : ℕ := (1 + (1 + 8 * k).sqrt) / 2

-- For the bounded range, two greedy blocks and some pairs suffice. If their total size c
-- exceeds six, the inequality rules out any admissible sample size below c.
private lemma greedy_split_certificate :
    ∀ k : Fin 198,
      let a := greedyBlockSize k
      let r := (k : ℕ) - a.choose 2
      let b := greedyBlockSize r
      let s := r - b.choose 2
      let c := a + b + 2 * s
      (k : ℕ) = a.choose 2 + b.choose 2 + s ∧
        (c ≤ 6 ∨ (c - 6) * (c - 1) < 10 * (k : ℕ)) := by
  decide +kernel

private lemma realize_pair_count_small {N k : ℕ} (hN : 6 ≤ N) (hN' : N < 48)
    (hk : 5 * (N + 2 * k) ≤ N ^ 2) :
    ∃ l : List ℕ, l.sum = N ∧ (l.map (fun a => a ^ 2)).sum = N + 2 * k := by
  have hprod : 10 * k ≤ (N - 5) * N := by
    rw [Nat.sub_mul, ← pow_two]
    omega
  have hkFin : k < 198 := by
    have h := Nat.mul_le_mul (show N - 5 ≤ 42 by omega) (show N ≤ 47 by omega)
    omega
  let a := greedyBlockSize k
  let r := k - a.choose 2
  let b := greedyBlockSize r
  let s := r - b.choose 2
  let c := a + b + 2 * s
  have hcert : k = a.choose 2 + b.choose 2 + s ∧
      (c ≤ 6 ∨ (c - 6) * (c - 1) < 10 * k) := greedy_split_certificate ⟨k, hkFin⟩
  have hc : c ≤ N := by
    rcases hcert.2 with hc | hc
    · omega
    · by_contra! hn
      have h := Nat.mul_le_mul (show N - 5 ≤ c - 6 by omega) (show N ≤ c - 1 by omega)
      omega
  exact realize_given_split hcert.1 hc

-- For N ≥ 48, one block can use up to half the sample, leaving room for the correction.
private lemma quadratic_lower_bound_large {N : ℕ} (hN : 48 ≤ N) :
    (((N ^ 2 / 5 : ℕ) : ℚ) - N) / 2 ≤ (giniSimpsonCount N : ℚ) := by
  let m := N / 2
  let B := N / 6
  have hB : 8 ≤ B := by dsimp [B]; omega
  have hmB : m ≤ 3 * B + 2 := by dsimp [m, B]; omega
  have hchoose : 3 * B + 2 ≤ B.choose 2 := by
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by decide)]
    have h := Nat.mul_le_mul_left B (show 7 ≤ B - 1 by omega)
    omega
  have hbudget : m + 3 * B ≤ N := by dsimp [m, B]; omega
  have hc := lower_count (hmB.trans hchoose) hbudget
  let F := N ^ 2 / 5
  change ((F : ℚ) - N) / 2 ≤ _
  have hfloor : 5 * F ≤ N ^ 2 := by dsimp [F]; omega
  have hlo : 2 * m ≤ N := by dsimp [m]; omega
  have hhi : N ≤ 2 * m + 1 := by dsimp [m]; omega
  qify at hfloor hlo hhi hc
  rw [Nat.cast_choose_two] at hc
  have hsq : (N : ℚ) ^ 2 ≤ (2 * (m : ℚ) + 1) ^ 2 := by gcongr
  have hm0 : (0 : ℚ) ≤ m := by positivity
  nlinarith only [hfloor, hlo, hc, hsq, sq_nonneg (m : ℚ), hm0]

/-- **Quadratic lower bound on the number of Gini–Simpson values.** Let $\gamma(N)$ be the number of
distinct values of $a_1^2 + \dots + a_k^2$ over all finite sequences $(a_1, \dots, a_k)$ of natural
numbers with $a_1 + \dots + a_k = N$ (for $N \ge 1$, the number of possible values of the
Gini–Simpson index across samples of size $N$). Then for every natural number $N$,
$$\tfrac{1}{2} \left( \lfloor N^2 / 5 \rfloor - N \right) \le \gamma(N).$$

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 6. -/
theorem giniSimpsonCount_ge (N : ℕ) :
    (((N ^ 2 / 5 : ℕ) : ℚ) - N) / 2 ≤ (giniSimpsonCount N : ℚ) := by
  let F := N ^ 2 / 5
  change ((F : ℚ) - N) / 2 ≤ _
  by_cases hsmall : N ≤ 5
  · have hs : N ^ 2 ≤ N * 5 := by simpa [pow_two] using Nat.mul_le_mul_left N hsmall
    have hfloor : F ≤ N := by dsimp [F]; omega
    qify at hfloor
    have hnonneg : (0 : ℚ) ≤ giniSimpsonCount N := by positivity
    linarith only [hfloor, hnonneg]
  by_cases hlarge : 48 ≤ N
  · exact quadratic_lower_bound_large hlarge
  let K := (F - N) / 2
  have hs : N * 5 ≤ N ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left N (show 5 ≤ N by omega)
  have hN_le : N ≤ F := by dsimp [F]; omega
  have hcount : K + 1 ≤ giniSimpsonCount N := by
    apply lower_count_of_realizations
    intro k hk
    dsimp [K] at hk
    have hfloor : 5 * F ≤ N ^ 2 := by dsimp [F]; omega
    exact realize_pair_count_small (by omega) (by omega) (by omega)
  have hK : F ≤ N + 2 * K + 1 := by dsimp [K]; omega
  qify at hK hcount
  linarith only [hK, hcount]

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
