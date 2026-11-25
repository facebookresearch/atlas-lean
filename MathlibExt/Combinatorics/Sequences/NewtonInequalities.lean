/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.SuccPred.Nat
import Mathlib.Data.Nat.Find

/-!
# Unimodality from Newton's inequalities

For a positive sequence, Newton's inequalities make the ratios of consecutive terms strictly
decreasing. Their position relative to one determines the peak.
-/

namespace MetaMathlibExt

/-- **Positive sequences satisfying Newton's inequalities are unimodal.** Let $n$ be a natural
number and let $(a_j)_{j \ge 0}$ be a sequence of real numbers with $a_j > 0$ for every $j \le n$,
such that
$$a_j^2 \ge \frac{j + 1}{j} \cdot \frac{n - j + 1}{n - j} \, a_{j-1} a_{j+1}$$
for every $j$ with $1 \le j \le n - 1$. Then there is an $m \le n$ such that $(a_j)$ is strictly
increasing on $\{0, \dots, m\}$, and either $(a_j)$ is strictly decreasing on $\{m, \dots, n\}$,
or $m < n$, $a_m = a_{m+1}$ and $(a_j)$ is strictly decreasing on $\{m + 1, \dots, n\}$.

The paper's "SLC" conclusion is not stated (the abbreviation is not defined in the extracted
statement).

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Corollary 1 (`integers-2024-A54-cor-1`). -/
public theorem unimodal_of_newton_inequalities {a : ℕ → ℝ} {n : ℕ}
    (hpos : ∀ j ≤ n, 0 < a j)
    (hnewton : ∀ j, 1 ≤ j → j ≤ n - 1 →
      ((j + 1 : ℝ) / j) * (((n : ℝ) - j + 1) / ((n : ℝ) - j)) * (a (j - 1) * a (j + 1)) ≤
        a j ^ 2) :
    ∃ m ≤ n, StrictMonoOn a (Set.Icc 0 m) ∧
      (StrictAntiOn a (Set.Icc m n) ∨
        (m < n ∧ a m = a (m + 1) ∧ StrictAntiOn a (Set.Icc (m + 1) n))) := by
  have hconc (j : ℕ) (hj : 0 < j) (hjn : j < n) :
      a (j - 1) * a (j + 1) < a j ^ 2 := by
    have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
    have hdiff : 0 < (n : ℝ) - j := sub_pos.mpr (Nat.cast_lt.mpr hjn)
    have h₁ : 1 < ((j : ℝ) + 1) / j := (one_lt_div hj').mpr (lt_add_one _)
    have h₂ : 1 < ((n : ℝ) - j + 1) / ((n : ℝ) - j) :=
      (one_lt_div hdiff).mpr (lt_add_one _)
    have hprod := mul_pos (hpos (j - 1) (by omega)) (hpos (j + 1) hjn)
    exact (lt_mul_of_one_lt_left hprod (one_lt_mul_of_le_of_lt h₁.le h₂)).trans_le
      (hnewton j hj (by omega))
  have hratio : StrictAntiOn (fun i => a (i + 1) / a i) (Set.Iio n) := by
    apply strictAntiOn_of_add_one_lt Set.ordConnected_Iio
    intro i _ hi hi'
    apply (div_lt_div_iff₀ (hpos _ hi'.le) (hpos _ hi.le)).mpr
    simpa [sq, mul_comm] using hconc (i + 1) (Nat.zero_lt_succ _) hi'
  -- Stop at the first nonincreasing step, or at the endpoint if every step increases.
  classical
  have hex : ∃ i, i = n ∨ a (i + 1) ≤ a i := ⟨n, Or.inl rfl⟩
  let m := Nat.find hex
  have hmn : m ≤ n := Nat.find_min' hex (Or.inl rfl)
  refine ⟨m, hmn, strictMonoOn_of_lt_add_one Set.ordConnected_Icc ?_, ?_⟩
  · intro i _ _ hi
    exact lt_of_not_ge fun h => Nat.find_min hex (Nat.lt_of_succ_le hi.2) (Or.inr h)
  rcases hmn.eq_or_lt with hend | hmn'
  · simp [hend]
  · have hstep : a (m + 1) ≤ a m := (Nat.find_spec hex).resolve_left hmn'.ne
    have hdrop {i : ℕ} (hmi : m < i) (hin : i < n) : a (i + 1) < a i := by
      apply (div_lt_one (hpos _ hin.le)).mp
      exact (hratio (hmi.trans hin) hin hmi).trans_le ((div_le_one (hpos _ hmn)).mpr hstep)
    rcases hstep.lt_or_eq with hlt | heq
    · left
      apply strictAntiOn_of_add_one_lt Set.ordConnected_Icc
      intro i _ hi hi'
      rcases hi.1.eq_or_lt with rfl | hmi
      · exact hlt
      · exact hdrop hmi hi'.2
    · refine Or.inr ⟨hmn', heq.symm, ?_⟩
      exact strictAntiOn_of_add_one_lt Set.ordConnected_Icc fun _ _ hi hi' => hdrop hi.1 hi'.2

end MetaMathlibExt
