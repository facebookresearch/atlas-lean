/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Combinatorics.BridgeTorchTwo
import Mathlib.Tactic.IntervalCases

/-! # An upper bound for the bridge and torch problem with capacity three

We prove `bridgeTime_three_le_closed_form`: for $n \ge 7$ people with crossing times
$1, \dots, n$ on a bridge of capacity $3$ with one torch, the optimal crossing time is at most
$n^2/6 + 2n - 181/36 + (-1)^n/4 - (2/9)\cos(2n\pi/3)$.

The theorem `closedForm_U_integral_and_near_V` shows that this bound is an integer in
$[V(n), V(n) + 1)$, where $V(n) = n^2/6 + 2n - 11/2$.

Explicit schedules for $7, \dots, 12$ people meet the bound. For $k \ge 9$ people, the three
fastest people ferry the six slowest across, three at a time, in six crossings of total time
$2k + 6$, after which $1, \dots, k - 6$ and the torch are on the left bank; these are the six
moves of the arXiv version of the source (arXiv:2608.05190v1, proof of Proposition 8,
Figure 5). Applying these moves before an optimal schedule for $k - 6$ gives
`bridgeTime_three_le_sub_six`. The closed-form bound grows by the same amount from $k - 6$ to $k$,
since its oscillating part has period $6$.
-/

set_option autoImplicit false

@[expose] public section

namespace MetaMathlibExt.BridgeTorchGeneralizations

open Finset

-- People already on the right bank may stay there for the rest of a schedule.
private theorem scheduleFrom_mono {c : ℕ} {P Q L : Finset ℕ} {side : Bool}
    {σ : List (Finset ℕ)} (hPQ : P ⊆ Q) (hσ : bridgeScheduleFrom c P L side σ = true) :
    bridgeScheduleFrom c Q L side σ = true := by
  induction σ generalizing L side with
  | nil => exact hσ
  | cons A σ ih =>
    cases side <;> simp only [bridgeScheduleFrom, Bool.and_eq_true, decide_eq_true_eq] at *
    · exact ⟨⟨hσ.1.1, hσ.1.2.1, hσ.1.2.2.trans (sdiff_subset_sdiff_left L hPQ)⟩, ih hσ.2⟩
    · exact ⟨hσ.1, ih hσ.2⟩

-- Send 1, 2, 3; bring 1 back; send the three slowest; bring 2 back; send the next three
-- slowest; bring 3 back.
private def sixStep (m : ℕ) (σ : List (Finset ℕ)) : List (Finset ℕ) :=
  {1, 2, 3} :: {1} :: {m + 4, m + 5, m + 6} :: {2} :: {m + 1, m + 2, m + 3} :: {3} :: σ

private theorem sixStep_valid {m : ℕ} (hm : 3 ≤ m) {σ : List (Finset ℕ)}
    (hσ : IsBridgeSchedule 3 m σ) : IsBridgeSchedule 3 (m + 6) (sixStep m σ) := by
  have htail := scheduleFrom_mono (Icc_subset_Icc_right (by omega : m ≤ m + 6)) hσ
  have hbank : ((((Icc 1 (m + 6) \ {1, 2, 3}) ∪ {1}) \ {m + 4, m + 5, m + 6}) ∪ {2}) \
      {m + 1, m + 2, m + 3} ∪ {3} = Icc 1 m := by
    ext i
    simp only [mem_union, mem_sdiff, mem_Icc, mem_insert, mem_singleton]
    omega
  simp only [IsBridgeSchedule, sixStep, bridgeScheduleFrom, Bool.and_eq_true,
    decide_eq_true_eq, hbank, htail, and_true]
  simp [insert_subset_iff, mem_sdiff, mem_Icc]
  omega

private theorem sixStep_cost (m : ℕ) (σ : List (Finset ℕ)) :
    scheduleCost (sixStep m σ) = scheduleCost σ + (2 * (m + 6) + 6) := by
  simp [scheduleCost, sixStep, sup_insert]
  omega

-- Person 1 can ferry each additional person across and return for the original schedule.
private theorem exists_schedule_three (n : ℕ) (hn : 1 ≤ n) : ∃ σ, IsBridgeSchedule 3 n σ := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨[{1}], by unfold IsBridgeSchedule; decide⟩
  | succ n hn ih =>
    obtain ⟨σ, hσ⟩ := ih
    refine ⟨{1, n + 1} :: {1} :: σ, ?_⟩
    have htail := scheduleFrom_mono (Icc_subset_Icc_right (Nat.le_succ n)) hσ
    have hbank : (Icc 1 (n + 1) \ {1, n + 1}) ∪ {1} = Icc 1 n := by
      ext i
      simp only [mem_union, mem_sdiff, mem_Icc, mem_insert, mem_singleton]
      omega
    simp only [IsBridgeSchedule, bridgeScheduleFrom, Bool.and_eq_true, decide_eq_true_eq,
      hbank, htail, and_true]
    simp [insert_subset_iff, mem_Icc, card_pair (by omega : 1 ≠ n + 1)]

/-- **Six-step upper bound for capacity three.** Let $T_3(n)$ be the optimal crossing time of
$n$ people with crossing times $1, \dots, n$ on a bridge of capacity $3$ with one torch. For
every $k \ge 9$, $T_3(k) \le T_3(k - 6) + 2k + 6$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 11 (`jis-2026-26.5.6-prop-11`). -/
theorem bridgeTime_three_le_sub_six (k : ℕ) (hk : 9 ≤ k) :
    bridgeTime 3 k ≤ bridgeTime 3 (k - 6) + 2 * k + 6 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
  obtain ⟨τ, hτ⟩ := exists_schedule_three m (by omega)
  obtain ⟨σ, hσ, hcost⟩ := Nat.sInf_mem
    (s := {t | ∃ σ, IsBridgeSchedule 3 m σ ∧ scheduleCost σ = t}) ⟨_, τ, hτ, rfl⟩
  change scheduleCost σ = bridgeTime 3 m at hcost
  have h := bridgeTime_le_scheduleCost (sixStep_valid (by omega : 3 ≤ m) hσ)
  rw [sixStep_cost, hcost] at h
  simpa [Nat.add_assoc] using h

-- The bound of the main theorem.
private noncomputable def closedForm (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 - 2 / 9 * Real.cos (2 * n * Real.pi / 3)

private theorem cos_two_mul_pi_div_three (n : ℕ) :
    Real.cos (2 * n * Real.pi / 3) = if n % 3 = 0 then 1 else -1 / 2 := by
  have hn : (n : ℝ) = 3 * (n / 3 : ℕ) + (n % 3 : ℕ) := by exact_mod_cast (Nat.div_add_mod n 3).symm
  rw [show 2 * (n : ℝ) * Real.pi / 3 = 2 * (n % 3 : ℕ) * Real.pi / 3 + (n / 3 : ℕ) * (2 * Real.pi)
    by rw [hn]; ring, Real.cos_add_nat_mul_two_pi]
  obtain ⟨r, hr, hnr⟩ : ∃ r, r < 3 ∧ n % 3 = r := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
  rw [hnr]
  interval_cases r
  · simp
  · rw [show 2 * ((1 : ℕ) : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · rw [show 2 * ((2 : ℕ) : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi by push_cast; ring,
      Real.cos_add_pi, Real.cos_pi_div_three]
    norm_num

-- The oscillating part of the bound has period 6.
private theorem closedForm_add_six (m : ℕ) :
    closedForm (m + 6) = closedForm m + (2 * (m + 6) + 6 : ℕ) := by
  have hcos : Real.cos (2 * ((m + 6 : ℕ) : ℝ) * Real.pi / 3) =
      Real.cos (2 * m * Real.pi / 3) := by
    rw [show 2 * ((m + 6 : ℕ) : ℝ) * Real.pi / 3 = 2 * m * Real.pi / 3 + (2 : ℕ) * (2 * Real.pi)
      by push_cast; ring, Real.cos_add_nat_mul_two_pi]
  simp only [closedForm, hcos, pow_add]
  push_cast
  ring

private theorem exists_of_cost {n c : ℕ} {σ : List (Finset ℕ)} (hσ : IsBridgeSchedule 3 n σ)
    (hc : scheduleCost σ = c) (h : (c : ℝ) ≤ closedForm n) :
    ∃ σ, IsBridgeSchedule 3 n σ ∧ (scheduleCost σ : ℝ) ≤ closedForm n :=
  ⟨σ, hσ, hc ▸ h⟩

private theorem exists_schedule_le_closedForm (n : ℕ) (hn : 7 ≤ n) :
    ∃ σ, IsBridgeSchedule 3 n σ ∧ (scheduleCost σ : ℝ) ≤ closedForm n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hsmall : n ≤ 12
    · have hU : closedForm n = (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
          2 / 9 * (if n % 3 = 0 then 1 else -1 / 2) := by
        rw [closedForm, cos_two_mul_pi_div_three]
      interval_cases n
      · exact exists_of_cost (σ := [{1, 2, 3}, {1}, {5, 6, 7}, {2}, {1, 2, 4}]) (c := 17)
          (by unfold IsBridgeSchedule; decide) (by decide) (by rw [hU]; norm_num)
      · exact exists_of_cost (c := 22)
          (σ := [{1, 2, 3}, {1}, {6, 7, 8}, {2}, {1, 4, 5}, {1}, {1, 2}])
          (by unfold IsBridgeSchedule; decide) (by decide) (by rw [hU]; norm_num)
      · exact exists_of_cost (c := 26)
          (σ := [{1, 2, 3}, {1}, {7, 8, 9}, {2}, {1, 5, 6}, {1}, {1, 2, 4}])
          (by unfold IsBridgeSchedule; decide) (by decide) (by rw [hU]; norm_num)
      · exact exists_of_cost (c := 32)
          (σ := [{1, 2, 3}, {1}, {8, 9, 10}, {2}, {1, 6, 7}, {1}, {1, 4, 5}, {1}, {1, 2}])
          (by unfold IsBridgeSchedule; decide) (by decide) (by rw [hU]; norm_num)
      · exact exists_of_cost (c := 37)
          (σ := [{1, 2, 3}, {1}, {9, 10, 11}, {2}, {1, 7, 8}, {1}, {1, 5, 6}, {1}, {1, 2, 4}])
          (by unfold IsBridgeSchedule; decide) (by decide) (by rw [hU]; norm_num)
      · exact exists_of_cost (c := 43)
          (σ := [{1, 2, 3}, {1}, {10, 11, 12}, {2}, {1, 2, 4}, {1}, {7, 8, 9}, {2}, {1, 5, 6},
            {1}, {1, 2}])
          (by unfold IsBridgeSchedule; decide) (by decide) (by rw [hU]; norm_num)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      obtain ⟨σ, hσ, hcost⟩ := ih m (by omega) (by omega)
      refine ⟨sixStep m σ, sixStep_valid (by omega) hσ, ?_⟩
      rw [sixStep_cost, closedForm_add_six, Nat.cast_add]
      exact add_le_add_left hcost _

/-- **Upper bound for capacity three.** Let $T_3(n)$ be the optimal crossing time of $n$ people
with crossing times $1, \dots, n$ on a bridge of capacity $3$ with one torch. For every
$n \ge 7$,
$$T_3(n) \le \frac{n^2}{6} + 2n - \frac{181}{36} + \frac{(-1)^n}{4} - \frac{2}{9}\cos(2n\pi/3).$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 12 (`jis-2026-26.5.6-thm-12`). -/
theorem bridgeTime_three_le_closed_form (n : ℕ) (hn : 7 ≤ n) :
    (bridgeTime 3 n : ℝ) ≤ (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
      2 / 9 * Real.cos (2 * n * Real.pi / 3) := by
  obtain ⟨σ, hσ, hcost⟩ := exists_schedule_le_closedForm n hn
  exact (Nat.cast_le.mpr (bridgeTime_le_scheduleCost hσ)).trans hcost

/-- **The capacity-3 closed form is an integer close to the lower bound.** For every integer
$n \ge 7$, let $U(n) = n^2/6 + 2n - 181/36 + (-1)^n/4 - (2/9)\cos(2n\pi/3)$ and
$V(n) = n^2/6 + 2n - 11/2$. Then $U(n)$ is an integer and $0 \le U(n) - V(n) < 1$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 19 (`jis-2026-26.5.6-lem-19`), with `U` from Theorem 12 and `V` from
Proposition 17. -/
theorem closedForm_U_integral_and_near_V (n : ℕ) (hn : 7 ≤ n) :
    (∃ z : ℤ, (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
        2 / 9 * Real.cos (2 * n * Real.pi / 3) = z) ∧
      0 ≤ ((n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
          2 / 9 * Real.cos (2 * n * Real.pi / 3)) - ((n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2) ∧
      ((n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
          2 / 9 * Real.cos (2 * n * Real.pi / 3)) - ((n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2) < 1 := by
  change (∃ z : ℤ, closedForm n = z) ∧
    0 ≤ closedForm n - ((n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2) ∧
    closedForm n - ((n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2) < 1
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hsmall : n ≤ 12
    · refine ⟨⟨⌊closedForm n⌋, ?_⟩, ?_⟩ <;> rw [closedForm, cos_two_mul_pi_div_three] <;>
        interval_cases n <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      obtain ⟨⟨z, hz⟩, hgap⟩ := ih m (by omega) (by omega)
      rw [closedForm_add_six]
      refine ⟨⟨z + (2 * (m + 6) + 6 : ℕ), by simp [hz]⟩, ?_⟩
      have hV : ((m + 6 : ℕ) : ℝ) ^ 2 / 6 + 2 * (m + 6 : ℕ) - 11 / 2 =
          (m : ℝ) ^ 2 / 6 + 2 * m - 11 / 2 + (2 * (m + 6) + 6 : ℕ) := by
        push_cast
        ring
      rw [hV]
      simpa using hgap

end MetaMathlibExt.BridgeTorchGeneralizations
