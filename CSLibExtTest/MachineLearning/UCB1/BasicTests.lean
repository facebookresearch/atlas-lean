/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.UCB1.Basic

/-!
# UCB1 tests

The index of an arm on concrete rewards; the least-index run plays the arms in order first and
breaks a tie toward arm `0`; on measurable reward stacks its pull counts are random variables;
a run of UCB1 may play the first arms in another order and break ties otherwise; and a sequence
that skips a maximizer is not a run.
-/

namespace Cslib.MachineLearning.UCB1

open Real Finset MeasureTheory

-- The index of an arm played twice, with rewards `1/2` and `1`, after four plays.
example (x : Fin 2 → ℕ → ℝ) (h0 : x 0 0 = 1 / 2) (h1 : x 0 1 = 1) :
    ucb1Index x 4 ![2, 2] 0 = 3 / 4 + √(log 4) := by
  simp [ucb1Index, sum_range_succ, h0, h1]
  norm_num

-- The least-index run plays the arms in order first.
example (x : Fin 3 → ℕ → ℝ) : ucb1Arm x 0 = 0 ∧ ucb1Arm x 1 = 1 ∧ ucb1Arm x 2 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [ucb1Arm] <;> rfl

-- With two arms and all rewards `0`, both indices after two plays are `√(2 ln 2)`: the tie goes to
-- arm `0`.
example : ucb1Arm (K := 2) (fun _ _ ↦ 0) 2 = 0 := by
  set x : Fin 2 → ℕ → ℝ := fun _ _ ↦ 0
  have hcard : ∀ j : Fin 2, ((range 2).attach.filter fun u ↦ ucb1Arm x u.1 = j).card = 1 :=
    fun j ↦ by
      rw [filter_attach (fun u ↦ ucb1Arm x u = j), card_map, card_attach,
        ← Nat.count_eq_card_filter_range]
      exact (isUCB1Run_ucb1Arm x).1 j
  rw [ucb1Arm.eq_1, dite_eq_right (by norm_num)]
  simp only [hcard]
  have hmax : (List.finRange 2).argmax (ucb1Index x 2 fun _ ↦ 1) = some 0 := by
    rw [List.argmax_eq_some_iff]
    refine ⟨List.mem_finRange 0, fun a _ ↦ ?_, fun a _ _ ↦ ?_⟩
    · simp [ucb1Index, x]
    · simp
  rw [hmax, Option.getD_some]

-- On measurable reward stacks, the pull counts of the least-index run are random variables.
example {K : ℕ} [NeZero K] {Ω : Type*} [MeasurableSpace Ω] {X : Fin K → ℕ → Ω → ℝ}
    (hX : ∀ j m, Measurable (X j m)) (i : Fin K) (n : ℕ) :
    Measurable fun ω ↦ Nat.count (ucb1Arm (fun j m ↦ X j m ω) · = i) n := by
  have hx : Measurable fun ω ↦ fun j m ↦ X j m ω :=
    measurable_pi_iff.mpr fun j ↦ measurable_pi_iff.mpr fun m ↦ hX j m
  simp only [Nat.count_eq_card_filter_range, card_filter]
  refine Finset.measurable_sum _ fun u _ ↦ Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_eq_fun ((measurable_ucb1Arm u).comp hx) measurable_const

/-- Two arms played alternately, starting with arm `1`. -/
private def alt (t : ℕ) : Fin 2 := if t % 2 = 0 then 1 else 0

private lemma count_alt_one (t : ℕ) : Nat.count (alt · = 1) t = (t + 1) / 2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Nat.count_succ, ih]
    by_cases h : t % 2 = 0 <;> simp [alt, h] <;> omega

private lemma count_alt_zero (t : ℕ) : Nat.count (alt · = 0) t = t / 2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Nat.count_succ, ih]
    by_cases h : t % 2 = 0 <;> simp [alt, h] <;> omega

-- With all rewards `0`, playing the arms alternately, starting with arm `1`, is a run of UCB1:
-- the first two plays come in the other order than in `ucb1Arm`, and the ties after an even
-- number of plays go to arm `1`.
example : IsUCB1Run (K := 2) (fun _ _ ↦ 0) alt := by
  have hidx : ∀ t (c : Fin 2 → ℕ) j, ucb1Index (fun _ _ ↦ 0) t c j = √(2 * log t / c j) :=
    fun t c j ↦ by simp [ucb1Index]
  refine ⟨fun j ↦ ?_, fun t ht j ↦ ?_⟩
  · fin_cases j
    · exact count_alt_zero 2
    · exact count_alt_one 2
  simp only [hidx]
  have hlog : 0 ≤ log t := log_natCast_nonneg t
  by_cases h : t % 2 = 0
  · have hA : alt t = 1 := by simp [alt, h]
    rw [hA]
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, count_alt_zero, count_alt_one]
      rw [show (t + 1) / 2 = t / 2 by omega]
    · exact le_rfl
  · have hA : alt t = 0 := by simp [alt, h]
    rw [hA]
    fin_cases j
    · exact le_rfl
    · simp only [Fin.isValue, count_alt_zero, Fin.mk_one, count_alt_one]
      refine sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity) ?_ ?_)
      · exact_mod_cast (by omega : 0 < t / 2)
      · exact_mod_cast (by omega : t / 2 ≤ (t + 1) / 2)

/-- Play arm `0`, then arm `1` forever. -/
private def zeroThenOne (t : ℕ) : Fin 2 := if t = 0 then 0 else 1

-- A sequence that skips a maximizer is not a run: when arm `0` pays `1` and arm `1` pays `0`,
-- after the plays `0, 1` the index of arm `0` exceeds that of arm `1` by `1`, so a third play of
-- arm `1` is not a play of UCB1.
example : ¬ IsUCB1Run (K := 2) (fun j _ ↦ if j = 0 then 1 else 0) zeroThenOne := by
  intro h
  have h2 := h.2 2 le_rfl 0
  have c0 : Nat.count (zeroThenOne · = 0) 2 = 1 := by decide
  have c1 : Nat.count (zeroThenOne · = 1) 2 = 1 := by decide
  have hA : zeroThenOne 2 = 1 := rfl
  simp only [ucb1Index, hA, c0, c1] at h2
  norm_num at h2

end Cslib.MachineLearning.UCB1
