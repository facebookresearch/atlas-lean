/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Optimal crossing time for a bridge of capacity two

The sum of the weights on the left bank, with a correction for the side of the torch,
gives a lower bound on the remaining cost. The two fastest people can ferry the torch
so that the two slowest cross together, attaining the bound recursively.
-/

set_option autoImplicit false

@[expose] public section

namespace MetaMathlibExt.BridgeTorchGeneralizations

open Finset

/-- **Valid crossing sequences from a state of the bridge and torch problem.** Let $c$ be a
natural number and let $P$ and $L$ be finite sets of natural numbers, the people and the left
bank. Whether a finite sequence $A_1, \dots, A_k$ of finite sets of natural numbers (the
crossings) is valid from the left bank $L$ with the torch on a given side is defined by recursion
on $k$. The empty sequence is valid exactly when $L = \emptyset$ and the torch is on the right.
With the torch on the left, the sequence is valid when $A_1$ is a nonempty subset of $L$ with at
most $c$ elements and $A_2, \dots, A_k$ is valid from the left bank $L \setminus A_1$ with the
torch on the right. With the torch on the right, it is valid when $A_1$ is a nonempty subset of
$P \setminus L$ with at most $c$ elements and $A_2, \dots, A_k$ is valid from the left bank
$L \cup A_1$ with the torch on the left.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
proof of Theorem 1 (states and moves) and Section 3 (capacity `c`). -/
def bridgeScheduleFrom (c : ℕ) (P : Finset ℕ) : Finset ℕ → Bool → List (Finset ℕ) → Bool
  | L, torchLeft, [] => decide (L = ∅) && !torchLeft
  | L, true, A :: σ =>
      decide (A.Nonempty ∧ A.card ≤ c ∧ A ⊆ L) && bridgeScheduleFrom c P (L \ A) false σ
  | L, false, A :: σ =>
      decide (A.Nonempty ∧ A.card ≤ c ∧ A ⊆ P \ L) && bridgeScheduleFrom c P (L ∪ A) true σ

/-- **Bridge schedules.** Let $c$ and $n$ be natural numbers. A finite sequence $\sigma$ of finite
sets of natural numbers (the crossings) is a schedule for the people $1, \dots, n$ on a bridge of
capacity $c$ with one torch when the following holds. Start with all of $1, \dots, n$ and the
torch on the left bank. The crossings at even positions (counting from $0$) are forward moves:
each is a nonempty set of at most $c$ people then on the left bank, who cross with the torch to
the right bank. The crossings at odd positions are returns: each is a nonempty set of at most $c$
people then on the right bank, who cross with the torch back to the left bank. After the last
crossing the left bank is empty and the torch is on the right bank.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
proof of Theorem 1 and Section 3. -/
def IsBridgeSchedule (c n : ℕ) (σ : List (Finset ℕ)) : Prop :=
  bridgeScheduleFrom c (Finset.Icc 1 n) (Finset.Icc 1 n) true σ = true

/-- **Total time of a schedule.** For a finite sequence $\sigma = (A_1, \dots, A_k)$ of finite sets
of natural numbers (the crossings), the total time of $\sigma$ is $\sum_{i=1}^{k} \max A_i$, where
$\max \emptyset = 0$. Since person $p$ has crossing time $p$, each crossing costs the largest
crossing time among the people in it.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
proof of Theorem 1. -/
def scheduleCost (σ : List (Finset ℕ)) : ℕ :=
  (σ.map fun A => A.sup id).sum

/-- **Optimal crossing time of the bridge and torch problem.** For a bridge of capacity $c$ and
$n$ people $1, \dots, n$, where person $i$ has crossing time $i$, the optimal crossing time is
the least total time of a complete schedule with one torch; the total time of a schedule is the
sum, over its crossings, of the largest crossing time among the people in that crossing. It is
written $T(n)$ for $c = 2$ and $T_3(n)$ for $c = 3$. If no complete schedule exists (for
example when $n = 0$), the value is $0$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 1 and Theorem 12. -/
noncomputable def bridgeTime (c n : ℕ) : ℕ :=
  sInf {t | ∃ σ, IsBridgeSchedule c n σ ∧ scheduleCost σ = t}

/-- **Every schedule bounds the optimal time.** For all natural numbers $c$ and $n$ and every
complete schedule $\sigma$ for the people $1, \dots, n$ on a bridge of capacity $c$ with one
torch, the optimal crossing time of these $n$ people on this bridge is at most the total time
of $\sigma$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 1 (definition of `T(n)`). -/
theorem bridgeTime_le_scheduleCost {c n : ℕ} {σ : List (Finset ℕ)}
    (hσ : IsBridgeSchedule c n σ) : bridgeTime c n ≤ scheduleCost σ :=
  Nat.sInf_le ⟨σ, hσ, rfl⟩

-- On a forward trip the weights can exceed the duration by at most five.
-- On a return trip the weights plus the duration recover at least five.
private def weight (i : ℕ) : ℕ :=
  if i ≤ 2 then 5 - i else i / 2 + 3

private theorem forward_bound {A : Finset ℕ} (hne : A.Nonempty) (hc : A.card ≤ 2)
    (hpos : ∀ i ∈ A, 0 < i) : ∑ i ∈ A, weight i ≤ A.sup id + 5 := by
  have hcard := card_pos.mpr hne
  rcases (show A.card = 1 ∨ A.card = 2 by omega) with h | h
  · obtain ⟨i, rfl⟩ := card_eq_one.mp h
    simp [weight]
    split <;> omega
  · obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp h
    have hi := hpos i (mem_insert_self _ _)
    have hj := hpos j (mem_insert_of_mem (mem_singleton_self _))
    simp [hij, weight, sup_insert, max_def]
    split_ifs <;> omega

private theorem return_bound {A : Finset ℕ} (hne : A.Nonempty) :
    5 ≤ (∑ i ∈ A, weight i) + A.sup id := by
  obtain ⟨i, hi⟩ := hne
  have hw := single_le_sum (f := weight) (fun j _ ↦ Nat.zero_le (weight j)) hi
  have hm : i ≤ A.sup id := le_sup (f := id) hi
  have : 5 ≤ weight i + i := by unfold weight; split <;> omega
  omega

private theorem schedule_lower_bound {P L : Finset ℕ} {side : Bool} {σ : List (Finset ℕ)}
    (hP : 0 ∉ P) (hL : L ⊆ P) (hσ : bridgeScheduleFrom 2 P L side σ = true) :
    ∑ i ∈ L, weight i ≤ scheduleCost σ + (if side then 5 else 0) := by
  induction σ generalizing L side with
  | nil =>
    simp [bridgeScheduleFrom] at hσ
    simp [hσ.1, scheduleCost]
  | cons A σ ih =>
    cases side <;> simp only [bridgeScheduleFrom, Bool.and_eq_true, decide_eq_true_eq] at hσ
    · obtain ⟨⟨hne, _, hA⟩, htail⟩ := hσ
      have hdis : Disjoint L A := disjoint_left.mpr fun _ hi ha ↦ (mem_sdiff.mp (hA ha)).2 hi
      have hh := ih (union_subset hL (hA.trans sdiff_subset)) htail
      rw [sum_union hdis] at hh
      have := return_bound hne
      simp only [scheduleCost, List.map_cons, List.sum_cons, Bool.false_eq_true, ↓reduceIte,
        add_zero] at *
      omega
    · obtain ⟨⟨hne, hc, hA⟩, htail⟩ := hσ
      have hh := ih (sdiff_subset.trans hL) htail
      have hf := forward_bound hne hc fun i hi ↦ Nat.pos_of_ne_zero fun e ↦ hP (e ▸ hL (hA hi))
      rw [← sum_sdiff (f := weight) hA]
      simp only [scheduleCost, List.map_cons, List.sum_cons, Bool.false_eq_true, ↓reduceIte,
        add_zero] at *
      omega

-- People already on the right may remain there for the whole schedule.
private theorem schedule_mono {P Q L : Finset ℕ} {side : Bool} {σ : List (Finset ℕ)}
    (hPQ : P ⊆ Q) (hσ : bridgeScheduleFrom 2 P L side σ = true) :
    bridgeScheduleFrom 2 Q L side σ = true := by
  induction σ generalizing L side with
  | nil => exact hσ
  | cons A σ ih =>
    cases side <;> simp only [bridgeScheduleFrom, Bool.and_eq_true, decide_eq_true_eq] at *
    · exact ⟨⟨hσ.1.1, hσ.1.2.1, hσ.1.2.2.trans (sdiff_subset_sdiff_left L hPQ)⟩, ih hσ.2⟩
    · exact ⟨hσ.1, ih hσ.2⟩

-- Send 1 and 2, bring 2 back, send the two slowest, and bring 1 back.
private def extendSchedule (n : ℕ) (σ : List (Finset ℕ)) : List (Finset ℕ) :=
  {1, 2} :: {2} :: {n + 1, n + 2} :: {1} :: σ

private theorem extend_valid {n : ℕ} (hn : 2 ≤ n) {σ : List (Finset ℕ)}
    (hσ : IsBridgeSchedule 2 n σ) : IsBridgeSchedule 2 (n + 2) (extendSchedule n σ) := by
  have hPQ : Icc 1 n ⊆ Icc 1 (n + 2) := Icc_subset_Icc_right (by omega)
  have htail := schedule_mono hPQ hσ
  have hbank : ((Icc 1 (n + 2) \ {1, 2}) ∪ {2}) \ {n + 1, n + 2} ∪ {1} = Icc 1 n := by
    ext i
    simp only [mem_union, mem_sdiff, mem_Icc, mem_insert, mem_singleton]
    omega
  simp only [IsBridgeSchedule, extendSchedule, bridgeScheduleFrom, Bool.and_eq_true,
    decide_eq_true_eq, hbank, htail, and_true]
  simp [insert_subset_iff, mem_sdiff, mem_Icc]
  omega

private theorem extend_cost (n : ℕ) (σ : List (Finset ℕ)) :
    scheduleCost (extendSchedule n σ) = scheduleCost σ + (n + 2) + 5 := by
  simp [scheduleCost, extendSchedule, sup_insert]
  omega

private def totalWeight (n : ℕ) : ℕ := ∑ i ∈ Icc 1 n, weight i

private theorem totalWeight_step {n : ℕ} (hn : 2 ≤ n) :
    totalWeight (n + 2) = totalWeight n + (n + 2) + 5 := by
  unfold totalWeight
  rw [sum_Icc_succ_top (b := n + 1) (by omega), sum_Icc_succ_top (b := n) (by omega)]
  unfold weight
  split_ifs <;> omega

private theorem exists_sharp_schedule (n : ℕ) (hn : 2 ≤ n) :
    ∃ σ, IsBridgeSchedule 2 n σ ∧ scheduleCost σ + 5 = totalWeight n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨[{1, 2}], by unfold IsBridgeSchedule; decide, by decide⟩
  | one => exact ⟨[{1, 2}, {1}, {1, 3}], by unfold IsBridgeSchedule; decide, by decide⟩
  | more k ih _ =>
    obtain ⟨σ, hσ, hcost⟩ := ih (by omega)
    exact ⟨extendSchedule (k + 2) σ, extend_valid (by omega) hσ, by
      rw [extend_cost, totalWeight_step (n := k + 2) (by omega)]
      omega⟩

private theorem bridgeTime_add_five (n : ℕ) (hn : 2 ≤ n) :
    bridgeTime 2 n + 5 = totalWeight n := by
  obtain ⟨σ, hσ, hcost⟩ := exists_sharp_schedule n hn
  apply le_antisymm
  · exact hcost ▸ Nat.add_le_add_right (bridgeTime_le_scheduleCost hσ) 5
  · obtain ⟨τ, hτ, heq⟩ := Nat.sInf_mem
      (s := {t | ∃ τ, IsBridgeSchedule 2 n τ ∧ scheduleCost τ = t}) ⟨_, σ, hσ, rfl⟩
    change scheduleCost τ = bridgeTime 2 n at heq
    rw [← heq]
    exact schedule_lower_bound (by simp) (Subset.rfl) hτ

/-- **Closed form for capacity two.** Let $T(n)$ be the optimal crossing time of $n$ people with
crossing times $1, \dots, n$ on a bridge of capacity $2$ with one torch. For every $n \ge 2$,
$$T(n) = \frac{n^2}{4} + 3n - 5 + \frac{(-1)^n - 1}{8}.$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 1 (`jis-2026-26.5.6-thm-1`). -/
theorem bridgeTime_two_closed_form (n : ℕ) (hn : 2 ≤ n) :
    (bridgeTime 2 n : ℝ) = (n : ℝ) ^ 2 / 4 + 3 * n - 5 + ((-1 : ℝ) ^ n - 1) / 8 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  induction k using Nat.twoStepInduction with
  | zero =>
    have h := bridgeTime_add_five 2 (by decide)
    rw [show totalWeight 2 = 7 by decide] at h
    norm_num [show bridgeTime 2 2 = 2 by omega]
  | one =>
    have h := bridgeTime_add_five 3 (by decide)
    rw [show totalWeight 3 = 11 by decide] at h
    norm_num [show bridgeTime 2 3 = 6 by omega]
  | more k ih _ =>
    set m := k + 2
    have hm : 2 ≤ m := by omega
    have h₁ := bridgeTime_add_five m hm
    have h₂ := bridgeTime_add_five (m + 2) (by omega)
    rw [totalWeight_step hm] at h₂
    have hstep : bridgeTime 2 (m + 2) = bridgeTime 2 m + (m + 2) + 5 := by omega
    rw [hstep]
    push_cast
    rw [ih hm, pow_add]
    ring

end MetaMathlibExt.BridgeTorchGeneralizations
