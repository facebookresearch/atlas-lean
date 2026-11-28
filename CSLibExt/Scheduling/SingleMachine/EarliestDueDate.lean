/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.SingleMachine.Lateness
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# The earliest-due-date rule minimizes maximum lateness

Jobs of a finite type, all available at time `0`, are processed on one machine without
preemption. Processing them in order of nondecreasing due date minimizes the maximum lateness
$\max_j (C_j - d_j)$, provided that the processing times are nonnegative
(`maxLateness_le_of_pairwise_dueDate_le`). Such an order always exists
(`exists_isSchedule_pairwise_dueDate_le`).

The proof compares the schedules directly instead of exchanging adjacent jobs. Let `τ` list the
jobs by nondecreasing due date, let `σ` be any schedule, and let `j` be a job. Among `j` and the
jobs before it in `τ`, let `k` be the one that `σ` processes last. All of these jobs complete in
`σ` no later than `k`, so, as processing times are nonnegative, `k` completes in `σ` no earlier
than `j` completes in `τ`. Since `k` comes no later than `j` in `τ`, its due date is at most that
of `j`, so the lateness of `k` in `σ` is at least that of `j` in `τ`.

## References

* *Lecture 5: Single Machine Environments (Maximum Lateness)*, Scheduling Theory, CO 454,
  Spring 2009, May 19, 2009, lecture notes (instructor: D. Chakrabarty, University of Waterloo),
  Definition 1.1 and Theorem 1.2.
-/

@[expose] public section

namespace Cslib.Scheduling.SingleMachine

variable {J R : Type*} [DecidableEq J]

-- On a list without duplicates, the completion time of `j` is the sum of the processing times
-- over the set of entries up to and including `j`.
private theorem completionTime_eq_sum_toFinset [AddCommMonoid R] (p : J → R) {σ : List J}
    (hσ : σ.Nodup) (j : J) :
    completionTime p σ j = ∑ i ∈ (σ.take (σ.idxOf j + 1)).toFinset, p i :=
  (List.sum_toFinset p (hσ.sublist (List.take_sublist _ _))).symm

-- In a list sorted by `d`, a job at or before the first occurrence of `j` has due date at most
-- that of `j`.
private theorem dueDate_le_of_mem_take [LinearOrder R] {d : J → R} {τ : List J}
    (hτ : τ.Pairwise fun i j => d i ≤ d j) {j k : J} (hj : j ∈ τ)
    (hk : k ∈ τ.take (τ.idxOf j + 1)) : d k ≤ d j := by
  by_cases hkj : k = j
  · exact hkj ▸ le_rfl
  have hkτ : k ∈ τ := List.mem_of_mem_take hk
  have hlt : τ.idxOf k < τ.idxOf j := by
    have hle := (List.mem_take_iff_idxOf_lt hkτ).1 hk
    have hne : τ.idxOf k ≠ τ.idxOf j := fun h => hkj ((List.idxOf_inj hkτ).1 h)
    omega
  have hk' : k ∈ τ.take (τ.idxOf j) := (List.mem_take_iff_idxOf_lt hkτ).2 hlt
  have hj' : j ∈ τ.drop (τ.idxOf j) := by
    rw [List.drop_eq_getElem_cons (List.idxOf_lt_length_of_mem hj), List.getElem_idxOf]
    exact List.mem_cons_self
  exact hτ.rel_of_mem_take_of_mem_drop hk' hj'

/-- **The earliest-due-date rule minimizes maximum lateness.** Let finitely many jobs $j$, all
available at time $0$, have processing times $p_j \ge 0$ and due dates $d_j$ in a linearly
ordered additive commutative group such as $\mathbb{R}$, and let them be processed one at a time
on a single machine without preemption or idle time, so that a schedule is an order of the jobs.
If the schedule `τ` lists the jobs by nondecreasing due date, then its maximum lateness
$\max_j (C_j - d_j)$, where $C_j$ is the completion time of job $j$, is at most that of every
schedule `σ`. The lateness may be negative, and the maximum over no jobs is `⊥`, standing for
$-\infty$. -/
theorem maxLateness_le_of_pairwise_dueDate_le [Fintype J] [AddCommGroup R] [LinearOrder R]
    [IsOrderedAddMonoid R] {p d : J → R} (hp : ∀ j, 0 ≤ p j) {σ τ : List J}
    (hσ : IsSchedule σ) (hτ : IsSchedule τ) (hedd : τ.Pairwise fun i j => d i ≤ d j) :
    maxLateness p d τ ≤ maxLateness p d σ := by
  refine maxLateness_le_iff.2 fun j => ?_
  -- `S`: `j` and the jobs before it in `τ`; `k`: the one of them that `σ` processes last.
  set S := (τ.take (τ.idxOf j + 1)).toFinset with hS
  have hjS : j ∈ S := by
    rw [hS, List.mem_toFinset, List.mem_take_iff_idxOf_lt (hτ.2 j)]
    exact Nat.lt_succ_self _
  obtain ⟨k, hkS, hkmax⟩ := S.exists_max_image σ.idxOf ⟨j, hjS⟩
  -- Every job of `S` completes in `σ` no later than `k`.
  have hST : S ⊆ (σ.take (σ.idxOf k + 1)).toFinset := fun x hx => by
    rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt (hσ.2 x)]
    exact Nat.lt_succ_of_le (hkmax x hx)
  have hC : completionTime p τ j ≤ completionTime p σ k := by
    rw [completionTime_eq_sum_toFinset p hτ.1, completionTime_eq_sum_toFinset p hσ.1]
    exact Finset.sum_le_sum_of_subset_of_nonneg hST fun i _ _ => hp i
  have hd : d k ≤ d j := dueDate_le_of_mem_take hedd (hτ.2 j) (List.mem_toFinset.1 hkS)
  exact (WithBot.coe_le_coe.2 (sub_le_sub hC hd)).trans (le_maxLateness p d σ k)

-- Some schedule lists the jobs by nondecreasing due date: for instance a merge sort of any
-- schedule.
omit [DecidableEq J] in
theorem exists_isSchedule_pairwise_dueDate_le [Finite J] [LinearOrder R] (d : J → R) :
    ∃ τ, IsSchedule τ ∧ τ.Pairwise fun i j => d i ≤ d j := by
  have := Fintype.ofFinite J
  have hperm := (Finset.univ : Finset J).toList.mergeSort_perm fun i j => decide (d i ≤ d j)
  refine ⟨_, isSchedule_univ_toList.perm hperm.symm, ?_⟩
  refine (List.pairwise_mergeSort (fun a b c hab hbc => ?_) (fun a b => ?_) _).imp ?_
  · simp only [decide_eq_true_eq] at hab hbc ⊢
    exact hab.trans hbc
  · simpa using le_total (d a) (d b)
  · intro a b h
    simpa using h

end Cslib.Scheduling.SingleMachine
