/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel

/-!
# Single-machine schedules and completion times

Jobs of a type `J` are processed on one machine, without preemption, and all of them are
available at time `0`. A schedule is an order of the jobs: a list in which every job occurs
exactly once (`IsSchedule`). The machine processes the jobs one after another in that order,
from time `0` and without idle time, so the completion time of a job is the sum of the
processing times of the jobs up to and including it (`completionTime`). The total weighted
completion time `∑ j, w j * C j` of the objective `1 ‖ ∑ wⱼ Cⱼ` is
`totalWeightedCompletionTime`.

Exchange arguments compare a schedule with the one that swaps two adjacent jobs `a` and `b`.
`completionTime_swap_of_ne`, `completionTime_swap_left` and `completionTime_swap_right` give
the completion times after the swap, and `totalWeightedCompletionTime_swap` the change of the
total weighted completion time, `w a * p b - w b * p a`, written without subtraction.

Reference: N. Shakhlevich, *Scheduling: Models and Algorithms*, School of Computing, University
of Leeds, 2004/2005, Handout 2, "Single machine problems".
-/

@[expose] public section

namespace Cslib.Scheduling.SingleMachine

variable {J R : Type*}

/-- **Single-machine schedule.** A schedule of the jobs of a type $J$ on one machine is a list
$\sigma$ of jobs in which every job of $J$ occurs exactly once; it gives the order in which the
machine processes the jobs. -/
def IsSchedule (σ : List J) : Prop :=
  σ.Nodup ∧ ∀ j, j ∈ σ

theorem IsSchedule.perm {σ τ : List J} (hσ : IsSchedule σ) (h : σ.Perm τ) : IsSchedule τ :=
  ⟨h.nodup_iff.1 hσ.1, fun j => h.mem_iff.1 (hσ.2 j)⟩

theorem IsSchedule.isSchedule_iff_perm {σ τ : List J} (hσ : IsSchedule σ) :
    IsSchedule τ ↔ σ.Perm τ :=
  ⟨fun hτ => (List.perm_ext_iff_of_nodup hσ.1 hτ.1).2 fun j => by simp [hσ.2 j, hτ.2 j],
    hσ.perm⟩

theorem isSchedule_univ_toList [Fintype J] : IsSchedule (Finset.univ : Finset J).toList :=
  ⟨Finset.nodup_toList _, fun j => Finset.mem_toList.2 (Finset.mem_univ j)⟩

section CompletionTime

variable [DecidableEq J]

/-- **Completion time on a single machine.** Let $\sigma$ be a list of jobs and let $p_j$ be the
processing time of job $j$, in an additive monoid such as $\mathbb{N}$ or $\mathbb{R}$. When the
machine processes the jobs of $\sigma$ one after another from time $0$, without idle time or
preemption, job $j$ completes at time $C_j$, the sum of $p_i$ over the entries $i$ of $\sigma$ up
to and including the first occurrence of $j$. If $j$ does not occur in $\sigma$, $C_j$ is the sum
of $p_i$ over all of $\sigma$. -/
def completionTime [AddMonoid R] (p : J → R) (σ : List J) (j : J) : R :=
  ((σ.take (σ.idxOf j + 1)).map p).sum

section AddMonoid

variable [AddMonoid R] (p : J → R)

@[simp]
theorem completionTime_nil (j : J) : completionTime p [] j = 0 := by
  simp [completionTime]

@[simp]
theorem completionTime_cons_self (a : J) (l : List J) : completionTime p (a :: l) a = p a := by
  simp [completionTime]

theorem completionTime_cons_of_ne {a j : J} (l : List J) (h : j ≠ a) :
    completionTime p (a :: l) j = p a + completionTime p l j := by
  simp [completionTime, List.idxOf_cons_ne l (Ne.symm h)]

theorem completionTime_append_of_mem {l₁ : List J} (l₂ : List J) {j : J} (h : j ∈ l₁) :
    completionTime p (l₁ ++ l₂) j = completionTime p l₁ j := by
  induction l₁ with
  | nil => simp at h
  | cons a l ih =>
    by_cases hja : j = a
    · subst hja
      simp
    · have hj : j ∈ l := (List.mem_cons.1 h).resolve_left hja
      rw [List.cons_append, completionTime_cons_of_ne p _ hja, completionTime_cons_of_ne p _ hja,
        ih hj]

theorem completionTime_append_of_notMem {l₁ : List J} (l₂ : List J) {j : J} (h : j ∉ l₁) :
    completionTime p (l₁ ++ l₂) j = (l₁.map p).sum + completionTime p l₂ j := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    rw [List.mem_cons, not_or] at h
    rw [List.cons_append, completionTime_cons_of_ne p _ h.1, ih h.2, List.map_cons, List.sum_cons,
      add_assoc]

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid R] (p : J → R)

/- Swapping two adjacent jobs `a` and `b` leaves the completion time of every other job
unchanged. -/
theorem completionTime_swap_of_ne (l₁ l₂ : List J) {a b j : J} (hja : j ≠ a) (hjb : j ≠ b) :
    completionTime p (l₁ ++ b :: a :: l₂) j = completionTime p (l₁ ++ a :: b :: l₂) j := by
  by_cases hj : j ∈ l₁
  · rw [completionTime_append_of_mem p _ hj, completionTime_append_of_mem p _ hj]
  · rw [completionTime_append_of_notMem p _ hj, completionTime_append_of_notMem p _ hj,
      completionTime_cons_of_ne p _ hjb, completionTime_cons_of_ne p _ hja,
      completionTime_cons_of_ne p _ hja, completionTime_cons_of_ne p _ hjb, add_left_comm (p b)]

/- Moving job `a` behind the adjacent job `b` delays it by the processing time of `b`. -/
theorem completionTime_swap_left (l₁ l₂ : List J) {a b : J} (ha : a ∉ l₁) (hab : a ≠ b) :
    completionTime p (l₁ ++ b :: a :: l₂) a = completionTime p (l₁ ++ a :: b :: l₂) a + p b := by
  rw [completionTime_append_of_notMem p _ ha, completionTime_append_of_notMem p _ ha,
    completionTime_cons_of_ne p _ hab, completionTime_cons_self, completionTime_cons_self,
    add_assoc, add_comm (p b)]

/- Moving job `b` ahead of the adjacent job `a` advances it by the processing time of `a`. -/
theorem completionTime_swap_right (l₁ l₂ : List J) {a b : J} (hb : b ∉ l₁) (hab : a ≠ b) :
    completionTime p (l₁ ++ b :: a :: l₂) b + p a = completionTime p (l₁ ++ a :: b :: l₂) b := by
  rw [completionTime_append_of_notMem p _ hb, completionTime_append_of_notMem p _ hb,
    completionTime_cons_self, completionTime_cons_of_ne p _ (Ne.symm hab), completionTime_cons_self,
    add_assoc, add_comm (p b)]

end AddCommMonoid

end CompletionTime

section TotalWeightedCompletionTime

variable [Fintype J] [DecidableEq J] [Semiring R]

/-- **Total weighted completion time.** Let finitely many jobs $j$ have processing times $p_j$
and weights $w_j$ in a semiring such as $\mathbb{N}$ or $\mathbb{R}$. The total weighted
completion time of a list $\sigma$ of jobs is $\sum_j w_j C_j$, summed over all jobs $j$, where
$C_j$ is the completion time of job $j$ when the machine processes the jobs of $\sigma$ one after
another from time $0$. -/
def totalWeightedCompletionTime (p w : J → R) (σ : List J) : R :=
  ∑ j, w j * completionTime p σ j

theorem totalWeightedCompletionTime_eq_sum_map (p w : J → R) {σ : List J}
    (hσ : IsSchedule σ) :
    totalWeightedCompletionTime p w σ = (σ.map fun j => w j * completionTime p σ j).sum := by
  rw [← List.sum_toFinset _ hσ.1, totalWeightedCompletionTime]
  exact (Finset.sum_congr (Finset.ext fun j => by simp [hσ.2 j]) fun _ _ => rfl)

/- The exchange identity: swapping two adjacent jobs `a` and `b` changes the total weighted
completion time by `w a * p b - w b * p a`. -/
theorem totalWeightedCompletionTime_swap (p w : J → R) {l₁ l₂ : List J} {a b : J}
    (h : (l₁ ++ a :: b :: l₂).Nodup) :
    totalWeightedCompletionTime p w (l₁ ++ b :: a :: l₂) + w b * p a =
      totalWeightedCompletionTime p w (l₁ ++ a :: b :: l₂) + w a * p b := by
  have h₁ := List.nodup_middle.1 h
  have h₂ : ((l₁ ++ [a]) ++ b :: l₂).Nodup := by simpa using h
  replace h₂ := List.nodup_middle.1 h₂
  have ha : a ∉ l₁ := fun ha => (List.nodup_cons.1 h₁).1 (List.mem_append_left _ ha)
  have hab : a ≠ b := fun hab => (List.nodup_cons.1 h₁).1 (by simp [hab])
  have hb : b ∉ l₁ := fun hb => (List.nodup_cons.1 h₂).1 (by simp [hb])
  have hmem : b ∈ (Finset.univ : Finset J).erase a :=
    Finset.mem_erase.2 ⟨Ne.symm hab, Finset.mem_univ b⟩
  simp only [totalWeightedCompletionTime]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ hmem,
    Finset.sum_congr rfl fun j hj => by
      rw [completionTime_swap_of_ne p l₁ l₂ (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))
        (Finset.ne_of_mem_erase hj)],
    completionTime_swap_left p l₁ l₂ ha hab, ← completionTime_swap_right p l₁ l₂ hb hab,
    mul_add, mul_add]
  abel

end TotalWeightedCompletionTime

end Cslib.Scheduling.SingleMachine
