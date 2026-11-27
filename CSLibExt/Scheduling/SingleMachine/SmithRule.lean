/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.SingleMachine.CompletionTime
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Basic

/-!
# Smith's rule for total weighted completion time

Jobs with processing times `p j` and weights `w j` run on one machine, all from time `0` and
without preemption, in the order of a schedule (`IsSchedule`, a list of all jobs). Smith's rule,
or the weighted shortest processing time (WSPT) rule, for `1 ‖ ∑ wⱼ Cⱼ` orders the jobs by
nondecreasing `p j / w j`. Written with cross-products, which also covers zero weights, it puts
the jobs with `w j > 0` first, so that `p i * w j ≤ p j * w i` whenever `i` precedes `j`, and the
jobs with `w j = 0` last.

* `totalWeightedCompletionTime_le_of_pairwise`: a schedule in which `p i * w j ≤ p j * w i`
  whenever `i` precedes `j` has total weighted completion time at most that of any schedule. It
  needs no sign condition, and holds over any ordered cancellative commutative semiring.
* `smithRule_minimizes_totalWeightedCompletionTime`: for real `p j ≥ 0` and `w j ≥ 0`, an order
  following Smith's rule exists, and every such order minimizes the total weighted completion
  time.

The proof is the adjacent pairwise interchange argument. Take a schedule `σ` with the
cross-product property and any schedule `τ`. Move the first job of `σ` to the front of `τ` by
swapping it with the job just before it; each swap changes the total weighted completion time by
`w b * p a - w a * p b ≤ 0` (`totalWeightedCompletionTime_swap`), where `a` is the moved job and
`b` the job it passes. Then repeat behind it with the remaining jobs.

Reference: N. Shakhlevich, *Scheduling: Models and Algorithms*, School of Computing, University
of Leeds, 2004/2005, Handout 2, "Single machine problems", Theorem 1 (stated there with the ratios
`p j / w j`).
-/

@[expose] public section

namespace Cslib.Scheduling.SingleMachine

variable {J R : Type*} [Fintype J] [DecidableEq J]

section Exchange

variable [CommSemiring R] [PartialOrder R] [IsOrderedCancelAddMonoid R] {p w : J → R}

/- Moving job `a` ahead of a block `t` of jobs that may precede it does not increase the total
weighted completion time. -/
private theorem totalWeightedCompletionTime_cons_append_le {a : J} (t : List J)
    (ht : ∀ c ∈ t, p a * w c ≤ p c * w a) (u v : List J) (h : (u ++ t ++ a :: v).Nodup) :
    totalWeightedCompletionTime p w (u ++ a :: (t ++ v)) ≤
      totalWeightedCompletionTime p w (u ++ t ++ a :: v) := by
  induction t generalizing u with
  | nil => simp
  | cons c t ih =>
    have hnodup : (u ++ c :: a :: (t ++ v)).Nodup :=
      ((List.perm_middle.cons c).append_left u).nodup_iff.1 (by simpa using h)
    have hswap := totalWeightedCompletionTime_swap p w hnodup
    have hc : w c * p a ≤ w a * p c := by
      simpa [mul_comm] using ht c (by simp)
    have h₁ : totalWeightedCompletionTime p w (u ++ a :: c :: (t ++ v)) ≤
        totalWeightedCompletionTime p w (u ++ c :: a :: (t ++ v)) :=
      le_of_add_le_add_right (hswap.trans_le (add_le_add le_rfl hc))
    have h₂ := ih (fun c' hc' => ht c' (by simp [hc'])) (u ++ [c]) (by simpa using h)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h₂ ⊢
    exact h₁.trans h₂

/- The exchange argument, after a common prefix `u`. -/
private theorem totalWeightedCompletionTime_append_le (σ : List J)
    (hσ : σ.Pairwise fun i j => p i * w j ≤ p j * w i) (u τ : List J)
    (hτ : (u ++ τ).Nodup) (h : τ.Perm σ) :
    totalWeightedCompletionTime p w (u ++ σ) ≤ totalWeightedCompletionTime p w (u ++ τ) := by
  induction σ generalizing u τ with
  | nil => simp [List.perm_nil.1 h]
  | cons a σ ih =>
    rw [List.pairwise_cons] at hσ
    obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem (h.mem_iff.2 List.mem_cons_self)
    have hrest : (t₁ ++ t₂).Perm σ :=
      (List.perm_cons a).1 (List.perm_middle.symm.trans h)
    have hfront : (u ++ [a] ++ (t₁ ++ t₂)).Nodup := by
      simpa using (List.perm_middle.append_left u).nodup_iff.1 hτ
    have h₁ := ih hσ.2 (u ++ [a]) (t₁ ++ t₂) hfront hrest
    have h₂ := totalWeightedCompletionTime_cons_append_le t₁
      (fun c hc => hσ.1 c (hrest.mem_iff.1 (List.mem_append_left _ hc))) u t₂
      (by simpa using hτ)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h₁ h₂ ⊢
    exact h₁.trans h₂

/- Any schedule in which `p i * w j ≤ p j * w i` whenever `i` precedes `j` minimizes the total
weighted completion time; no sign condition is needed. -/
theorem totalWeightedCompletionTime_le_of_pairwise {σ τ : List J} (hσ : IsSchedule σ)
    (hτ : IsSchedule τ) (h : σ.Pairwise fun i j => p i * w j ≤ p j * w i) :
    totalWeightedCompletionTime p w σ ≤ totalWeightedCompletionTime p w τ := by
  simpa using totalWeightedCompletionTime_append_le σ h [] τ hτ.1
    (hσ.isSchedule_iff_perm.1 hτ).symm

end Exchange

/-- **Smith's rule minimizes total weighted completion time.** Let finitely many jobs $j$ have
real processing times $p_j \ge 0$ and real weights $w_j \ge 0$. They are processed on one machine
from time $0$, one after another without idle time or preemption, in the order of a schedule: a
list $\sigma$ in which every job occurs exactly once; $C_j$ is the completion time of job $j$.
Smith's rule asks that, whenever job $i$ precedes job $j$ in $\sigma$, $w_j > 0$ implies $w_i > 0$
(the jobs with $w_j > 0$ come first and those with $w_j = 0$ last) and $p_i w_j \le p_j w_i$.
Some schedule follows Smith's rule, and every schedule $\sigma$ that does has
$\sum_j w_j C_j(\sigma) \le \sum_j w_j C_j(\tau)$ for every schedule $\tau$. -/
theorem smithRule_minimizes_totalWeightedCompletionTime {p w : J → ℝ} (hp : ∀ j, 0 ≤ p j)
    (hw : ∀ j, 0 ≤ w j) :
    (∃ σ, IsSchedule σ ∧ σ.Pairwise fun i j => (0 < w j → 0 < w i) ∧ p i * w j ≤ p j * w i) ∧
      ∀ σ τ, IsSchedule σ → IsSchedule τ →
        (σ.Pairwise fun i j => (0 < w j → 0 < w i) ∧ p i * w j ≤ p j * w i) →
        totalWeightedCompletionTime p w σ ≤ totalWeightedCompletionTime p w τ := by
  classical
  refine ⟨?_, fun σ τ hσ hτ h => totalWeightedCompletionTime_le_of_pairwise hσ hτ
    (h.imp fun h => h.2)⟩
  -- Sort the jobs by the total preorder "`w j = 0`, or `w i > 0` and `p i * w j ≤ p j * w i`".
  let le : J → J → Bool := fun i j => decide (w j = 0 ∨ (0 < w i ∧ p i * w j ≤ p j * w i))
  have hpos : ∀ j, w j ≠ 0 → 0 < w j := fun j hj => lt_of_le_of_ne (hw j) (Ne.symm hj)
  have htrans : ∀ a b c, le a b = true → le b c = true → le a c = true := by
    intro a b c hab hbc
    simp only [le, decide_eq_true_eq] at hab hbc ⊢
    by_cases hc : w c = 0
    · exact Or.inl hc
    obtain ⟨hb, hbc⟩ := hbc.resolve_left hc
    obtain ⟨ha, hab⟩ := hab.resolve_left hb.ne'
    refine Or.inr ⟨ha, le_of_mul_le_mul_right ?_ hb⟩
    calc p a * w c * w b = p a * w b * w c := mul_right_comm _ _ _
      _ ≤ p b * w a * w c := mul_le_mul_of_nonneg_right hab (hw c)
      _ = p b * w c * w a := mul_right_comm _ _ _
      _ ≤ p c * w b * w a := mul_le_mul_of_nonneg_right hbc (hw a)
      _ = p c * w a * w b := mul_right_comm _ _ _
  have htotal : ∀ a b, (le a b || le b a) = true := by
    intro a b
    simp only [le, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hb : w b = 0
    · exact Or.inl (Or.inl hb)
    by_cases ha : w a = 0
    · exact Or.inr (Or.inl ha)
    rcases le_total (p a * w b) (p b * w a) with h | h
    · exact Or.inl (Or.inr ⟨hpos a ha, h⟩)
    · exact Or.inr (Or.inr ⟨hpos b hb, h⟩)
  refine ⟨(Finset.univ : Finset J).toList.mergeSort le,
    isSchedule_univ_toList.perm (List.mergeSort_perm _ _).symm, ?_⟩
  refine (List.pairwise_mergeSort htrans htotal _).imp fun {i j} hij => ?_
  simp only [le, decide_eq_true_eq] at hij
  rcases hij with hj | ⟨hi, hij⟩
  · refine ⟨fun h => absurd hj h.ne', ?_⟩
    rw [hj, mul_zero]
    exact mul_nonneg (hp j) (hw i)
  · exact ⟨fun _ => hi, hij⟩

end Cslib.Scheduling.SingleMachine
