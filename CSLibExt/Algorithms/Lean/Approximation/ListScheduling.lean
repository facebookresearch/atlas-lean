/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Cslib.Algorithms.Lean.MergeSort.MergeSort
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Order.Basic
import Mathlib.Tactic.Ring

/-!
# List scheduling and LPT on identical machines

Jobs with processing times `ps : List ℕ` run on `m` identical machines; the makespan of a
schedule is its largest machine load. Graham's *list scheduling* takes the jobs in the given
order and puts each on a currently least-loaded machine. *LPT* (longest processing time first)
first sorts the jobs into nonincreasing order and then list-schedules them.

* Graham, "Bounds for certain multiprocessing anomalies", Bell System Technical Journal 45
  (1966): list scheduling in any order has makespan at most `(2 - 1/m)` times optimal
  (`listSchedule_approx`: `m * C ≤ (2 * m - 1) * M`).
* Graham, "Bounds on multiprocessing timing anomalies", SIAM J. Appl. Math. 17 (1969): LPT has
  makespan at most `(4/3 - 1/(3m))` times optimal (`lpt_approx`: `3 * m * C ≤ (4 * m - 1) * M`).
* Textbook treatment: Williamson and Shmoys, *The Design of Approximation Algorithms* (2011),
  Section 2.3.

In both bounds `M` is the makespan of an arbitrary schedule of the same jobs, so in particular of
an optimal one. A schedule is a function `σ : Fin m → List ℕ` giving each machine its jobs; it
schedules `ps` when the machines' lists together form `ps` as a multiset (`IsScheduleOf`).

The LPT proof avoids the usual minimal-counterexample argument. When job `p` is placed, either
`3 * p ≤ M`, and the averaging argument gives the bound, or `3 * p > M`. In the second case, if
the new load exceeded `M`, every machine would already hold two jobs or one job longer than
`M - p`, while any schedule with makespan `M` holds at most two jobs of length `≥ p` per machine
and at most one if one of them is longer than `M - p`; counting both sides over the machines
gives a contradiction (`lpt_step_le`).

## Cost model

Placing a job costs `m`: one unit per machine load inspected to find a least-loaded machine (the
loads are kept in an array). Updating the chosen load and appending the job are free. So list
scheduling of `n` jobs costs exactly `n * m`. LPT adds CSLib's `mergeSort` comparisons, at most
`n * ⌈log₂ n⌉`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Scheduling

open Cslib.Algorithms.Lean TimeM

variable {m : ℕ}

/-- **Schedule of a list of jobs.** Let $m$ be a natural number. An assignment $\sigma$ of a list
$\sigma(i)$ of natural numbers (processing times) to each machine $i \in \{0, \dots, m - 1\}$ is a
schedule of a list $J$ of natural numbers when the sum over all machines $i$ of the multisets of
entries of $\sigma(i)$ equals the multiset of entries of $J$, that is, every number occurs in
the lists $\sigma(i)$ together exactly as often as it occurs in $J$. -/
def IsScheduleOf (σ : Fin m → List ℕ) (ps : List ℕ) : Prop :=
  ∑ i, (σ i : Multiset ℕ) = (ps : Multiset ℕ)

/-- **Makespan.** For a schedule $\sigma$ that gives each of $m$ machines a list of processing
times, the load of a machine is the sum of its list, and the makespan of $\sigma$ is the largest
machine load ($0$ when $m = 0$). -/
def makespan (σ : Fin m → List ℕ) : ℕ :=
  Finset.univ.sup fun i => (σ i).sum

/-- **Least-loaded machine.** Let $m \ge 1$ and let $L$ assign a load $L(i) \in \mathbb{N}$ to
each machine $i \in \{0, \dots, m - 1\}$. The least-loaded machine for $L$ is the smallest index
$i$ at which $L(i)$ is minimal. -/
def leastLoaded [NeZero m] (loads : Fin m → ℕ) : Fin m :=
  ((List.finRange m).argmin loads).getD 0

theorem leastLoaded_le [NeZero m] (loads : Fin m → ℕ) (i : Fin m) :
    loads (leastLoaded loads) ≤ loads i := by
  unfold leastLoaded
  cases h : (List.finRange m).argmin loads with
  | none =>
      rw [List.argmin_eq_none] at h
      exact absurd h (List.ne_nil_of_mem (List.mem_finRange (0 : Fin m)))
  | some j =>
      simp only [Option.getD_some]
      exact le_of_not_gt (List.not_lt_of_mem_argmin (List.mem_finRange i) h)

/-- **List scheduling from an intermediate state.** Let $m \ge 1$. Given loads $L(i)$ and job
lists $\sigma(i)$ for the machines $i \in \{0, \dots, m - 1\}$ and a list of remaining jobs, list
scheduling returns $\sigma$ at cost $0$ when no jobs remain. Otherwise it charges cost $m$, takes
the first remaining job $p$, appends $p$ to $\sigma(k)$ and adds $p$ to $L(k)$ for the
least-loaded machine $k$ for $L$, and continues in the same way with the other remaining jobs.
The loads $L$ are not required to be the sums of the lists $\sigma(i)$. -/
def listScheduleScan [NeZero m] (loads : Fin m → ℕ) (σ : Fin m → List ℕ) :
    List ℕ → TimeM ℕ (Fin m → List ℕ)
  | [] => pure σ
  | p :: ps => do
      ✓[m]
      let i := leastLoaded loads
      listScheduleScan (Function.update loads i (loads i + p))
        (Function.update σ i (σ i ++ [p])) ps

/-- **Graham's list scheduling.** Given $m \ge 1$ identical machines and a list of job
processing times (natural numbers), start with every machine empty and take the jobs in the
given order, appending each job to the list of a currently least-loaded machine (the first one in
index order), where the load of a machine is the sum of its jobs. The result assigns to each
machine its list of jobs. The cost counted is $m$ per job, one unit for each machine load
inspected. -/
def listSchedule (m : ℕ) [NeZero m] (ps : List ℕ) : TimeM ℕ (Fin m → List ℕ) :=
  listScheduleScan (fun _ => 0) (fun _ => []) ps

/-- **Longest processing time first (LPT).** Given $m \ge 1$ identical machines and a list of job
processing times (natural numbers), LPT sorts the jobs into nonincreasing order by merge sort and
then applies Graham's list scheduling on $m$ machines to the sorted list. The cost counted is the
number of comparisons made by merge sort plus the cost of list scheduling, $m$ per job. -/
def lpt (m : ℕ) [NeZero m] (ps : List ℕ) : TimeM ℕ (Fin m → List ℕ) := do
  let sorted ← mergeSort (ps.map OrderDual.toDual)
  listSchedule m (sorted.map OrderDual.ofDual)

/-! ## Schedules -/

/-- **The empty schedule.** For every number $m$ of machines, the assignment of the empty list
to each of the $m$ machines is a schedule of the empty list of jobs. -/
theorem isScheduleOf_nil : IsScheduleOf (fun _ : Fin m => ([] : List ℕ)) [] := by
  simp [IsScheduleOf]

theorem IsScheduleOf.perm {σ : Fin m → List ℕ} {ps qs : List ℕ} (h : IsScheduleOf σ ps)
    (hpq : ps.Perm qs) : IsScheduleOf σ qs := by
  unfold IsScheduleOf at *
  rw [h]
  exact Multiset.coe_eq_coe.2 hpq

theorem IsScheduleOf.sum_length {σ : Fin m → List ℕ} {ps : List ℕ} (h : IsScheduleOf σ ps) :
    ∑ i, (σ i).length = ps.length := by
  have := congrArg Multiset.card h
  simpa [Multiset.card_sum] using this

theorem IsScheduleOf.sum_sum {σ : Fin m → List ℕ} {ps : List ℕ} (h : IsScheduleOf σ ps) :
    ∑ i, (σ i).sum = ps.sum := by
  have := congrArg Multiset.sum h
  simpa [Multiset.sum_sum] using this

theorem IsScheduleOf.sum_countP {σ : Fin m → List ℕ} {ps : List ℕ} (h : IsScheduleOf σ ps)
    (q : ℕ → Prop) [DecidablePred q] :
    ∑ i, (σ i).countP (fun x => decide (q x)) = ps.countP (fun x => decide (q x)) := by
  have := congrArg (Multiset.countPAddMonoidHom q) h
  rw [map_sum] at this
  simpa [Multiset.countPAddMonoidHom, Multiset.coe_countP] using this

theorem IsScheduleOf.exists_mem {σ : Fin m → List ℕ} {ps : List ℕ} (h : IsScheduleOf σ ps)
    {x : ℕ} (hx : x ∈ ps) : ∃ i, x ∈ σ i := by
  have : x ∈ (∑ i, (σ i : Multiset ℕ)) := by rw [h]; exact Multiset.mem_coe.2 hx
  simpa [Multiset.mem_sum] using this

theorem IsScheduleOf.concat {σ : Fin m → List ℕ} {ps : List ℕ} (h : IsScheduleOf σ ps)
    (i : Fin m) (p : ℕ) :
    IsScheduleOf (Function.update σ i (σ i ++ [p])) (ps ++ [p]) := by
  unfold IsScheduleOf at *
  have hsplit : ∀ τ : Fin m → List ℕ,
      ∑ j, (τ j : Multiset ℕ) =
        (τ i : Multiset ℕ) + ∑ j ∈ Finset.univ.erase i, (τ j : Multiset ℕ) :=
    fun τ => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [hsplit, Function.update_self, Finset.sum_congr rfl (fun j hj =>
    by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]), ← Multiset.coe_add,
    ← Multiset.coe_add, add_right_comm, ← hsplit σ, h]

@[simp]
theorem makespan_nil : makespan (fun _ : Fin m => ([] : List ℕ)) = 0 :=
  Nat.le_zero.1 (Finset.sup_le fun _ _ => by simp)

theorem le_makespan {σ : Fin m → List ℕ} (i : Fin m) : (σ i).sum ≤ makespan σ :=
  Finset.le_sup (f := fun i => (σ i).sum) (Finset.mem_univ i)

/-- **Every job is at most the makespan.** Let $\sigma$ be a schedule on $m$ machines of a list
$J$ of processing times. Then every entry $x$ of $J$ is at most the makespan of $\sigma$. -/
theorem IsScheduleOf.le_makespan {σ : Fin m → List ℕ} {ps : List ℕ} (h : IsScheduleOf σ ps)
    {x : ℕ} (hx : x ∈ ps) : x ≤ makespan σ := by
  obtain ⟨i, hi⟩ := h.exists_mem hx
  exact (List.le_sum_of_mem hi).trans (Scheduling.le_makespan i)

/-- **Total work is at most $m$ times the makespan.** If $\sigma$ is a schedule of a list $P$ of
jobs on $m$ machines, then the total processing time of $P$ is at most $m$ times the makespan of
$\sigma$. -/
theorem IsScheduleOf.sum_le {σ : Fin m → List ℕ} {ps : List ℕ} (h : IsScheduleOf σ ps) :
    ps.sum ≤ m * makespan σ := by
  rw [← h.sum_sum]
  simpa using Finset.sum_le_card_nsmul Finset.univ (fun i => (σ i).sum) (makespan σ)
    (fun i _ => Scheduling.le_makespan i)

/-! ## The scan invariant -/

/-- **List-scheduling state invariant.** A list $P$ of jobs, machine loads $\ell_i \in \mathbb{N}$
for $i < m$, and a schedule $\sigma$ on $m$ machines satisfy the invariant when $\sigma$ is a
schedule of $P$ and, for every machine $i$, $\ell_i$ is the load of machine $i$ in $\sigma$, the
sum of the processing times assigned to it. -/
def ScanInv (P : List ℕ) (loads : Fin m → ℕ) (σ : Fin m → List ℕ) : Prop :=
  (∀ i, loads i = (σ i).sum) ∧ IsScheduleOf σ P

theorem scanInv_init : ScanInv [] (fun _ : Fin m => 0) (fun _ => []) :=
  ⟨fun _ => rfl, isScheduleOf_nil⟩

theorem ScanInv.step [NeZero m] {P : List ℕ} {loads : Fin m → ℕ} {σ : Fin m → List ℕ}
    (h : ScanInv P loads σ) (p : ℕ) :
    ScanInv (P ++ [p]) (Function.update loads (leastLoaded loads) (loads (leastLoaded loads) + p))
      (Function.update σ (leastLoaded loads) (σ (leastLoaded loads) ++ [p])) := by
  refine ⟨fun j => ?_, h.2.concat _ p⟩
  by_cases hj : j = leastLoaded loads
  · subst hj
    simp [h.1]
  · simp [Function.update_of_ne hj, h.1]

theorem makespan_update_le {σ : Fin m → List ℕ} (i : Fin m) (p : ℕ) :
    makespan (Function.update σ i (σ i ++ [p])) ≤ max (makespan σ) ((σ i).sum + p) := by
  apply Finset.sup_le
  intro j _
  by_cases hj : j = i
  · subst hj
    simp
  · simp only [Function.update_of_ne hj]
    exact (Scheduling.le_makespan j).trans (le_max_left _ _)

theorem listScheduleScan_isScheduleOf [NeZero m] {P : List ℕ} {loads : Fin m → ℕ}
    {σ : Fin m → List ℕ} (h : ScanInv P loads σ) (rest : List ℕ) :
    IsScheduleOf (listScheduleScan loads σ rest).ret (P ++ rest) := by
  induction rest generalizing P loads σ with
  | nil => simpa [listScheduleScan] using h.2
  | cons p rest ih =>
      simpa [listScheduleScan] using ih (h.step p)

/-- **Invariant bound for list scheduling.** Let $m \ge 1$ and $a, b, M \in \mathbb{N}$. Let
$\sigma$ assign job lists to the $m$ machines so that $\sigma$ is a schedule of a list $P$ of
jobs already placed, let $L(i)$ be the sum of $\sigma(i)$ for each machine $i$, and let $R$ be a
list of remaining jobs. Assume that $a$ times the makespan of $\sigma$ is at most $bM$. Assume
also that whenever $P$ followed by $R$ equals $P'$ followed by a job $p$ followed by a list
$R'$, and $\sigma'$ is any schedule of $P'$ with loads $L'(i)$ equal to the sum of
$\sigma'(i)$, we have $a(L'(k) + p) \le bM$, where $k$ is the least-loaded machine for $L'$.
Then list scheduling of $R$ started from the loads $L$ and machine lists $\sigma$ produces a
schedule whose makespan $C$ satisfies $aC \le bM$. -/
theorem listScheduleScan_bound [NeZero m] {a b M : ℕ} {P : List ℕ} {loads : Fin m → ℕ}
    {σ : Fin m → List ℕ} (h : ScanInv P loads σ) (rest : List ℕ)
    (h0 : a * makespan σ ≤ b * M)
    (hstep : ∀ P' p rest' (loads' : Fin m → ℕ) (σ' : Fin m → List ℕ),
      P ++ rest = P' ++ p :: rest' → ScanInv P' loads' σ' →
        a * (loads' (leastLoaded loads') + p) ≤ b * M) :
    a * makespan (listScheduleScan loads σ rest).ret ≤ b * M := by
  induction rest generalizing P loads σ with
  | nil => simpa [listScheduleScan] using h0
  | cons p rest ih =>
      simp only [listScheduleScan, ret_bind]
      apply ih (h.step p)
      · have hmk := makespan_update_le (σ := σ) (leastLoaded loads) p
        rw [← h.1] at hmk
        have hp := hstep P p rest loads σ rfl h
        calc a * makespan _ ≤ a * max (makespan σ) (loads (leastLoaded loads) + p) :=
              Nat.mul_le_mul_left a hmk
          _ = max (a * makespan σ) (a * (loads (leastLoaded loads) + p)) :=
              (Nat.mul_max_mul_left a _ _).symm
          _ ≤ b * M := max_le h0 hp
      · intro P' p' rest' loads' σ' heq hinv
        exact hstep P' p' rest' loads' σ' (by simpa using heq) hinv

/-- **A least-loaded machine carries at most the average load.** Let $\sigma$ be a schedule of a
list $P$ of jobs on $m \ge 1$ machines, with load $\ell_i$ on machine $i$. Then $m$ times the load
of a least-loaded machine is at most the total processing time $T$ of the jobs in $P$, counted
with multiplicity: $m \min_i \ell_i \le T$. -/
theorem mul_leastLoaded_le [NeZero m] {P : List ℕ} {loads : Fin m → ℕ} {σ : Fin m → List ℕ}
    (h : ScanInv P loads σ) : m * loads (leastLoaded loads) ≤ P.sum := by
  have := Finset.card_nsmul_le_sum Finset.univ loads (loads (leastLoaded loads))
    (fun i _ => leastLoaded_le loads i)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  rw [← h.2.sum_sum]
  simpa [h.1] using this

/-! ## Graham's bound for list scheduling -/

/-- **Graham's bound for list scheduling.** Let $m \ge 1$ and let $J$ be a list of processing
times. Let $C$ be the makespan of the schedule that list scheduling on $m$ machines produces
from $J$, taking the jobs in the order of $J$, and let $M$ be the makespan of any schedule of $J$
on $m$ machines. Then $mC \le (2m - 1)M$, that is, $C \le (2 - 1/m)M$.

Source: Graham, "Bounds for certain multiprocessing anomalies", Bell System Technical Journal 45
(1966). -/
theorem listSchedule_approx [NeZero m] (ps : List ℕ) (τ : Fin m → List ℕ)
    (hτ : IsScheduleOf τ ps) :
    m * makespan (listSchedule m ps).ret ≤ (2 * m - 1) * makespan τ := by
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  apply listScheduleScan_bound scanInv_init ps (by simp)
  intro P' p rest' loads' σ' heq hinv
  simp only [List.nil_append] at heq
  set M := makespan τ
  set L := loads' (leastLoaded loads')
  have havg : m * L ≤ P'.sum := mul_leastLoaded_le hinv
  have hsum : P'.sum + p ≤ ps.sum := by rw [heq]; simp
  have hp : p ≤ M := hτ.le_makespan (by rw [heq]; simp)
  have hM : ps.sum ≤ m * M := hτ.sum_le
  have h1 : (m - 1) * p ≤ (m - 1) * M := Nat.mul_le_mul_left _ hp
  have h2 : (2 * m - 1) * M = m * M + (m - 1) * M := by
    rw [← Nat.add_mul]; congr 1; omega
  have h3 : m * p = p + (m - 1) * p := by
    conv_lhs => rw [show m = 1 + (m - 1) by omega]
    rw [Nat.add_mul, Nat.one_mul]
  rw [Nat.mul_add, h2]
  omega

/-! ## Graham's bound for LPT -/

/-- **Counting jobs when every machine is heavily loaded.** Let $\sigma$ be a schedule of a list
$P$ of jobs on $m$ machines, let $p$ and $M$ be natural numbers, and let $d = \max(M - p, 0)$. If
every job in $P$ is at least $p$ and every machine has load (the sum of its jobs) greater than
$d$, then $2m \le n + k$, where $n$ is the number of jobs in $P$ and $k$ is the number of jobs
$x$ in $P$ with $p \le x$ and $x > d$, both counted with multiplicity.

The reason is that each machine then holds two jobs or one job longer than $d$. -/
theorem two_mul_le_of_loads_gt {P : List ℕ} {σ : Fin m → List ℕ} (hσ : IsScheduleOf σ P)
    {p M : ℕ} (hP : ∀ x ∈ P, p ≤ x) (hload : ∀ i, M - p < (σ i).sum) :
    2 * m ≤ P.length + P.countP (fun x => decide (p ≤ x ∧ M - p < x)) := by
  rw [← hσ.sum_length, ← hσ.sum_countP (fun x => p ≤ x ∧ M - p < x), ← Finset.sum_add_distrib]
  have : ∀ i, 2 ≤ (σ i).length + (σ i).countP (fun x => decide (p ≤ x ∧ M - p < x)) := by
    intro i
    have hi := hload i
    match hσi : σ i with
    | [] => simp [hσi] at hi
    | [x] =>
        have hx : x ∈ P := by
          obtain := hσ.exists_mem
          have : x ∈ (∑ j, (σ j : Multiset ℕ)) :=
            Multiset.mem_sum.2 ⟨i, Finset.mem_univ i, by simp [hσi]⟩
          rw [hσ] at this
          exact Multiset.mem_coe.1 this
        simp only [hσi, List.sum_cons, List.sum_nil, Nat.add_zero] at hi
        simp [hP x hx, hi]
    | x :: y :: zs =>
        simp only [List.length_cons]
        omega
  calc 2 * m = ∑ _i : Fin m, 2 := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun i _ => this i

/-- **At most two long jobs per machine.** Let $p$ and $M$ be natural numbers with $M < 3p$,
and let $\ell$ be a list of natural numbers (the jobs of one machine) whose sum is at most $M$.
Then the number of entries of $\ell$ that are at least $p$, plus the number of entries that are
at least $p$ and greater than $M - p$, is at most $2$. Here $M - p$ is truncated subtraction,
equal to $0$ when $M < p$. So $\ell$ has at most two entries that are at least $p$, and at most
one if one of them is greater than $M - p$. -/
theorem countP_add_countP_le {l : List ℕ} {p M : ℕ} (hl : l.sum ≤ M) (h3 : M < 3 * p) :
    l.countP (fun x => decide (p ≤ x)) + l.countP (fun x => decide (p ≤ x ∧ M - p < x)) ≤ 2 := by
  have key : ∀ l : List ℕ, (l.filter (fun x => decide (p ≤ x))).sum ≤ l.sum := fun l =>
    (List.filter_sublist (l := l)).sum_le_sum (fun _ _ => Nat.zero_le _)
  have hf := (key l).trans hl
  have hc : l.countP (fun x => decide (p ≤ x ∧ M - p < x)) =
      (l.filter (fun x => decide (p ≤ x))).countP (fun x => decide (M - p < x)) := by
    rw [List.countP_filter]
    congr 1
    funext x
    simp only [Bool.decide_and]
    exact Bool.and_comm _ _
  rw [hc, List.countP_eq_length_filter (p := fun x => decide (p ≤ x))]
  have hall : ∀ x ∈ l.filter (fun x => decide (p ≤ x)), p ≤ x := by
    intro x hx
    simpa using (List.mem_filter.1 hx).2
  generalize l.filter (fun x => decide (p ≤ x)) = f at hf hall
  match f, hf, hall with
  | [], _, _ => simp
  | [x], _, _ =>
      have := List.countP_le_length (p := fun x => decide (M - p < x)) (l := [x])
      simp only [List.length_singleton] at this ⊢
      omega
  | [x, y], hf, hall =>
      have hx := hall x (by simp)
      have hy := hall y (by simp)
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hf
      simp only [List.length_cons, List.length_nil, List.countP_cons, List.countP_nil,
        decide_eq_true_eq]
      split_ifs <;> omega
  | x :: y :: z :: zs, hf, hall =>
      have hx := hall x (by simp)
      have hy := hall y (by simp)
      have hz := hall z (by simp)
      simp only [List.sum_cons] at hf
      omega

/-- **The LPT placement step.** Let $m \ge 1$ and let a list of job processing times, in
nonincreasing order, be the concatenation of a list $P$, a job $p$ and a list $R$. Let $\sigma$
be a schedule of the jobs $P$ on $m$ machines, with load $\ell_i$ on machine $i$, and let
$L = \min_i \ell_i$ be the load of a least-loaded machine. Then for every schedule $\tau$ of all
the jobs on the $m$ machines, with makespan $M$, we have $3m(L + p) \le (4m - 1)M$. -/
theorem lpt_step_le [NeZero m] {ps P rest : List ℕ} {p : ℕ} (hps : ps = P ++ p :: rest)
    (hsorted : ps.Pairwise (· ≥ ·)) {loads : Fin m → ℕ} {σ : Fin m → List ℕ}
    (hinv : ScanInv P loads σ) (τ : Fin m → List ℕ) (hτ : IsScheduleOf τ ps) :
    3 * m * (loads (leastLoaded loads) + p) ≤ (4 * m - 1) * makespan τ := by
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  set M := makespan τ
  set L := loads (leastLoaded loads)
  have hP : ∀ x ∈ P, p ≤ x := by
    intro x hx
    rw [hps, List.pairwise_append] at hsorted
    exact hsorted.2.2 x hx p (by simp)
  have hp : p ≤ M := hτ.le_makespan (by rw [hps]; simp)
  have hsum : P.sum + p ≤ ps.sum := by rw [hps]; simp
  have havg : m * L ≤ P.sum := mul_leastLoaded_le hinv
  have hM : ps.sum ≤ m * M := hτ.sum_le
  by_cases h3 : 3 * p ≤ M
  · have h2 : (4 * m - 1) * M = 3 * (m * M) + (m - 1) * M := by
      rw [show 4 * m - 1 = 3 * m + (m - 1) by omega, Nat.add_mul, Nat.mul_assoc]
    have h4 : 3 * ((m - 1) * p) ≤ (m - 1) * M := by
      calc 3 * ((m - 1) * p) = (m - 1) * (3 * p) := by ring
        _ ≤ (m - 1) * M := Nat.mul_le_mul_left _ h3
    have h5 : m * p = p + (m - 1) * p := by
      conv_lhs => rw [show m = 1 + (m - 1) by omega]
      rw [Nat.add_mul, Nat.one_mul]
    have h6 : 3 * m * (L + p) = 3 * (m * L) + 3 * (m * p) := by ring
    rw [h6, h2]
    omega
  · have h3 : M < 3 * p := Nat.lt_of_not_le h3
    suffices hLM : L + p ≤ M by
      calc 3 * m * (L + p) ≤ 3 * m * M := Nat.mul_le_mul_left _ hLM
        _ ≤ (4 * m - 1) * M := Nat.mul_le_mul_right _ (by omega)
    by_contra hgt
    have hgt : M < L + p := Nat.lt_of_not_le hgt
    have hload : ∀ i, M - p < (σ i).sum := by
      intro i
      rw [← hinv.1]
      have := leastLoaded_le loads i
      omega
    have hlpt := two_mul_le_of_loads_gt hinv.2 hP hload
    have hcmp : ps.countP (fun x => decide (p ≤ x)) +
        ps.countP (fun x => decide (p ≤ x ∧ M - p < x)) ≤ 2 * m := by
      rw [← hτ.sum_countP (fun x => p ≤ x), ← hτ.sum_countP (fun x => p ≤ x ∧ M - p < x),
        ← Finset.sum_add_distrib]
      calc _ ≤ ∑ _i : Fin m, 2 :=
            Finset.sum_le_sum fun i _ => countP_add_countP_le (le_makespan i) h3
        _ = 2 * m := by simp [Nat.mul_comm]
    have hbig : P.countP (fun x => decide (p ≤ x ∧ M - p < x)) ≤
        ps.countP (fun x => decide (p ≤ x ∧ M - p < x)) := by
      rw [hps]
      exact (List.sublist_append_left P (p :: rest)).countP_le
    have hge : P.length + 1 ≤ ps.countP (fun x => decide (p ≤ x)) := by
      rw [hps, List.countP_append, List.countP_cons_of_pos (by simp)]
      have : P.countP (fun x => decide (p ≤ x)) = P.length :=
        List.countP_eq_length.2 (fun x hx => by simpa using hP x hx)
      omega
    omega

/-- **Graham's bound for LPT scheduling.** Let $m \ge 1$ and let $J$ be a list of natural numbers
(job processing times). Let $C$ be the makespan of the schedule of $J$ on $m$ machines produced
by the LPT algorithm, and let $M$ be the makespan of any schedule $\tau$ of $J$ on $m$ machines.
Then $3mC \le (4m - 1)M$, that is, $C \le (4/3 - 1/(3m))M$.

Source: Graham, "Bounds on multiprocessing timing anomalies", SIAM J. Appl. Math. 17 (1969). -/
theorem lpt_approx [NeZero m] (ps : List ℕ) (τ : Fin m → List ℕ) (hτ : IsScheduleOf τ ps) :
    3 * m * makespan (lpt m ps).ret ≤ (4 * m - 1) * makespan τ := by
  set sorted := ((mergeSort (ps.map OrderDual.toDual)).ret).map OrderDual.ofDual
  have hperm : sorted.Perm ps := by
    have := (mergeSort_perm (ps.map OrderDual.toDual)).map OrderDual.ofDual
    simpa [sorted, List.map_map] using this
  have hsorted : sorted.Pairwise (· ≥ ·) := by
    have := mergeSort_sorted (ps.map OrderDual.toDual)
    exact List.Pairwise.map _ (fun a b h => h) this
  have hτ' : IsScheduleOf τ sorted := hτ.perm hperm.symm
  simp only [lpt, ret_bind]
  apply listScheduleScan_bound scanInv_init sorted (by simp)
  intro P' p rest' loads' σ' heq hinv
  exact lpt_step_le (by simpa using heq) hsorted hinv τ hτ'

/-! ## Validity and cost -/

/-- **List scheduling schedules every job.** For $m \ge 1$ and every list $J$ of processing
times, the assignment that list scheduling on $m$ machines produces from $J$ is a schedule of
$J$. -/
theorem listSchedule_isScheduleOf [NeZero m] (ps : List ℕ) :
    IsScheduleOf (listSchedule m ps).ret ps := by
  simpa [listSchedule] using listScheduleScan_isScheduleOf scanInv_init ps

theorem lpt_isScheduleOf [NeZero m] (ps : List ℕ) : IsScheduleOf (lpt m ps).ret ps := by
  have hperm : (((mergeSort (ps.map OrderDual.toDual)).ret).map OrderDual.ofDual).Perm ps := by
    have := (mergeSort_perm (ps.map OrderDual.toDual)).map OrderDual.ofDual
    simpa [List.map_map] using this
  simp only [lpt, ret_bind]
  exact (listSchedule_isScheduleOf _).perm hperm

@[simp]
theorem listScheduleScan_time [NeZero m] (loads : Fin m → ℕ) (σ : Fin m → List ℕ)
    (ps : List ℕ) : (listScheduleScan loads σ ps).time = ps.length * m := by
  induction ps generalizing loads σ with
  | nil => simp [listScheduleScan]
  | cons p ps ih => simp [listScheduleScan, ih, Nat.add_mul, Nat.add_comm]

/-- **Running time of list scheduling.** For $m \ge 1$ and every list of $n$ jobs, list
scheduling on $m$ machines has cost exactly $nm$, in the cost model that charges $m$ for each job
placed (one unit per machine load inspected). -/
@[simp]
theorem listSchedule_time [NeZero m] (ps : List ℕ) :
    (listSchedule m ps).time = ps.length * m :=
  listScheduleScan_time _ _ ps

/-- **Running time of LPT.** On $m \ge 1$ machines and a list of $n$ jobs, LPT costs at most
$n \lceil \log_2 n \rceil + nm$, counting merge-sort comparisons and machine load inspections. -/
theorem lpt_time_le [NeZero m] (ps : List ℕ) :
    (lpt m ps).time ≤ ps.length * Nat.clog 2 ps.length + ps.length * m := by
  have hs := mergeSort_time (ps.map OrderDual.toDual)
  have hlen := mergeSort_same_length (ps.map OrderDual.toDual)
  simp only [List.length_map] at hs hlen
  simp only [lpt, time_bind, listSchedule_time, List.length_map, hlen]
  omega

end Cslib.Algorithms.Lean.Scheduling
