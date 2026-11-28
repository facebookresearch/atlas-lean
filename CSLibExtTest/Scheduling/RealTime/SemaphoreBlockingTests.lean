/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Scheduling.RealTime.SemaphoreBlocking
import Mathlib.Tactic.FinCases

/-!
# Executions with nested and disjoint binary semaphore sections

Concrete clients for the job, critical section and blocking definitions of L. Sha, R. Rajkumar
and J. P. Lehoczky, “Priority Inheritance Protocols: An Approach to Real-Time Synchronization”,
IEEE Transactions on Computers 39(9), 1990, §II, pp. 1176–1177. Distinct arrival patterns yield
different certified blocking episodes for one workload. The examples distinguish mandatory exits
from exits that only happen to precede service. Maximality below is in the certified set only.
-/

namespace Cslib.Scheduling.RealTime.Semaphore.Tests

private abbrev one (s : Bool) : Program Bool where
  length := 2
  count := 1
  sec := fun _ => ⟨s, 0, 1⟩
  bounds := by cases s <;> decide
  ordered := fun k l h => (not_lt_of_ge (le_of_eq (Subsingleton.elim _ _)) h).elim

-- P(S), P(T), work, V(T), V(S).
private abbrev nested : Program Bool where
  length := 5
  count := 2
  sec := fun k => if k = 0 then ⟨false, 0, 4⟩ else ⟨true, 1, 3⟩
  bounds := by decide
  ordered := by decide

-- P(S), work, V(S); P(S), work, work, V(S).
private abbrev disjoint : Program Bool where
  length := 7
  count := 2
  sec := fun k => if k = 0 then ⟨false, 0, 2⟩ else ⟨false, 3, 6⟩
  bounds := by decide
  ordered := by decide

private def cpu (n : ℕ) : Program Bool := ⟨n, 0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩

private abbrev pair (high low : Program Bool) : Workload (Fin 2) Bool 2 :=
  ⟨id, Fin.val, Fin.cases high (fun _ => low), fun _ _ h => h⟩

private def arrive {n} (t : Fin n → ℕ) : Arrivals n :=
  ⟨t, Fin.val, fun _ _ _ eq => Fin.ext eq⟩

private def late (t : ℕ) : Arrivals 2 := arrive (fun i => if i = 0 then t else 0)

private def slots {n} (jobs : List (Fin n)) : Schedule (Fin n) := fun t => jobs[t]?

private abbrev both := pair (one false) nested
private abbrev onlyT := pair (one true) nested
private abbrev twice := pair (one false) disjoint
private instance : NeZero (both.code 1).count := ⟨by decide⟩
private instance : NeZero (onlyT.code 1).count := ⟨by decide⟩
private instance : NeZero (twice.code 1).count := ⟨by decide⟩
private abbrev lowStart : Schedule (Fin 2) := fun _ => some 1

example : (List.range 5).map nested.instruction =
    [.acquire false, .acquire true, .cpu, .release true, .release false] := by decide

example : ¬ (Section.mk false 0 5).Before ⟨false, 1, 3⟩ ∧
    ¬ (Section.mk false 0 3).Before ⟨true, 1, 4⟩ := by decide

-- Both acquisitions actually ran; the higher job arrives while both locks are held.
private theorem outer_blocks : 0 ∈ certifiedBlockers both .ordinary 0 1 :=
  ⟨by decide, late 2, lowStart, 2, by decide, by decide,
    Or.inl (.guard (by decide) (by decide) (by decide) (by decide))⟩

private theorem inner_blocks : 1 ∈ certifiedBlockers both .ordinary 0 1 :=
  ⟨by decide, late 2, lowStart, 2, by decide, by decide,
    Or.inl (.inner (.guard (k := 0) (by decide) (by decide) (by decide) (by decide))
      (by decide) (by decide))⟩

example : CertifiedThrough both .ordinary 0 1 true := ⟨1, inner_blocks, rfl⟩

example : maximalCertifiedBlockers both .ordinary 0 1 = {0} := by
  ext k
  fin_cases k
  · exact ⟨fun _ => rfl, fun _ => ⟨outer_blocks, fun l _ => by fin_cases l <;> decide⟩⟩
  · constructor
    · intro h; exact (h.2 0 outer_blocks (by decide)).elim
    · intro h; exact (by decide : (1 : Fin 2) ≠ 0) h |>.elim

-- Releasing T is enough for a job requesting T. S remains held while that job executes.
private abbrev tRun := slots (n := 2) [1, 1, 1, 1, 0, 0, 1]
example : Admissible onlyT .ordinary (late 2) tRun 7 := by decide

private theorem only_inner_blocks : 1 ∈ certifiedBlockers onlyT .ordinary 0 1 :=
  ⟨by decide, late 2, tRun, 2, by decide, by decide,
    Or.inl (.guard (by decide) (by decide) (by decide) (by decide))⟩

private theorem path_step {w : Workload (Fin 2) Bool 2} {a : Arrivals 2} {x : Fin 2 → ℕ}
    (i : Fin 2) (h : Enabled w .ordinary x i) :
    Relation.ReflTransGen (ProtectedMove w .ordinary a) x (advance x i) :=
  .single (ordinary_protectedMove.mpr ⟨i, h, rfl⟩)

-- Enumerate the two possible pending PCs and four possible open-S PCs. From *each* pair,
-- either the victim steps now, or T's owner takes its remaining steps through V(T) and the
-- victim steps immediately thereafter. No such path executes V(S).
private theorem escape (a : Arrivals 2) (x : Fin 2 → ℕ) (hx : x 0 < 2) (lo : 0 < x 1)
    (hi : x 1 ≤ 4) : ∃ y, Relation.ReflTransGen (ProtectedMove onlyT .ordinary a) x y ∧
      x 0 < y 0 ∧ y 1 ≤ 4 := by
  let can (x : Fin 2 → ℕ) (i : Fin 2) : Bool := decide (Enabled onlyT .ordinary x i)
  let x' (p : Fin 2) (q : Fin 5) := fun i : Fin 2 => if i = 0 then p.val else q.val
  have check : ∀ p q, 0 < q.val →
      (can (x' p q) 0 ∨
       (can (x' p q) 1 ∧
        (can (advance (x' p q) 1) 0 ∧ q.val + 1 ≤ 4 ∨
         can (advance (x' p q) 1) 1 ∧
         can (advance (advance (x' p q) 1) 1) 0 ∧ q.val + 2 ≤ 4))) := by
    dsimp only [x', can]
    decide
  simp only [can, decide_eq_true_eq] at check
  let p : Fin 2 := ⟨_, hx⟩
  let q : Fin 5 := ⟨x 1, by omega⟩
  have eq : x' p q = x := by funext i; fin_cases i <;> rfl
  have routes := check p q lo
  rw [eq] at routes
  rcases routes with now | ⟨step, ⟨now, bound⟩ | ⟨step', now, bound⟩⟩
  · exact ⟨_, path_step 0 now, by simp [advance], by simpa [advance] using hi⟩
  · exact ⟨_, (path_step 1 step).trans (path_step 0 now), by simp [advance], by simpa [advance] using bound⟩
  · exact ⟨_, ((path_step 1 step).trans (path_step 1 step')).trans (path_step 0 now),
      by simp [advance], by simpa [advance, Nat.add_assoc] using bound⟩

private theorem not_outer : 0 ∉ certifiedBlockers onlyT .ordinary 0 1 := by
  rintro ⟨_, a, s, t, hadm, _, dep⟩
  let x := service s t
  have held := dep.held
  have pending : x 0 < 2 := dep.pending
  obtain ⟨y, path, prog, bound⟩ := escape a x pending held.1 held.2
  have := dep.passed_of_progress path prog
  change 4 < y 1 at this
  omega

example : maximalCertifiedBlockers onlyT .ordinary 0 1 = {1} := by
  ext k; fin_cases k
  · exact ⟨fun h => (not_outer h.1).elim, fun h => ((by decide : (0 : Fin 2) ≠ 1) h).elim⟩
  · exact ⟨fun _ => rfl, fun _ => ⟨only_inner_blocks, fun l hl => by
      fin_cases l
      · exact (not_outer hl).elim
      · decide⟩⟩

-- Two disjoint sections on S are both maximal for the same victim. Different release times of
-- the victim witness the two episodes. Their solo body durations are one and two, respectively.
private theorem disjoint_max (k : Fin 2) : k ∈ maximalCertifiedBlockers twice .ordinary 0 1 := by
  refine ⟨?_, fun l _ => by fin_cases k <;> fin_cases l <;> decide⟩
  fin_cases k
  · exact ⟨by decide, late 1, lowStart, 1, by decide, by decide,
      Or.inl (.guard (by decide) (by decide) (by decide) (by decide))⟩
  · exact ⟨by decide, late 4, lowStart, 4, by decide, by decide,
      Or.inl (.guard (by decide) (by decide) (by decide) (by decide))⟩

example : (⟨1, 0⟩ : (j : Fin 2) × Fin (twice.code j).count) ∈ maximalCertifiedUnion twice .ordinary 0 ∧
    ⟨1, 1⟩ ∈ maximalCertifiedUnion twice .ordinary 0 ∧
    (disjoint.sec 0).duration < (disjoint.sec 1).duration :=
  ⟨disjoint_max 0, disjoint_max 1, by decide⟩

-- The outer body's three local steps occupy five wall slots because both high-job steps
-- intervene before V(S). The high job did not need to wait for V(S).
example : (nested.sec 0).duration = service tRun 6 1 - service tRun 1 1 ∧
    (nested.sec 0).duration < 6 - 1 ∧ tRun 6 = some 1 := by decide

-- Equal-priority jobs 0 and 1 are instances of the same task. Job 1 arrived first, even
-- though it has the larger index. Job 2 is a genuinely lower-priority third job.
private abbrev tied : Workload ℕ Bool 3 where
  task i := i.val / 2
  priority := id
  code i := if i = 2 then nested else cpu 2
  numbered := fun _ _ h => Nat.div_le_div_right h

private abbrev arrivals3 := arrive (fun i : Fin 3 => 2 - i.val)
private abbrev tiedRun := slots (n := 3) [2, 1, 1, 0, 0, 2, 2, 2, 2]

example : tied.task 0 = tied.task 1 ∧ tied.base 0 = tied.base 1 ∧ tied.base 1 < tied.base 2 ∧
    Admissible tied .ordinary arrivals3 tiedRun 9 ∧
    ¬ First tied .ordinary arrivals3 2 (service tiedRun 2) 0 := by
  refine ⟨rfl, rfl, by decide, by decide, fun sel => ?_⟩
  have later := sel.2.2 1 (by decide) (by decide)
  change 0 < 0 ∨ (0 = 0 ∧ (2 < 1 ∨ (2 = 1 ∧ 0 ≤ 1))) at later
  omega

example : certifiedBlockers tied .ordinary 0 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro k h; exact (Nat.lt_irrefl 0) (lower_of_mem_certifiedBlockers h).2

-- The earlier equal-priority job really holds the semaphore the later one requests. That
-- creates an exit obligation, but is not lower-priority blocking, even with different indices.
private abbrev sameTask : Workload Unit Bool 2 :=
  ⟨fun _ => (), fun _ => 0, fun _ => one false, fun _ _ _ => le_rfl⟩

example : Admissible sameTask .ordinary (late 1) lowStart 1 ∧
    GuardExitCertificate sameTask .ordinary (service lowStart 1) 0 1 (0 : Fin 1) ∧
    (0 : Fin 1) ∉ certifiedBlockers sameTask .ordinary 0 1 :=
  ⟨by decide, .guard (by decide) (by decide) (by decide) (by decide),
    fun h => (Nat.lt_irrefl 0) (lower_of_mem_certifiedBlockers h).2⟩

-- A different owner of T must exit even though the high job requests only S:
-- low owns T, middle owns S and needs T, high needs S. All three finish in this trace.
private abbrev chained : Workload (Fin 3) Bool 3 :=
  ⟨id, Fin.val, fun i => if i = 0 then one false else if i = 1 then nested else one true,
    fun _ _ h => h⟩
private abbrev chainRun := slots (n := 3) [2, 1, 2, 1, 1, 1, 1, 0, 0]

example : Admissible chained .ordinary arrivals3 chainRun 9 ∧
    CertifiedThroughAt chained .ordinary arrivals3 chainRun 2 0 2 true := by
  refine ⟨by decide, (0 : Fin 1), ⟨by decide, by decide, by decide, Or.inl ?_⟩, rfl⟩
  exact .chain (j := 1) (k := (0 : Fin 2))
    (.guard (by decide) (by decide) (by decide) (by decide))
    (.guard (by decide) (by decide) (by decide) (by decide))

-- A rank-changing protocol, not a priority-inheritance algorithm: while holding S the
-- lower job runs at rank zero. A high job needing only CPU really must await its V(S):
-- the victim cannot be the first mover even after ordinary CPU competition is removed.
private def promoted : Protocol Bool :=
  ⟨fun _ _ => [], fun p held => if held.isEmpty then p else 0, fun _ => rfl⟩
private abbrev boosted := pair (cpu 1) (one false)
private abbrev boostRun := slots (n := 2) [1, 1, 0]

example : Admissible boosted promoted (late 1) boostRun 3 ∧
    CertifiedBlockedAt boosted promoted (late 1) boostRun 1 0 1 (0 : Fin 1) := by
  have ok : Admissible boosted promoted (late 1) boostRun 3 := by decide
  refine ⟨ok, by decide, by decide, by decide, Or.inr ⟨by decide, by decide, ?_, ?_⟩⟩
  · exact ⟨_, protectedPath_of_admissible ok (u := 1) (by decide), by decide⟩
  · intro y path progress
    rcases path.cases_head with rfl | ⟨mid, step, rest⟩
    · exact (lt_irrefl _ progress).elim
    · obtain ⟨q, _, rfl, choose⟩ := step
      fin_cases q
      · have impossible := choose 1 (by decide) (by decide) (by decide)
        exact (by decide : ¬ (_ < _ ∨ (_ = _ ∧ (_ < _ ∨ (_ = _ ∧ _ ≤ _))))) impossible |>.elim
      · exact (show 1 < 2 by decide).trans_le (service_mono_of_protectedPath rest 1)

end Cslib.Scheduling.RealTime.Semaphore.Tests
