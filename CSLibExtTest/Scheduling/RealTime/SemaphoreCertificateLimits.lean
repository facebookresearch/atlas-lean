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
# Limits of sufficient semaphore exit certificates

A late arrival and a holdings-dependent demotion give two ways that a real dispatch can be forced
to wait for a lower job's V without a certificate. In both examples the admitted prefix is unique;
the tests also check the changes of resource admission or effective rank that matter for dispatch.
The absence of a certificate is not evidence of the absence of blocking. A solo job executing V
is contrasted with a positive circular guard derivation. These are finite examples concerning the
resource-access model in L. Sha, R. Rajkumar and J. P. Lehoczky, “Priority Inheritance Protocols:
An Approach to Real-Time Synchronization”, IEEE Transactions on Computers 39(9), 1990, §II,
pp. 1176–1177. No inheritance or ceiling algorithm is assumed.
-/

namespace Cslib.Scheduling.RealTime.Semaphore.Limits

private abbrev compute : Program ℕ := ⟨1, 0, Fin.elim0, fun k => k.elim0, fun k => k.elim0⟩

-- P(r), work, V(r).
private abbrev single (r : ℕ) : Program ℕ where
  length := 3
  count := 1
  sec := fun _ => ⟨r, 0, 2⟩
  bounds := fun _ => ⟨Nat.zero_lt_succ 1, Nat.lt_succ_self 2⟩
  ordered := fun _ _ h => (not_lt_of_ge (le_of_eq (Subsingleton.elim _ _)) h).elim

-- P(S), P(T), work, V(T), V(S), work. The last V is not termination.
private abbrev nested (s t : ℕ) (ne : s ≠ t) : Program ℕ where
  length := 6
  count := 2
  sec k := if k = 0 then ⟨s, 0, 4⟩ else ⟨t, 1, 3⟩
  bounds := by
    intro k
    split
    · exact (show 0 < 4 ∧ 4 < 6 by decide)
    · exact (show 1 < 3 ∧ 3 < 6 by decide)
  ordered := by
    intro k l lt
    fin_cases k <;> fin_cases l <;> first | exact (by decide : ¬ (_ < _)) lt |>.elim
                                           | exact Or.inr ⟨(show 0 < 1 ∧ 3 < 4 by decide), ne⟩

private def calendar {n} (times : Fin n → ℕ) : Arrivals n :=
  ⟨times, Fin.val, fun _ _ _ eq => Fin.ext eq⟩

private def schedule {n} (owners : List (Fin n)) : Schedule (Fin n) := fun t => owners[t]?

-- A CPU job (0) arrives while job 1 owns S=7. Job 2 uses T=8 but cannot yet run.
private abbrev arrivalCase : Workload (Fin 3) ℕ 3 :=
  ⟨id, Fin.val, fun i => if i = 0 then compute else if i = 1 then nested 7 8 (by decide)
    else single 8, fun _ _ h => h⟩
private abbrev priorityOnS : Protocol ℕ :=
  ⟨fun _ _ => [], fun base locks => if 7 ∈ locks then 0 else base, fun _ => rfl⟩
private abbrev arrivals := calendar (fun i : Fin 3 => if i = 0 then 1 else if i = 1 then 0 else 12)
private abbrev traceA := schedule (n := 3) [1, 1, 1, 1, 1, 0]
private abbrev atOne := service traceA 1
private abbrev outer : Fin (arrivalCase.code 1).count := ⟨0, by decide⟩

private theorem realA : Admissible arrivalCase priorityOnS arrivals traceA 6 := by decide

-- Every admitted prefix runs the owner through V(S) before the victim's first instruction.
example (s : Schedule (Fin 3)) (h : Admissible arrivalCase priorityOnS arrivals s 6) :
    (∀ t < 5, s t = some 1) ∧ s 5 = some 0 := by
  refine ⟨fun t ht => ?_, admissible_agree _ _ h realA (by decide : 5 < 6)⟩
  rw [admissible_agree _ _ h realA (by omega : t < 6)]
  exact (by decide : ∀ u : Fin 5, traceA u = some 1) ⟨t, ht⟩

-- Before V(S), the victim is eligible, but the enabled owner's held S gives it the same rank
-- and its earlier arrival wins. Once V(S) has run that priority advantage disappears.
example : ∀ u : Fin 5, 1 ≤ u.val →
    Enabled arrivalCase priorityOnS (service traceA u) 0 ∧
    Enabled arrivalCase priorityOnS (service traceA u) 1 ∧
    current arrivalCase priorityOnS (service traceA u) 1 = 0 ∧
    (arrivalCase.code 1 |>.sec outer).Held (service traceA u 1) := by
  intro u hu; fin_cases u <;> first | exact (by decide : ¬ (1 ≤ 0)) hu |>.elim | exact ⟨by decide, by decide, rfl, by decide⟩

example : current arrivalCase priorityOnS (service traceA 5) 1 = 1 ∧
    arrivals.time 1 < arrivals.time 0 ∧ 1 < arrivals.time 2 := by decide

-- The owner still has ordinary work at slot 5. The high job wins as soon as S is gone. At
-- slot 1, the very same released jobs would already select the high job without rank promotion.
example : First arrivalCase priorityOnS arrivals 5 (service traceA 5) 0 ∧
    Enabled arrivalCase priorityOnS (service traceA 5) 1 ∧
    First arrivalCase .ordinary arrivals 1 atOne 0 := by
  let := decFirst arrivalCase priorityOnS arrivals 5 (service traceA 5) 0
  let := decFirst arrivalCase .ordinary arrivals 1 atOne 0
  exact ⟨by decide, by decide, by decide⟩

-- A genuinely impossible dispatch at slot 1 has no release check in the relaxation. It
-- starts job 2 on T. Job 1 then cannot take T and job 0 can run with S still held.
private theorem earlyEscape : ¬ CertifiedExitDependency arrivalCase priorityOnS arrivals atOne 0 1 outer := by
  intro cert
  let z := advance atOne 2
  have early : ProtectedMove arrivalCase priorityOnS arrivals atOne z :=
    ⟨2, by decide, rfl, fun j _ lt _ => (by decide : ∀ j : Fin 3, ¬ (2 < j.val)) j lt |>.elim⟩
  have denied : ¬ Enabled arrivalCase priorityOnS z 1 := by dsimp [z]; decide
  have victim : ProtectedMove arrivalCase priorityOnS arrivals z (advance z 0) := by
    refine ⟨0, by dsimp [z]; decide, rfl, ?_⟩
    intro j en lower prom
    fin_cases j
    · exact (Nat.lt_irrefl 0 lower).elim
    · exact (denied en).elim
    · exact (Nat.lt_irrefl 2 prom).elim
  have before := cert.exited_before_step (by decide) (.single early) victim
  exact (by decide : ¬ (4 < advance atOne 2 1)) before

example : ¬ CertifiedBlockedAt arrivalCase priorityOnS arrivals traceA 1 0 1 outer :=
  fun h => earlyEscape h.2.2.2

-- Demotion without shared resources: the high job owns U=4; the lower job holds S=7, T=8.
-- Exactly one held lock worsens the rank by five. Releasing T changes the owner's rank from
-- 1 to 6, putting it behind the enabled victim at rank 5, even though it still holds S.
private abbrev demotionCase : Workload (Fin 2) ℕ 2 :=
  ⟨id, Fin.val, Fin.cases (single 4) (fun _ => nested 7 8 (by decide)), fun _ _ h => h⟩
private abbrev demote : Protocol ℕ :=
  ⟨fun _ _ => [], fun p locks => if locks.length = 1 then p + 5 else p, fun _ => rfl⟩
private abbrev released := calendar (fun i : Fin 2 => if i = 0 then 3 else 0)
private abbrev traceD := schedule (n := 2) [1, 1, 1, 0, 1, 0, 0, 1, 1]
private theorem realD : Admissible demotionCase demote released traceD 9 := by decide

example (s : Schedule (Fin 2)) (ok : Admissible demotionCase demote released s 9) :
    s 4 = some 1 ∧ s 5 = some 0 ∧ (demotionCase.code 1).instruction (service traceD 4 1) = .release 8 :=
  ⟨admissible_agree _ _ ok realD (by decide : 4 < 9),
   admissible_agree _ _ ok realD (by decide : 5 < 9), rfl⟩

example : Enabled demotionCase demote (service traceD 4) 0 ∧
    current demotionCase demote (service traceD 4) 0 = 5 ∧
    current demotionCase demote (service traceD 4) 1 = 1 ∧
    current demotionCase demote (service traceD 5) 1 = 6 ∧
    ((demotionCase.code 1).sec (0 : Fin 2)).Held (service traceD 5 1) :=
  ⟨by decide, rfl, rfl, rfl, by decide⟩

-- An empty certified set for *all* arrival patterns despite the forced reversal above.
example : certifiedBlockers demotionCase demote 0 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro k ⟨_, a, s, t, _, _, cert⟩
  let x := service s t
  have live : x 0 < 3 := cert.pending
  have enabled : Enabled demotionCase demote x 0 := by
    refine ⟨live, fun j diff l _ => ?_⟩
    fin_cases j
    · exact (diff rfl).elim
    · have alts : x 0 = 0 ∨ x 0 = 1 ∨ x 0 = 2 := by omega
      rcases alts with eq | eq | eq <;> rw [eq] <;> fin_cases l <;> decide
  have step : ProtectedMove demotionCase demote a x (advance x 0) := by
    refine ⟨0, enabled, rfl, fun j _ _ promo => ?_⟩
    unfold current at promo; dsimp only [demote] at promo
    split at promo <;> omega
  exact (not_lt_of_ge cert.held.2) (cert.exited_before_step (by decide) .refl step)

-- A solo V is not an earlier exit by a different job. But positive resource edges may form
-- a cycle even if no job is able to move. These two cases must not be conflated.
private abbrev solo : Workload Unit ℕ 1 := ⟨fun _ => (), fun _ => 0, fun _ => single 4, fun _ _ _ => le_rfl⟩
private abbrev alone : Schedule (Fin 1) := fun _ => some 0
private abbrev start := calendar (fun _ : Fin 1 => 0)
example : Admissible solo .ordinary start alone 3 ∧
    (solo.code 0).instruction (service alone 2 0) = .release 4 ∧
    ¬ CertifiedExitDependency solo .ordinary start (service alone 2) 0 0 (0 : Fin 1) := by
  refine ⟨solo_admissible _ _ _ rfl, rfl, ?_⟩
  rintro (guard | ⟨diff, _⟩)
  · have impossible {i j k} (g : GuardExitCertificate solo .ordinary (service alone 2) i j k) : False := by
      induction g with
      | guard diff _ _ _ => exact diff (Subsingleton.elim _ _)
      | inner _ _ _ ih | chain _ _ ih _ => exact ih
    exact impossible guard
  · exact diff rfl

private abbrev cycle : Workload (Fin 2) ℕ 2 :=
  ⟨id, Fin.val, Fin.cases (nested 7 8 (by decide)) (fun _ => nested 8 7 (by decide)), fun _ _ h => h⟩
private abbrev stagger := calendar (fun i : Fin 2 => if i = 0 then 1 else 0)
private abbrev stuckRun := schedule (n := 2) [1, 0]
private abbrev endState := service stuckRun 2
example : Admissible cycle .ordinary stagger stuckRun 3 ∧
    (∀ i, ¬ Enabled cycle .ordinary endState i) ∧
    CertifiedExitDependency cycle .ordinary stagger endState 0 0 (0 : Fin 2) := by
  refine ⟨by decide, by decide, Or.inl ?_⟩
  exact .chain (j := 1) (k := (0 : Fin 2))
    (.guard (by decide) (by decide) (by decide) (by decide))
    (.guard (by decide) (by decide) (by decide) (by decide))

end Cslib.Scheduling.RealTime.Semaphore.Limits
