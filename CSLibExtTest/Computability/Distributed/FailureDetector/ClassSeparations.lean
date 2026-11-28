/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.FailureDetector.ClassSeparations

/-!
# Tests for separations of failure detector classes

These strict inclusions compare sets of detectors. One two-process history protects some
process at each tick but protects neither process at all ticks. A second history suspects a
target before it crashes, without ever suspecting a correct process.
-/

namespace Cslib.Distributed.FailureDetector.DetectorClass

private abbrev classes (n : ℕ) (k : DetectorClass) := k.detectors (Proc := Fin n)

-- Four proper completeness inclusions for every population from three onwards.
example {n : ℕ} (hn : 3 ≤ n) :
    classes n .perfect ⊂ classes n .q ∧ classes n .strong ⊂ classes n .weak ∧
    classes n .eventuallyPerfect ⊂ classes n .eventuallyQ ∧
    classes n .eventuallyStrong ⊂ classes n .eventuallyWeak := by
  have hpos : 0 < n := by omega
  simp [classes, ssubset_iff_subset_not_subset, detectors_subset_iff hpos,
    allObservers, allTargets, perpetual, hn]

-- All eight accuracy arrows are already proper at two, without an upper bound on n.
example {n : ℕ} (hn : 2 ≤ n) :
    classes n .perfect ⊂ classes n .strong ∧ classes n .perfect ⊂ classes n .eventuallyPerfect ∧
    classes n .strong ⊂ classes n .eventuallyStrong ∧
    classes n .eventuallyPerfect ⊂ classes n .eventuallyStrong ∧
    classes n .q ⊂ classes n .weak ∧ classes n .q ⊂ classes n .eventuallyQ ∧
    classes n .weak ⊂ classes n .eventuallyWeak ∧ classes n .eventuallyQ ⊂ classes n .eventuallyWeak := by
  have hpos : 0 < n := by omega
  simp [classes, ssubset_iff_subset_not_subset, detectors_subset_iff hpos,
    allObservers, allTargets, perpetual, hn]

example : classes 1 .perfect ⊂ classes 1 .eventuallyPerfect := by
  simp [classes, ssubset_iff_subset_not_subset, detectors_subset_iff (by decide : 0 < 1),
    allObservers, allTargets, perpetual]

-- Suspect process 0 only at tick 0, and process 1 only at tick 1. This history leaves a
-- choice of a safe target at each tick, but that choice cannot be made once and for all.
private def staggered : History (Fin 2) := fun _ t => {p | t = p.val}

private def crashFree : FailurePattern (Fin 2) where
  crashedBy _ := ∅
  mono := monotone_const
  exists_correct := ⟨0, fun _ => Set.notMem_empty _⟩

private def staggeredDetector : Detector (Fin 2) :=
  fun F => {H | F = crashFree ∧ H = staggered}

example : ∀ t, ∃ p ∈ crashFree.correct, ∀ q, p ∉ staggered q t := by
  intro t
  by_cases ht : t = 0
  · exact ⟨1, fun _ => Set.notMem_empty _, fun _ => by simp [staggered, ht]⟩
  · exact ⟨0, fun _ => Set.notMem_empty _, fun _ => ht⟩

example : staggeredDetector ∈ classes 2 .eventuallyPerfect ∧ staggeredDetector ∉ classes 2 .weak := by
  constructor
  · constructor
    · rintro _ _ ⟨rfl, rfl⟩
      exact ⟨0, fun _ ⟨_, h⟩ => h.elim⟩
    · rintro _ _ ⟨rfl, rfl⟩
      exact ⟨2, fun _ ht p _ _ _ h => (Nat.not_lt_of_ge ht) (h ▸ p.isLt)⟩
  · intro h
    obtain ⟨p, _, hnever⟩ := h.2 crashFree staggered ⟨rfl, rfl⟩
    exact hnever p.val p (Set.notMem_empty _) rfl

-- A report from a correct observer about a target that crashes *later* still counts against
-- perpetual strong accuracy. No correct target is ever suspected in this example.
private def lateCrash : FailurePattern (Fin 2) where
  crashedBy t := {p | p = 1 ∧ 1 ≤ t}
  mono := fun _ _ h _ hp => ⟨hp.1, hp.2.trans h⟩
  exists_correct := ⟨0, fun _ h => (by decide : (0 : Fin 2) ≠ 1) h.1⟩

private def earlyReport : History (Fin 2) := fun _ _ => {1}

private def earlyDetector : Detector (Fin 2) := fun F => {H | F = lateCrash ∧ H = earlyReport}

example : earlyDetector ∈ classes 2 .eventuallyPerfect ∧ earlyDetector ∉ classes 2 .q := by
  constructor
  · constructor
    · rintro _ _ ⟨rfl, rfl⟩
      exact ⟨0, fun _ ⟨_, hp, _⟩ _ _ _ _ => hp⟩
    · rintro _ _ ⟨rfl, rfl⟩
      exact ⟨0, fun _ _ _ hp _ _ hs => hp 1 ⟨hs, le_rfl⟩⟩
  · intro h
    exact h.2 lateCrash earlyReport ⟨rfl, rfl⟩ 0 1 0
      (fun hc => Nat.not_succ_le_zero 0 hc.2) (fun hc => Nat.not_succ_le_zero 0 hc.2) rfl

end Cslib.Distributed.FailureDetector.DetectorClass
