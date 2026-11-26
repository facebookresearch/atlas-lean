/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.FailureDetector
import Mathlib.Data.Fintype.Fin

/-!
# Tests for failure detector classes

These finite populations have histories over all natural-number ticks. Alternating histories
check that the eventual witnesses are fixed for the entire suffix, not chosen at each tick.
-/

namespace Cslib.Distributed.FailureDetector

private def thresholdCrash (n k τ : ℕ) (hn : 0 < n) (hk : 0 < k) : FailurePattern (Fin n) where
  crashedBy t := {p | k ≤ p.val ∧ τ ≤ t}
  mono := by
    intro s t hst p h
    exact ⟨h.1, Nat.le_trans h.2 hst⟩
  exists_correct := ⟨⟨0, hn⟩, fun _ h => (Nat.not_le_of_lt hk) h.1⟩

private def sample {n : ℕ} (F : FailurePattern (Fin n)) (H : History (Fin n)) : Detector (Fin n) :=
  fun F' => {H' | F' = F ∧ H' = H}

private def oneCrash := thresholdCrash 3 2 0 (by decide) (by decide)

private def alternatingObservers : History (Fin 3) := fun q t =>
  {p | 2 ≤ p.val ∧ q.val = t % 2}

-- There is a correct observer at every tick, but no single observer for an entire suffix.
example : ∃ T : ℕ, ∀ p ∈ oneCrash.crashed, ∀ t ≥ T,
    ∃ q ∈ oneCrash.correct, p ∈ alternatingObservers q t := by
  refine ⟨0, ?_⟩
  intro p hp t _
  obtain ⟨_, hp, _⟩ := hp
  refine ⟨⟨t % 2, by omega⟩, ?_, ⟨hp, rfl⟩⟩
  intro s hs
  change 2 ≤ t % 2 ∧ 0 ≤ s at hs
  omega

example : ¬ (sample oneCrash alternatingObservers).WeakCompleteness := by
  intro h
  obtain ⟨T, hT⟩ := h oneCrash alternatingObservers ⟨rfl, rfl⟩
  obtain ⟨q, _, hq⟩ := hT 2 ⟨0, by decide, by decide⟩
  have h₀ : q.val = T % 2 := (hq T le_rfl).2
  have h₁ : q.val = (T + 1) % 2 := (hq (T + 1) (Nat.le_succ T)).2
  omega

private def twoCrashes := thresholdCrash 4 2 0 (by decide) (by decide)

private def splitObservers : History (Fin 4) := fun q _ => {p | p.val = q.val + 2}

-- Crash 2 has observer 0, and crash 3 has observer 1. Weak completeness allows that split.
example : (sample twoCrashes splitObservers).WeakCompleteness := by
  rintro _ _ ⟨rfl, rfl⟩
  refine ⟨0, ?_⟩
  intro p hp
  obtain ⟨_, hp, _⟩ := hp
  change 2 ≤ p.val at hp
  have hlt := p.isLt
  refine ⟨⟨p.val - 2, by omega⟩, ?_, ?_⟩
  · intro s hs
    change 2 ≤ p.val - 2 ∧ 0 ≤ s at hs
    omega
  · intro t _
    change p.val = p.val - 2 + 2
    omega

example : ¬ ∃ T : ℕ, ∃ q ∈ twoCrashes.correct, ∀ p ∈ twoCrashes.crashed, ∀ t ≥ T,
    p ∈ splitObservers q t := by
  rintro ⟨T, q, _, hq⟩
  have h₂ : 2 = q.val + 2 := hq 2 ⟨0, by decide, by decide⟩ T le_rfl
  have h₃ : 3 = q.val + 2 := hq 3 ⟨0, by decide, by decide⟩ T le_rfl
  omega

example : ¬ (sample twoCrashes splitObservers).StrongCompleteness := by
  intro h
  obtain ⟨T, hT⟩ := h twoCrashes splitObservers ⟨rfl, rfl⟩
  have hq : (0 : Fin 4) ∈ twoCrashes.correct := fun _ hc => (by decide : ¬ 2 ≤ 0) hc.1
  have hmiss : 3 = 0 + 2 := hT 3 ⟨0, by decide, by decide⟩ 0 hq T le_rfl
  omega

private def lateCrash := thresholdCrash 2 1 1 (by decide) (by decide)

private def faultyObserver : History (Fin 2) := fun q _ => {p | q.val = 1 ∧ p.val = 0}

-- Process 1's report at tick 0 counts for weak accuracy, though it crashes at tick 1.
example : ¬ (sample lateCrash faultyObserver).WeakAccuracy := by
  intro h
  obtain ⟨p, hp, hNever⟩ := h lateCrash faultyObserver ⟨rfl, rfl⟩
  have hlt : ¬ 1 ≤ p.val := fun hle => hp 1 ⟨hle, le_rfl⟩
  exact hNever 0 1 (fun hc => Nat.not_succ_le_zero 0 hc.2) ⟨rfl, by omega⟩

-- The same observer has reports after its crash, but none count against eventual accuracy.
example : (sample lateCrash faultyObserver).EventualStrongAccuracy := by
  rintro _ _ ⟨rfl, rfl⟩
  refine ⟨0, ?_⟩
  intro _ _ _ _ q hq hs
  exact hq 1 ⟨Nat.le_of_eq hs.1.symm, le_rfl⟩

private def mutualAt (τ : ℕ) : History (Fin 2) := fun q t => {p | q.val ≠ p.val ∧ t = τ}

-- At tick 1, process 1 is already crashed. Both directions of suspicion are allowed.
example : (sample lateCrash (mutualAt 1)).StrongAccuracy := by
  rintro _ _ ⟨rfl, rfl⟩
  intro t p q hp hq h
  obtain ⟨hne, rfl⟩ := h
  have hp' : ¬ 1 ≤ p.val := fun hle => hp ⟨hle, le_rfl⟩
  have hq' : ¬ 1 ≤ q.val := fun hle => hq ⟨hle, le_rfl⟩
  omega

example : (sample lateCrash (mutualAt 1)).WeakAccuracy := by
  rintro _ _ ⟨rfl, rfl⟩
  refine ⟨0, fun _ h => Nat.not_succ_le_zero 0 h.1, ?_⟩
  intro t q hq h
  obtain ⟨hne, rfl⟩ := h
  have hlt : 1 ≤ q.val := by
    change q.val ≠ 0 at hne
    omega
  exact hq ⟨hlt, le_rfl⟩

example : ¬ (sample lateCrash (mutualAt 0)).StrongAccuracy := by
  intro h
  exact h lateCrash (mutualAt 0) ⟨rfl, rfl⟩ 0 1 0
    (fun hc => Nat.not_succ_le_zero 0 hc.2) (fun hc => Nat.not_succ_le_zero 0 hc.2)
    ⟨by decide, rfl⟩

private def noCrash := thresholdCrash 2 2 0 (by decide) (by decide)

private def alternatingTargets : History (Fin 2) := fun _ t => {p | p.val = t % 2}

-- Each tick leaves one target unsuspected, but neither correct target is safe forever.
example : ∀ t, ∃ p ∈ noCrash.correct, ∀ q, p ∉ alternatingTargets q t := by
  intro t
  refine ⟨⟨1 - t % 2, by omega⟩, ?_, ?_⟩
  · intro s hs
    change 2 ≤ 1 - t % 2 ∧ 0 ≤ s at hs
    omega
  · intro _ hs
    change 1 - t % 2 = t % 2 at hs
    omega

example : ¬ (sample noCrash alternatingTargets).EventualWeakAccuracy := by
  intro h
  obtain ⟨T, p, _, hNever⟩ := h noCrash alternatingTargets ⟨rfl, rfl⟩
  have hq : (0 : Fin 2) ∈ noCrash.correct := fun _ hc => (by decide : ¬ 2 ≤ (0 : Fin 2).val) hc.1
  have hp := p.isLt
  by_cases h₀ : p.val = T % 2
  · exact hNever T le_rfl 0 hq h₀
  · exact hNever (T + 1) (Nat.le_succ T) 0 hq (show p.val = (T + 1) % 2 by omega)

-- The two rows of Figure 1, in column order.
example (D : Detector (Fin 2)) :
    (D ∈ DetectorClass.detectors .perfect ↔ D.StrongCompleteness ∧ D.StrongAccuracy) ∧
    (D ∈ DetectorClass.detectors .strong ↔ D.StrongCompleteness ∧ D.WeakAccuracy) ∧
    (D ∈ DetectorClass.detectors .eventuallyPerfect ↔
      D.StrongCompleteness ∧ D.EventualStrongAccuracy) ∧
    (D ∈ DetectorClass.detectors .eventuallyStrong ↔
      D.StrongCompleteness ∧ D.EventualWeakAccuracy) ∧
    (D ∈ DetectorClass.detectors .q ↔ D.WeakCompleteness ∧ D.StrongAccuracy) ∧
    (D ∈ DetectorClass.detectors .weak ↔ D.WeakCompleteness ∧ D.WeakAccuracy) ∧
    (D ∈ DetectorClass.detectors .eventuallyQ ↔ D.WeakCompleteness ∧ D.EventualStrongAccuracy) ∧
    (D ∈ DetectorClass.detectors .eventuallyWeak ↔ D.WeakCompleteness ∧ D.EventualWeakAccuracy) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

end Cslib.Distributed.FailureDetector
