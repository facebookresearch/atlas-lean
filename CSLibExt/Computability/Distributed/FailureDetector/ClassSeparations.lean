/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.FailureDetector.ClassInclusions

/-!
# Separations of failure detector classes

On `Fin n` with `n > 0`, three examples distinguish all the requirements that do not
collapse. Suspecting everyone initially separates perpetual from eventual accuracy. With a
second correct process one target can be permanently suspected while another is never
suspected. With a crash and two correct observers, only one observer need suspect the
crashed process. Each example is a detector admitting a single pattern-history pair.

The model and the eight classes are from T. D. Chandra and S. Toueg, *Unreliable failure
detectors for reliable distributed systems*, Journal of the ACM 43(2):225–267, 1996,
§§2.1–2.4, Figure 1. The strict inclusions and their population thresholds below follow
from those definitions; they concern sets of detectors, not implementability.
-/

public section

namespace Cslib.Distributed.FailureDetector.DetectorClass

private def supported {P : Type*} [Finite P] (F : FailurePattern P) (H : History P) : Detector P :=
  fun F' => {H' | F' = F ∧ H' = H}

private def noCrash {n : ℕ} (hn : 0 < n) : FailurePattern (Fin n) where
  crashedBy _ := ∅
  mono := monotone_const
  exists_correct := ⟨⟨0, hn⟩, fun _ => Set.notMem_empty _⟩

private theorem noCrash_complete {n : ℕ} (hn : 0 < n) (H : History (Fin n)) :
    (supported (noCrash hn) H).StrongCompleteness := by
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨0, fun _ ⟨_, h⟩ => h.elim⟩

-- Every target is suspected at time zero. A mistake about just one target would not
-- rule out perpetual weak accuracy when a second correct target is never suspected.
private theorem not_perpetual_subset {n : ℕ} (hn : 0 < n) :
    ¬ eventuallyPerfect.detectors (Proc := Fin n) ⊆ weak.detectors := by
  let H : History (Fin n) := fun _ t => {_p | t = 0}
  let F := noCrash hn
  have hE : (supported F H).EventualStrongAccuracy := by
    rintro _ _ ⟨rfl, rfl⟩
    refine ⟨1, fun t ht _ _ _ _ => ?_⟩
    exact Nat.ne_of_gt ht
  intro h
  have hW := h (show supported F H ∈ eventuallyPerfect.detectors from ⟨noCrash_complete hn H, hE⟩)
  obtain ⟨p, _, hsafe⟩ := hW.2 F H ⟨rfl, rfl⟩
  exact hsafe 0 p (Set.notMem_empty _) rfl

-- All observers always suspect 0. Target 1 is a fixed correct witness for weak accuracy.
private theorem not_allTargets_subset {n : ℕ} (hn : 2 ≤ n) :
    ¬ strong.detectors (Proc := Fin n) ⊆ eventuallyQ.detectors := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, hn⟩
  let F := noCrash (n := n) (by omega)
  let H : History (Fin n) := fun _ _ => {z}
  have hoz : o ≠ z := fun he => (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val he)
  have hW : (supported F H).WeakAccuracy := by
    rintro _ _ ⟨rfl, rfl⟩
    exact ⟨o, fun _ => Set.notMem_empty _, fun _ _ _ => hoz⟩
  intro h
  have hQ := h (show supported F H ∈ strong.detectors from ⟨noCrash_complete _ H, hW⟩)
  obtain ⟨T, hT⟩ := hQ.2 F H ⟨rfl, rfl⟩
  have hz : z ∈ F.correct := fun _ => Set.notMem_empty _
  exact hT T le_rfl z hz z hz rfl

-- Only observer 0 reports the crash of 2; observer 1 is correct and never reports it.
private theorem not_allObservers_subset {n : ℕ} (hn : 3 ≤ n) :
    ¬ q.detectors (Proc := Fin n) ⊆ eventuallyStrong.detectors := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, hn⟩
  have hzc : z ≠ c := fun he => (by decide : (0 : ℕ) ≠ 2) (congrArg Fin.val he)
  have hoc : o ≠ c := fun he => (by decide : (1 : ℕ) ≠ 2) (congrArg Fin.val he)
  have hoz : o ≠ z := fun he => (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val he)
  let F : FailurePattern (Fin n) := {
    crashedBy := fun _ => {c}
    mono := monotone_const
    exists_correct := ⟨z, fun _ => hzc⟩ }
  let H : History (Fin n) := fun obs _ => {p | obs = z ∧ p = c}
  have hW : (supported F H).WeakCompleteness := by
    rintro _ _ ⟨rfl, rfl⟩
    exact ⟨0, fun _ ⟨_, hp⟩ => ⟨z, fun _ => hzc, fun _ _ => ⟨rfl, hp⟩⟩⟩
  have hA : (supported F H).StrongAccuracy := by
    rintro _ _ ⟨rfl, rfl⟩
    exact fun _ _ _ hp _ hs => hp hs.2
  intro h
  have hS := h (show supported F H ∈ q.detectors from ⟨hW, hA⟩)
  obtain ⟨T, hT⟩ := hS.1 F H ⟨rfl, rfl⟩
  exact hoz (hT c ⟨0, rfl⟩ o (fun _ => hoc) T le_rfl).1

/-- For `n > 0`, the set of Chandra–Toueg detectors in class `a` on `Fin n` is included in
class `b` exactly when every requirement of `b` is also imposed by `a`, counting strong
completeness only for `n ≥ 3`, all-target accuracy only for `n ≥ 2`, and perpetual accuracy
for every `n`. Thus all twelve one-requirement weakenings are proper for `n ≥ 3`; at two
processes only the four completeness inclusions collapse, and at one process only the strict
inclusion from perpetual to eventual accuracy remains. -/
theorem detectors_subset_iff {n : ℕ} (hn : 0 < n) {a b : DetectorClass} :
    a.detectors (Proc := Fin n) ⊆ b.detectors ↔
      (3 ≤ n → b.allObservers → a.allObservers) ∧
      (2 ≤ n → b.allTargets → a.allTargets) ∧ (b.perpetual → a.perpetual) := by
  refine ⟨fun h => ?_, fun ⟨hc, ha, ht⟩ => detectors_subset_of_requirements hn hc ha ht⟩
  refine ⟨fun h₃ hb => ?_, fun h₂ hb => ?_, fun hb => ?_⟩
  · by_contra ha
    apply not_allObservers_subset h₃
    calc
      q.detectors (Proc := Fin n) ⊆ a.detectors := ?_
      _ ⊆ b.detectors := h
      _ ⊆ eventuallyStrong.detectors := ?_
    all_goals
      apply detectors_subset_of_requirements hn <;> simp_all [allObservers, allTargets, perpetual]
  · by_contra ha
    apply not_allTargets_subset h₂
    calc
      strong.detectors (Proc := Fin n) ⊆ a.detectors := ?_
      _ ⊆ b.detectors := h
      _ ⊆ eventuallyQ.detectors := ?_
    all_goals
      apply detectors_subset_of_requirements hn <;> simp_all [allObservers, allTargets, perpetual]
  · by_contra ha
    apply not_perpetual_subset hn
    calc
      eventuallyPerfect.detectors (Proc := Fin n) ⊆ a.detectors := ?_
      _ ⊆ b.detectors := h
      _ ⊆ weak.detectors := ?_
    all_goals
      apply detectors_subset_of_requirements hn <;> simp_all [allObservers, allTargets, perpetual]

end Cslib.Distributed.FailureDetector.DetectorClass
