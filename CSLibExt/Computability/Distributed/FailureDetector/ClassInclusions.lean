/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.FailureDetector
public import Mathlib.Data.Fintype.Fin

/-!
# Inclusions of failure detector classes

Weakening completeness, weakening accuracy from all targets to one, or weakening accuracy
from perpetual to eventual gives an inclusion of sets of detectors. Two small populations
admit further implications. With at most two processes, if one crashes there is at most one
correct observer. With one process, every target is the correct target.

These deductions concern the properties of all histories allowed by each abstract detector,
not reductions between detectors. The underlying classes are those of T. D. Chandra and
S. Toueg, *Unreliable failure detectors for reliable distributed systems*, Journal of the ACM
43(2):225–267, 1996, §§2.1–2.4, Figure 1.
-/

@[expose] public section

namespace Cslib.Distributed.FailureDetector

namespace DetectorClass

/-- Whether a Chandra–Toueg class requires strong completeness (`P`, `S` and their eventual
versions): after a common cutoff, every correct observer permanently suspects each process that
crashes. Weak completeness requires only one fixed correct observer per crashed process. -/
def allObservers : DetectorClass → Bool
  | .perfect | .strong | .eventuallyPerfect | .eventuallyStrong => true
  | _ => false

/-- Whether a Chandra–Toueg class requires accuracy for all relevant targets (`P`, `Q` and
their eventual versions), rather than one fixed correct target. All-target accuracy protects
every target still alive at the tick in the perpetual case, and every correct target from a
common cutoff onward in the eventual case. -/
def allTargets : DetectorClass → Bool
  | .perfect | .q | .eventuallyPerfect | .eventuallyQ => true
  | _ => false

/-- Whether a Chandra–Toueg class requires accuracy at every tick (`P`, `Q`, `S`, `W`), for
observers still alive at that tick. The four eventual versions require accuracy only from an
inclusive cutoff onward and only for correct observers. -/
def perpetual : DetectorClass → Bool
  | .perfect | .q | .strong | .weak => true
  | _ => false

end DetectorClass

namespace Detector

variable {Proc : Type*} [Finite Proc] {D : Detector Proc}

private theorem strongComp_weak (h : D.StrongCompleteness) : D.WeakCompleteness := by
  intro F H hH
  obtain ⟨T, hT⟩ := h F H hH
  obtain ⟨q, hq⟩ := F.exists_correct
  exact ⟨T, fun p hp => ⟨q, hq, hT p hp q hq⟩⟩

private theorem strongAcc_weak (h : D.StrongAccuracy) : D.WeakAccuracy := by
  intro F H hH
  obtain ⟨p, hp⟩ := F.exists_correct
  exact ⟨p, hp, fun t q => h F H hH t p q (hp t)⟩

private theorem strongAcc_eventual (h : D.StrongAccuracy) : D.EventualStrongAccuracy := by
  intro F H hH
  exact ⟨0, fun t _ p hp q hq => h F H hH t p q (hp t) (hq t)⟩

private theorem weakAcc_eventual (h : D.WeakAccuracy) : D.EventualWeakAccuracy := by
  intro F H hH
  obtain ⟨p, hp, hnever⟩ := h F H hH
  exact ⟨0, p, hp, fun t _ q hq => hnever t q (hq t)⟩

private theorem eventualStrongAcc_weak (h : D.EventualStrongAccuracy) : D.EventualWeakAccuracy := by
  intro F H hH
  obtain ⟨T, hT⟩ := h F H hH
  obtain ⟨p, hp⟩ := F.exists_correct
  exact ⟨T, p, hp, fun t ht => hT t ht p hp⟩

private theorem weakComp_strong_of_le_two {n : ℕ} (hn : n ≤ 2) {D : Detector (Fin n)}
    (h : D.WeakCompleteness) : D.StrongCompleteness := by
  intro F H hH
  obtain ⟨T, hT⟩ := h F H hH
  refine ⟨T, fun p hp q hq => ?_⟩
  obtain ⟨r, hr, hperm⟩ := hT p hp
  obtain ⟨t, ht⟩ := hp
  have hqp : q ≠ p := fun he => hq t (he ▸ ht)
  have hrp : r ≠ p := fun he => hr t (he ▸ ht)
  have he : q = r := by omega
  exact he ▸ hperm

private theorem weakAcc_strong_of_subsingleton [Subsingleton Proc] (h : D.WeakAccuracy) :
    D.StrongAccuracy := by
  intro F H hH t p q _ hq
  obtain ⟨r, _, hnever⟩ := h F H hH
  exact Subsingleton.elim r p ▸ hnever t q hq

private theorem eventualWeakAcc_strong_of_subsingleton [Subsingleton Proc]
    (h : D.EventualWeakAccuracy) : D.EventualStrongAccuracy := by
  intro F H hH
  obtain ⟨T, r, _, hnever⟩ := h F H hH
  exact ⟨T, fun t ht p _ q hq => Subsingleton.elim r p ▸ hnever t ht q hq⟩

end Detector

namespace DetectorClass

-- List also the weaker properties implied by each defining pair. This lets the three
-- requirements be compared separately, without case-splitting on pairs of class names.
private theorem mem_iff_requirements {Proc : Type*} [Finite Proc] {D : Detector Proc}
    (k : DetectorClass) : D ∈ k.detectors ↔
      D.WeakCompleteness ∧ (k.allObservers → D.StrongCompleteness) ∧
      D.EventualWeakAccuracy ∧ (k.allTargets → D.EventualStrongAccuracy) ∧
      (k.perpetual → D.WeakAccuracy) ∧ (k.allTargets → k.perpetual → D.StrongAccuracy) := by
  have hc := @Detector.strongComp_weak Proc _ D
  have hw := @Detector.strongAcc_weak Proc _ D
  have he := @Detector.strongAcc_eventual Proc _ D
  have hwe := @Detector.weakAcc_eventual Proc _ D
  have hew := @Detector.eventualStrongAcc_weak Proc _ D
  cases k <;> simp [detectors, allObservers, allTargets, perpetual] <;> tauto

/-- On a positive population of `n` processes, the set of detectors of class `a` is included
in that of `b` if `a` meets the requirements of `b`: strong completeness when required and
`n ≥ 3`, all-target accuracy when required and `n ≥ 2`, and perpetual accuracy whenever
required. Below the respective thresholds the observer or target distinction disappears. -/
theorem detectors_subset_of_requirements {n : ℕ} (hn : 0 < n) {a b : DetectorClass}
    (hc : 3 ≤ n → b.allObservers → a.allObservers) (ha : 2 ≤ n → b.allTargets → a.allTargets)
    (ht : b.perpetual → a.perpetual) : a.detectors (Proc := Fin n) ⊆ b.detectors := by
  intro D hD
  obtain ⟨hw, hs, hew, hes, hpw, hps⟩ := (mem_iff_requirements a).mp hD
  apply (mem_iff_requirements b).mpr
  refine ⟨hw, fun hb => ?_, hew, fun hb => ?_, fun hb => hpw (ht hb), fun hb htime => ?_⟩
  · by_cases h : 3 ≤ n
    · exact hs (hc h hb)
    · exact Detector.weakComp_strong_of_le_two (by omega) hw
  · by_cases h : 2 ≤ n
    · exact hes (ha h hb)
    · obtain rfl : n = 1 := by omega
      exact Detector.eventualWeakAcc_strong_of_subsingleton hew
  · by_cases h : 2 ≤ n
    · exact hps (ha h hb) (ht htime)
    · obtain rfl : n = 1 := by omega
      exact Detector.weakAcc_strong_of_subsingleton (hpw (ht htime))

end DetectorClass

end Cslib.Distributed.FailureDetector
