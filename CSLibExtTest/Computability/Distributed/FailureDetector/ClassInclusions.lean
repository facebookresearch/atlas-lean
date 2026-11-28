/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.FailureDetector.ClassInclusions

/-!
# Tests for inclusions of failure detector classes

These clients use named classes rather than another encoding of the three requirements.
-/

namespace Cslib.Distributed.FailureDetector.DetectorClass

private abbrev classes (n : ℕ) (k : DetectorClass) := k.detectors (Proc := Fin n)

-- Composites that weaken both completeness and accuracy.
example {n : ℕ} (hn : 0 < n) :
    classes n .perfect ⊆ classes n .eventuallyWeak ∧ classes n .strong ⊆ classes n .eventuallyWeak ∧
    classes n .eventuallyPerfect ⊆ classes n .eventuallyWeak := by
  refine ⟨?_, ?_, ?_⟩ <;> apply detectors_subset_of_requirements hn <;>
    simp [allObservers, allTargets, perpetual]

-- On two processes, a correct observer of a crash is the only correct observer.
example : classes 2 .perfect = classes 2 .q ∧ classes 2 .strong = classes 2 .weak ∧
    classes 2 .eventuallyPerfect = classes 2 .eventuallyQ ∧
    classes 2 .eventuallyStrong = classes 2 .eventuallyWeak := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Set.Subset.antisymm <;>
    apply detectors_subset_of_requirements (by decide) <;> decide

-- One process leaves exactly one class in each of the two time regimes.
example : classes 1 .strong = classes 1 .perfect ∧ classes 1 .weak = classes 1 .perfect ∧
    classes 1 .q = classes 1 .perfect ∧ classes 1 .eventuallyStrong = classes 1 .eventuallyPerfect ∧
    classes 1 .eventuallyWeak = classes 1 .eventuallyPerfect ∧
    classes 1 .eventuallyQ = classes 1 .eventuallyPerfect := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Set.Subset.antisymm <;>
    apply detectors_subset_of_requirements (by decide) <;> decide

end Cslib.Distributed.FailureDetector.DetectorClass
