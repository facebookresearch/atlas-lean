/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.Boosting

/-!
# Tests for boosting weak learners

On a countable instance space with measurable singletons, weak and PAC learnability over the
realizable family coincide (both directions, with the trivial one from `WeakLearnability`). The
theorem is applied with its named hypothesis, to a one-concept class on `ℕ` that is given only as
weakly learnable with the poor accuracy `9 / 20`, and to the empty class, whose realizable family
is empty.
-/

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory
open scoped ENNReal NNReal

-- Schapire's equivalence in sample-complexity form, for the realizable family.
example {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) :
    IsWeakPACLearnable C (realizableFamily C) ↔ IsPACLearnable C (realizableFamily C) :=
  ⟨fun h => h.isPACLearnable_realizableFamily, IsPACLearnable.toIsWeakPACLearnable⟩

-- The hypothesis keeps its name `h`.
example {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {C : ConceptClass X Bool} (hw : IsWeakPACLearnable C (realizableFamily C)) :
    IsPACLearnable C (realizableFamily C) :=
  IsWeakPACLearnable.isPACLearnable_realizableFamily (h := hw)

/-- The learner that ignores its (zero) examples and outputs `c` weakly learns `{c}` with the
accuracy `9 / 20`, barely better than random guessing. -/
private theorem isWeakPACLearnable_singleton_nine_twentieths (c : ℕ → Bool) :
    IsWeakPACLearnable ({c} : ConceptClass ℕ Bool) (realizableFamily {c}) := by
  refine ⟨⟨9 / 20, by norm_num, by norm_num⟩, by norm_num, fun δ =>
    ⟨0, fun _ => c, fun D _ hD => ?_⟩⟩
  rw [optimalError_eq_zero_of_mem_realizableFamily hD, zero_add]
  obtain ⟨h, hh, he⟩ := hD
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hempty : {S : LabeledSample ℕ Bool 0 |
      (((⟨9 / 20, by norm_num, by norm_num⟩ : Set.Ioo (0 : ℝ≥0) 1).val : ℝ≥0) : ℝ≥0∞) <
        error D h} = ∅ := by
    ext S; simp [he]
  rw [hempty, measure_empty]
  exact zero_le

-- Boosting the weak learner above: the class `{c}` is PAC learnable at every accuracy.
example (c : ℕ → Bool) : IsPACLearnable ({c} : ConceptClass ℕ Bool) (realizableFamily {c}) :=
  (isWeakPACLearnable_singleton_nine_twentieths c).isPACLearnable_realizableFamily

-- The empty class has no realizable distribution, so both notions hold vacuously.
example : IsPACLearnable (∅ : ConceptClass ℕ Bool) (realizableFamily ∅) :=
  IsWeakPACLearnable.isPACLearnable_realizableFamily
    ⟨⟨1 / 4, by norm_num, by norm_num⟩, by norm_num, fun _ =>
      ⟨0, fun _ _ => false, fun D _ hD => by simp [realizableFamily] at hD⟩⟩

end Cslib.MachineLearning.PACLearning
