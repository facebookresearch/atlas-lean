/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.Occam
public import CSLibExt.MachineLearning.PACLearning.WeakLearnability

/-!
# Tests for weak PAC learnability

A one-concept class is PAC learnable over its realizable distributions by the learner that always
outputs the concept, hence weakly PAC learnable: the notion is satisfiable.
-/

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory

theorem isPACLearnable_singleton {X : Type*} [MeasurableSpace X] (c : X → Bool) :
    IsPACLearnable ({c} : ConceptClass X Bool) (realizableFamily {c}) := by
  intro ε δ
  refine ⟨0, fun _ => c, fun D _ hD => ?_⟩
  obtain ⟨h, hh, he⟩ := hD
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hopt : optimalError D ({h} : ConceptClass X Bool) = 0 := by
    simp [optimalError, he]
  have : {S : LabeledSample X Bool 0 |
      optimalError D ({h} : ConceptClass X Bool) + ↑ε.val < error D h} = ∅ := by
    ext S; simp [hopt, he]
  rw [this, measure_empty]
  exact zero_le

example {X : Type*} [MeasurableSpace X] (c : X → Bool) :
    IsWeakPACLearnable ({c} : ConceptClass X Bool) (realizableFamily {c}) :=
  (isPACLearnable_singleton c).toIsWeakPACLearnable

#print axioms IsPACLearnable.toIsWeakPACLearnable

end Cslib.MachineLearning.PACLearning
