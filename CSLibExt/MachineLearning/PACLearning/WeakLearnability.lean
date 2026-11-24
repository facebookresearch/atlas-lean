/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.MachineLearning.PACLearning.Defs

/-!
# Weak PAC learnability

Kearns and Valiant's weak learnability, in CSLib's PAC vocabulary: a learner need only reach some
fixed accuracy `ε < 1 / 2`, slightly better than random guessing, but at every confidence
`δ ∈ (0, 1)` (R. E. Schapire, *The strength of weak learnability*, Machine Learning 5 (1990),
197–227, Section 2). CSLib's `IsPACLearnerFor` counts examples and imposes no running time, so this
is the sample-complexity form of the notion. It matches the standard notion only over realizable
distributions: `IsPACLearnerFor` measures error above the optimum of the class, which is `0`
in the realizable case. Schapire's definition also asks for polynomial running time and
an inverse-polynomial advantage in the size parameters.

Main results:

* `IsWeakPACLearnable`: some accuracy `ε < 1 / 2` is achievable at every confidence.
* `IsPACLearnable.toIsWeakPACLearnable`: PAC learnability implies weak PAC learnability, the
  trivial direction of Schapire's Theorem 1.

The converse, the statistical form of Schapire's theorem for the realizable case, is recorded as
wanted in `WantedExt/ComputerScience/WeakLearnabilityWanted.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory
open scoped NNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Weak PAC learnability** (Kearns and Valiant's notion as stated by Schapire, *The strength of
weak learnability*, Machine Learning 5, 1990, Section 2, without the running-time requirement):
a concept class `C` is weakly PAC learnable over the distribution family `𝒟` if some accuracy
`ε ∈ (0, 1)` with `ε < 1 / 2` admits, for every confidence `δ ∈ (0, 1)`, a sample size `m` and an
`(ε, δ)`-PAC learner (`IsPACLearnerFor m ε δ C 𝒟`).

`IsPACLearnerFor` measures error above the optimum `optimalError D C`, so this matches Kearns and
Valiant's notion only when every distribution in `𝒟` is realizable (optimal error `0`), as for
`realizableFamily C`; over other distributions it is an agnostic variant. -/
def IsWeakPACLearnable (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∃ ε : Set.Ioo (0 : ℝ≥0) 1, ε.val < 1 / 2 ∧
    ∀ δ : Set.Ioo (0 : ℝ≥0) 1, ∃ m, IsPACLearnerFor m ε δ C 𝒟

/-- **PAC learnability implies weak PAC learnability**, the trivial direction of Schapire's
Theorem 1 (*The strength of weak learnability*, Machine Learning 5, 1990): take the accuracy
`ε = 1 / 4`. -/
theorem IsPACLearnable.toIsWeakPACLearnable {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsPACLearnable C 𝒟) : IsWeakPACLearnable C 𝒟 :=
  ⟨⟨1 / 4, by constructor <;> norm_num⟩, by norm_num, fun δ => h _ δ⟩

end Cslib.MachineLearning.PACLearning
