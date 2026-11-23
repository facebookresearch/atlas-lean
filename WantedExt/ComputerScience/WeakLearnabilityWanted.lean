/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.PACLearning.Occam
public import CSLibExt.MachineLearning.PACLearning.WeakLearnability

/-!
# Weak learnability implies PAC learnability (wanted)

R. E. Schapire, *The strength of weak learnability*, Machine Learning 5 (1990), 197–227,
Theorem 1: a concept class is weakly learnable if and only if it is strongly learnable. Schapire's
models are polynomial-time and representation-independent; the statement below is the
sample-complexity form in CSLib's vocabulary, for binary labels in the realizable case, on a
countable instance space with measurable singletons (Schapire also works with discrete instance
spaces, Section 2). The trivial direction is `IsPACLearnable.toIsWeakPACLearnable`.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

/-- **Weak learnability implies PAC learnability** (the sample-complexity form of Schapire's
Theorem 1, *The strength of weak learnability*, Machine Learning 5, 1990, whose proof boosts a weak
learner by majority votes over filtered distributions): on a countable instance space with
measurable singletons, a class `C` of binary hypotheses that is weakly PAC learnable over its
realizable distributions is PAC learnable over them. -/
public theorem_wanted IsWeakPACLearnable.isPACLearnable_realizableFamily {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] {C : ConceptClass X Bool}
    (h : IsWeakPACLearnable C (realizableFamily C)) : IsPACLearnable C (realizableFamily C)

end Cslib.MachineLearning.PACLearning
