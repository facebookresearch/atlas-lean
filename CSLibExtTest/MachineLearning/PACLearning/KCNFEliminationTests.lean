/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.KCNFElimination

/-!
# k-CNF elimination tests

Closed checks over two variables: from the positive examples `(1, 0)` and `(1, 1)`, elimination of
the clauses of at most one literal keeps exactly the unit clause `p₀`, which is the target; the
learner reads only the labelled sample (the negative example `(0, 1)` is ignored); and the class of
1-CNF functions over two variables is PAC learnable.
-/

namespace Cslib.MachineLearning.PACLearning.KCNF

/-- Elimination with `k = 1` recovers the conjunction `p₀` from two positive examples. -/
example : eliminate 1 [![true, false], ![true, true]] = {{((0 : Fin 2), true)}} := by
  decide

example : (eliminate 1 [![true, false], ![true, true]]).Holds ![true, false] :=
  eval_eliminate_of_mem 1 _ (by simp)

-- one-sided error: the output implies the target `p₀`, a 1-CNF satisfied by both examples
example (x : Fin 2 → Bool) (hx : (eliminate 1 [![true, false], ![true, true]]).Holds x) :
    CNF.Holds ({{((0 : Fin 2), true)}} : CNF 2) x :=
  eliminate_imp (by decide) _ (by decide) hx

-- the learner keeps the positive instances of a labelled sample and drops the negative one
example : positives (![(![true, false], true), (![false, true], false), (![true, true], true)] :
    LabeledSample (Fin 2 → Bool) Bool 3) = [![true, false], ![true, true]] := by
  decide

example : IsPACLearnable (kcnfClass 2 1 : ConceptClass (Fin 2 → Bool) Bool)
    (realizableFamily (kcnfClass 2 1 : ConceptClass (Fin 2 → Bool) Bool)) :=
  isPACLearnable_kcnfClass 2 1

end Cslib.MachineLearning.PACLearning.KCNF
