/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5

open MathlibExt.GroupTheory.GroupClassesShared
open MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted

-- Unpack the negative answer into a module satisfying all the hypotheses at once.
example : ∃ (k : Type) (_ : CommRing k) (G : Type) (_ : Group G),
    (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) ∧ IsAlmostPolycyclic G ∧
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module (MonoidAlgebra k G) P),
      Module.Finite (MonoidAlgebra k G) P ∧ Module.Projective (MonoidAlgebra k G) P ∧
      (∃ x y : P, LinearIndependent (MonoidAlgebra k G) ![x, y]) ∧
      ¬ Module.Free (MonoidAlgebra k G) P := by
  classical
  simpa only [projectiveWithTwoIndependentFree, not_forall, exists_prop] using
    projectiveWithTwoIndependentFree_refuted
