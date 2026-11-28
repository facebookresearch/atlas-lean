/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5

/-! # Regression test for the negative answer to Kourovka Notebook Problem 11.5 -/

open MathlibExt.GroupTheory.GroupClassesShared (IsAlmostPolycyclic)
open MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted

-- Check the public refutation against the quantified statement, not the implementation's witness.
example : ¬ (∀ (k : Type) [CommRing k] (G : Type) [Group G],
    (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) → IsAlmostPolycyclic G →
    ∀ (P : Type) [AddCommGroup P] [Module (MonoidAlgebra k G) P],
      Module.Finite (MonoidAlgebra k G) P → Module.Projective (MonoidAlgebra k G) P →
      (∃ x y : P, LinearIndependent (MonoidAlgebra k G) ![x, y]) →
      Module.Free (MonoidAlgebra k G) P) :=
  projectiveWithTwoIndependentFree_refuted
