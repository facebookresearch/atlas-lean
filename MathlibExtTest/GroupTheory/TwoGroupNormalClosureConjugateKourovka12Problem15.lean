/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TwoGroupNormalClosureConjugateKourovka12Problem15

open MathlibExt.GroupTheory.TwoGroupNormalClosureConjugateKourovka12Problem15Wanted

-- Recover the counterexample, including two noncommuting elements of the derived subgroup.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup 2 G ∧
    (∀ x y : G, Subgroup.normalClosure {x} = Subgroup.normalClosure {y} → IsConj x y) ∧
    ∃ a ∈ commutator G, ∃ b ∈ commutator G, a * b ≠ b * a := by
  classical
  by_contra! h
  exact normalClosureConjDerivedAbelian_refuted fun G _ _ hp hc a ha b hb =>
    h G inferInstance inferInstance hp hc a ha b hb
