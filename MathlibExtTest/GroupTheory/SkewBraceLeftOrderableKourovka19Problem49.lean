/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.GroupTheory.SkewBraceLeftOrderableKourovka19Problem49

/-! # Tests for Nasybullov's skew brace on the integers -/

namespace MathlibExtTest.GroupTheory.SkewBraceLeftOrderableKourovka19Problem49

open MathlibExt.GroupTheory.SkewBraceLeftOrderableKourovka19Problem49Wanted
open Multiplicative (ofAdd)

private theorem exactSource :
    ¬ ∀ (B : Type) [AddGroup B] [Group B],
      (∀ a b c : B, a * (b + c) = a * b - a + a * c) →
      (∃ r : B → B → Prop, IsStrictTotalOrder B r ∧ ∀ a b c : B, r b c → r (a * b) (a * c)) →
      ∃ r : B → B → Prop, IsStrictTotalOrder B r ∧ ∀ a b c : B, r b c → r (a + b) (a + c) :=
  skewBraceAdditiveLeftOrderable_refuted

attribute [local instance] braceAddGroup

-- Odd first inputs subtract the second input. Even first inputs add it.
example : ofAdd (-3 : ℤ) + ofAdd 2 = ofAdd (-5) := rfl
example : ofAdd (-4 : ℤ) + ofAdd 2 = ofAdd (-2) := rfl

-- The same inputs give zero under twisted addition and two under multiplication.
example : ofAdd (1 : ℤ) + ofAdd 1 = 0 ∧ ofAdd (1 : ℤ) * ofAdd 1 = ofAdd 2 :=
  ⟨rfl, rfl⟩

end MathlibExtTest.GroupTheory.SkewBraceLeftOrderableKourovka19Problem49
