/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.RamseyFamily

/-! # Tests for the left-ideal criterion on two-element semigroups -/

namespace MetaMathlibExt.betaFamily_isLeftIdeal_iff.Tests

private theorem contains_true_isRamseyFamily : IsRamseyFamily {A : Set Bool | true ∈ A} :=
  ⟨⟨Set.univ, Set.mem_univ true⟩, id, fun _ _ hA hAB => hAB hA, fun _ _ h => h⟩

attribute [local instance] Ultrafilter.semigroup

section

local instance rightZero : Semigroup Bool where
  mul _ y := y
  mul_assoc _ _ _ := rfl

-- For x * y = y, every left translation fixes every set.
example : ∀ p : Ultrafilter Bool, ∀ q ∈ betaFamily {A : Set Bool | true ∈ A},
    p * q ∈ betaFamily {A : Set Bool | true ∈ A} := by
  apply (betaFamily_isLeftIdeal_iff contains_true_isRamseyFamily).2
  exact fun _ _ hE => ⟨true, hE, rfl⟩

end

section

local instance leftZero : Semigroup Bool where
  mul x _ := x
  mul_assoc _ _ _ := rfl

-- For x * y = x, translating {true} by false gives {false}.
example : ¬ ∀ p : Ultrafilter Bool, ∀ q ∈ betaFamily {A : Set Bool | true ∈ A},
    p * q ∈ betaFamily {A : Set Bool | true ∈ A} := by
  intro hleft
  obtain ⟨_, _, h⟩ := (betaFamily_isLeftIdeal_iff contains_true_isRamseyFamily).1 hleft
    false {true} (Set.mem_singleton true)
  exact Bool.noConfusion h

end

end MetaMathlibExt.betaFamily_isLeftIdeal_iff.Tests
