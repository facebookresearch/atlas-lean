/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.GroupTheory.ExactlyOneNoncommutator

/-! The paper's exceptional vector gives the unique failure for the concrete group. -/

namespace MathlibExt.GroupTheory.ExactlyOneNoncommutatorKourovka17Problem76Wanted

open ProductCertificate

example : exactlyOneNoncommutator := exactlyOneNoncommutator_holds

example : Nat.card G = 368640 := group_card

example : {g : G | ¬ ∃ x y : G, g = x⁻¹ * y⁻¹ * x * y} =
    {⟨(⟨0b10101, 0b11111⟩ : Vec), 1⟩} := noncommutators_eq_singleton

example : ∃ x y : G, (1 : G) = x⁻¹ * y⁻¹ * x * y := ⟨1, 1, by simp⟩

end MathlibExt.GroupTheory.ExactlyOneNoncommutatorKourovka17Problem76Wanted
