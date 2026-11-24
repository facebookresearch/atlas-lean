/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisorSumReciprocalConvergence

public section

namespace MathlibExt.NumberTheory.DivisorSumReciprocalConvergenceWanted

private theorem inA_iff_properDivisors (n : ℕ) :
    InA n ↔ 0 < n ∧ Nat.Pseudoperfect n ∧
      ∀ m ∈ n.properDivisors, ¬Nat.Pseudoperfect m := by
  simp [InA, Nat.mem_properDivisors, and_imp]

example : ¬InA 0 := fun h ↦ (Nat.lt_irrefl 0 h.1)

example : InA 6 := by rw [inA_iff_properDivisors]; decide

/-- The pseudoperfect divisor 6 excludes 12 from the index set. -/
example : Nat.Pseudoperfect 12 ∧ ¬InA 12 := by
  rw [inA_iff_properDivisors]
  decide

/-- A primitive pseudoperfect number can have an abundant proper divisor. -/
example : InA 350 ∧ Nat.Abundant 70 ∧ 70 ∈ Nat.properDivisors 350 := by
  refine ⟨?_, by decide +kernel⟩
  rw [inA_iff_properDivisors]
  refine ⟨by decide, ⟨by decide, {1, 5, 14, 35, 50, 70, 175}, by decide +kernel, by decide⟩, ?_⟩
  decide +kernel

example : Summable (fun n : {n : ℕ // InA n} ↦ (1 : ℝ) / (n.val : ℝ)) := conjecture_holds

end MathlibExt.NumberTheory.DivisorSumReciprocalConvergenceWanted
