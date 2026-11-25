/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.CorrelationInequalities.ReimerInequality

/-! # Tests for Reimer's inequality -/

open StatMech MathlibExt.Probability.ReimerInequalityWanted

-- With no coordinates, the weight hypotheses quantify over the empty type.
example (φ : Fin 0 → Bool → ℝ) (A B : Set (ConfigSpace (Fin 0))) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  reimer_inequality 0 φ (fun i => i.elim0) (fun i => i.elim0) A B

-- A nonmonotone event with a competing witness, under a law with a deterministic bit.
private noncomputable def weight (i : Fin 4) (b : Bool) : ℝ :=
  if i = 3 then (if b then 0 else 1) else 1 / 2

example :
    wprob weight (disjointOccurrence
      {ω | ω 0 ≠ ω 1 ∨ ω 2 = true} {ω | ω 2 = true}) ≤
    wprob weight {ω | ω 0 ≠ ω 1 ∨ ω 2 = true} * wprob weight {ω | ω 2 = true} := by
  apply reimer_inequality
  · intro i b
    by_cases hi : i = 3 <;> cases b <;> norm_num [weight, hi]
  · intro i
    by_cases hi : i = 3 <;> norm_num [weight, hi]
