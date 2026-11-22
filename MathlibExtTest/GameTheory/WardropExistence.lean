/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.WardropExistence

open MathlibExt.GameTheory.SelfishRouting

/-- Pigou's network has a Wardrop flow for every nonnegative demand. -/
example (t : ℝ) (ht : 0 ≤ t) : ∃ f, pigou.IsFeasible (fun _ => t) f ∧ pigou.IsWardrop f :=
  pigou.exists_isWardrop (fun e => by
      fin_cases e
      · exact continuousOn_const
      · exact continuousOn_id)
    (fun _ => ht) (fun _ => ⟨0, rfl⟩)

/-- Without a path, a commodity with positive demand has no feasible flow, so the path
hypothesis of `exists_isWardrop` cannot be dropped. -/
example (N : RoutingInstance (Fin 1) Unit Empty) :
    ¬ ∃ f, N.IsFeasible (fun _ => 1) f := by
  rintro ⟨f, -, h⟩
  simpa using h ()

#print axioms RoutingInstance.exists_isWardrop
