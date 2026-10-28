/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQPhaseWitness

/-! The actual physical tensor columns identify every genuine extraspecial operator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Equality on all actual physical tensors identifies the actual extraspecial group element. -/
theorem generatedAxisGlobalTensor_Q_injective (q r : Q)
    (h : ∀ T : SpinIndex → Fin 24 → ℝ,
      localTensorRepresentation (localFiberIncl q) T =
        localTensorRepresentation (localFiberIncl r) T) : q = r := by
  apply spinRepresentation_injective
  apply LinearEquiv.ext
  intro x
  funext t
  have ht := congrArg (fun T : SpinIndex → Fin 24 → ℝ => T t 0) (h (fun t _ => x t))
  simp only [localTensorRepresentation_q] at ht
  exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
