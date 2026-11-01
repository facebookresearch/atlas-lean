/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalForm

/-! Propositional application rules for the actual local tensor representation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Applying a genuine product uses the proved representation law. -/
theorem generatedAxisGlobalTensorRepresentation_mul_apply
    (f g : localFiberSubgroup) (T : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation (f * g) T =
      localTensorRepresentation f (localTensorRepresentation g T) := by
  rw [map_mul, LinearEquiv.mul_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
