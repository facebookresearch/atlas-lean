/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality

/-! Rational preferred-coordinate transport by the complete original short operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- All original inverse preferred coordinates and their genuine central signs. -/
def generatedAxisGlobalRationalShortOperator (f : localFiberSubgroup)
    (C : GriessShortIndex → ℚ) (r : GriessShortIndex) : ℚ :=
  let s := (griessShortPermutation f.val.2).symm r
  (generatedAxisGlobalIntSign (localShortPhase f s) : ℚ) * C s

/-- The complete rational expression equals every actual original real short coefficient. -/
theorem generatedAxisGlobalRationalShortOperator_actual (f : localFiberSubgroup)
    (C : GriessShortIndex → ℚ) :
    localShortOperator f (fun r => (C r : ℝ)) =
      fun r => (generatedAxisGlobalRationalShortOperator f C r : ℝ) := by
  funext r
  let s := (griessShortPermutation f.val.2).symm r
  have hs : griessShortPermutation f.val.2 s = r := Equiv.apply_symm_apply _ _
  rw [← hs, localShortOperator_image]
  simp only [generatedAxisGlobalRationalShortOperator,
    Equiv.symm_apply_apply, Rat.cast_mul, Rat.cast_intCast,
    generatedAxisGlobalIntSign_real]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
