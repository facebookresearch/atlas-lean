/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! The physical matrix Frobenius norm is a genuine local-orbit invariant.
It can distinguish two already established full-vector orbit alternatives. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual physical matrix squared norm in the original Conway coordinate model. -/
def generatedAxisGlobalMatrixNorm (x : GriessSpace) : ℝ :=
  conwayMatrixForm (griessConwayEncode x).1 (griessConwayEncode x).1

/-- Every actual local group element preserves the complete matrix constituent pairing. -/
theorem generatedAxisGlobalMatrixPairing_local (h : H) (x y : GriessSpace) :
    conwayMatrixForm (griessConwayEncode (rhoLocal h x)).1
      (griessConwayEncode (rhoLocal h y)).1 =
    conwayMatrixForm (griessConwayEncode x).1 (griessConwayEncode y).1 := by
  refine Quotient.inductionOn h ?_
  intro f
  change conwayMatrixForm (griessConwayEncode (localGriessRepresentation f x)).1
    (griessConwayEncode (localGriessRepresentation f y)).1 = _
  rw [localGriessRepresentation_encode, localGriessRepresentation_encode]
  exact conwayMatrixAction_form f.val.2 _ _

/-- The full physical matrix squared norm is constant on each genuine local orbit. -/
theorem generatedAxisGlobalMatrixNorm_local (h : H) (x : GriessSpace) :
    generatedAxisGlobalMatrixNorm (rhoLocal h x) = generatedAxisGlobalMatrixNorm x :=
  generatedAxisGlobalMatrixPairing_local h x x

/-- Unequal actual matrix norms exclude a full-vector local orbit equality. -/
theorem generatedAxisGlobalMatrixNorm_ne_local {x y : GriessSpace}
    (hxy : generatedAxisGlobalMatrixNorm x ≠ generatedAxisGlobalMatrixNorm y) :
    ¬∃ h : H, x = rhoLocal h y := by
  rintro ⟨h, rfl⟩
  exact hxy (generatedAxisGlobalMatrixNorm_local h y)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
