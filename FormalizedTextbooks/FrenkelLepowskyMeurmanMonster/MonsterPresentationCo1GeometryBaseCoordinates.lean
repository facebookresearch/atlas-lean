/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Conway base frame has the literal binary coordinate used by the sign certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The first integral basis vector is the actual distinguished norm-eight coordinate frame. -/
theorem monsterCo1GeometryBasePoint_integral :
    leechExplicitCoordinateMap (Pi.single 0 (1 : ℤ)) = leechCoordinateFrameLattice 0 := by
  apply Subtype.ext
  change leechBasisMatrix *ᵥ (Pi.single 0 (1 : ℤ)) = leechCoordinateFrameVector 0
  decide +kernel

/-- The genuine integral basis coordinates of the actual frame are the first coordinate unit. -/
theorem monsterCo1GeometryBasePoint_integralCoordinates :
    leechExplicitCoordinates (leechCoordinateFrameLattice 0) = Pi.single 0 (1 : ℤ) := by
  rw [← monsterCo1GeometryBasePoint_integral]
  exact leechExplicitCoordinates.apply_symm_apply _

/-- The actual frame class is coordinate eleven in the actual binary hyperbolic basis. -/
theorem monsterCo1GeometryBasePoint_binary :
    monsterCo1GeometryBasePoint.val = (Pi.single 11 1 : Fin 24 → ZMod 2) := by
  rw [monsterCo1GeometryBasePoint_value, leechHyperbolicCoordinates_explicit,
    monsterCo1GeometryBasePoint_integralCoordinates]
  change leechHyperbolicInverse *ᵥ integerParity (Pi.single 0 (1 : ℤ)) = Pi.single 11 1
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
