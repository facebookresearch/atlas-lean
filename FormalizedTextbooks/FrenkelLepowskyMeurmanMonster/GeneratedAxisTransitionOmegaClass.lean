/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFrameClass
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

/-! Identification of the source Ω class with the actual lattice coordinate frame. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The positive initial frame vector has the zeroth integer basis coordinate. -/
theorem leechFrame_zero_coordinates :
    leechExplicitCoordinates (leechCoordinateFrameLattice 0) = Pi.single 0 1 := by
  apply leechBasisMatrix_injective
  change leechBasisMatrix *ᵥ leechExplicitCoordinates (leechCoordinateFrameLattice 0) =
    leechBasisMatrix *ᵥ Pi.single 0 1
  rw [leechExplicitCoordinates_vector]
  have hb : ∀ i : Fin 24, leechBasisMatrix i 0 = leechCoordinateFrameVector 0 i := by
    decide +kernel
  ext i
  simpa [leechCoordinateFrameLattice, Matrix.mulVec, dotProduct, Pi.single_apply] using
    (hb i).symm

/-- The actual quotient frame class has the published hyperbolic Ω coordinate. -/
theorem leechFrame_zero_hyperbolic :
    leechHyperbolicCoordinates (leechReduction (leechCoordinateFrameLattice 0)) =
      Pi.single 11 1 := by
  rw [leechHyperbolicCoordinates_explicit, leechFrame_zero_coordinates]
  have hp : integerParity (Pi.single (0 : Fin 24) (1 : ℤ)) = Pi.single 0 1 := by
    ext i
    simp [integerParity, Pi.single_apply]
  rw [hp]
  have hb : ∀ i : Fin 24, leechHyperbolicInverse i 0 =
      (Pi.single 11 1 : Fin 24 → ZMod 2) i := by decide +kernel
  ext i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hb i

/-- The source Ω base is exactly the actual coordinate-frame class in the
proved lattice quotient coordinates. -/
theorem sourceOmegaQ_eq_frame_class :
    Multiplicative.toAdd (qQuotHom sourceOmegaQ) =
      leechHyperbolicCoordinates (leechReduction (leechCoordinateFrameLattice 0)) := by
  rw [leechFrame_zero_hyperbolic]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
