/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitBasisActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitBinaryCertificates

/-! The genuine binary actions of the certified original monomial isometries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every monomial packed matrix is the actual source action on the genuine lattice quotient. -/
theorem sixthFrameOrbit_monomial_binary (k : Fin 16) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (sixthFrameOrbitMonomialIsometry k) v =
      sixthFrameOrbitColumnMatrix (sixthFrameOrbitMonomialColumns k) *ᵥ v := by
  rw [leechBinaryAction_of_basis_certificate _ _ (sixthFrameOrbit_monomial_basis k),
    ← sixthFrameOrbit_binary_check k]


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
