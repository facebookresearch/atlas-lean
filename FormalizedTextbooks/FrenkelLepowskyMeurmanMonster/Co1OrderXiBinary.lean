/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXi
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! Binary action of the actual source three-bases isometry. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The concrete three-bases action in the same hyperbolic binary coordinates as Q. -/
theorem co1Xi_binaryAction (v : Fin 24 → ZMod 2) :
    leechBinaryAction co1XiIsometry v =
      (leechHyperbolicInverse * co1XiBasisMatrix.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ v := by
  exact leechBinaryAction_of_basis_certificate co1XiIsometry co1XiBasisMatrix
    co1Xi_embedding_basis v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
