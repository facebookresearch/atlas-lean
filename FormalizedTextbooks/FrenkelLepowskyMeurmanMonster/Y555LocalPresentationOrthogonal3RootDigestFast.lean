/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A bounded exact root-set digest algorithm with the ordinary integer-digest semantics proved. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootDigest
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationExactTwoPower

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Compute the exact finite matrix root digest using checked binary exponentiation. -/
def y322Orthogonal3MatrixRootDigestFast (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3)) : ℕ :=
  ∑ i : Fin 126, y322ExactTwoPower (y322Orthogonal3VectorCode
    (matrix *ᵥ y322Orthogonal3E7RootCoordinates i))

/-- The bounded algorithm is exactly the original finite integer root-digest sum. -/
theorem y322Orthogonal3MatrixRootDigestFast_eq (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3)) :
    y322Orthogonal3MatrixRootDigestFast matrix = y322Orthogonal3MatrixRootDigest matrix := by
  simp only [y322Orthogonal3MatrixRootDigestFast, y322ExactTwoPower_eq,
    y322Orthogonal3MatrixRootDigest]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
