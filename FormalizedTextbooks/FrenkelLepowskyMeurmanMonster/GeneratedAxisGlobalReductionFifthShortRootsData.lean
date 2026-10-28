/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! Seven actual norm-four representatives for the fifth-axis transition
roots. Integral basis coordinates, norms, and binary classes are kernel checked. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Root masks in the actual hyperbolic coordinate basis, not external runtime coordinates. -/
def generatedAxisGlobalFifthShortRootMask : Fin 7 → ℕ :=
  ![3, 5, 16, 106, 284, 2052, 196608]

/-- The corresponding actual binary vectors. -/
def generatedAxisGlobalFifthShortRootBinary (k : Fin 7) (i : Fin 24) : ZMod 2 :=
  if (generatedAxisGlobalFifthShortRootMask k).testBit i.val then 1 else 0

/-- Concrete physical integer representatives of the seven candidate roots. -/
def generatedAxisGlobalFifthShortRootPhysical : Fin 7 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 2, -2, 0, 0, 2, -2, 0, 0, 2, -2],
    ![0, 0, 0, 0, 0, 0, 2, -2, 0, 2, 0, -2, 2, 0, 0, 2, 0, 0, 0, 0, -2, -2, 0, 0],
    ![0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, -2, 0, -2, 0, 2, 0, 0, 2],
    ![2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalFifthShortRootCoordinates : Fin 7 → Fin 24 → ℤ :=
  ![![3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, -1, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, 0, 0, -2, 1, 1, 1, 0, 0, 0, 0],
    ![14, -3, -2, -2, -4, -3, -3, 1, -3, -1, -2, 0, -3, 1, 2, 0, -3, 1, 2, 0, 1, 1, 2, -2],
    ![-5, 2, 2, 1, 1, 0, 1, -1, 1, 1, 0, -1, 1, 0, 0, 1, 1, 0, 0, 0, -1, -1, 0, 0],
    ![-15, 3, 2, 4, 3, 3, 3, -1, 3, 3, 4, -2, 2, -1, -1, -1, 2, -1, -2, -1, 0, -1, -1, 2],
    ![6, -1, -1, -2, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0, 0, 0, -2, 1, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 12000000 in
-- Check seven complete lattice-coordinate, norm, and binary identities.
/-- Every displayed root has the exact basis coordinates, norm four, and stated binary class. -/
theorem generatedAxisGlobalFifthShortRoot_certificate : ∀ k : Fin 7,
    leechBasisMatrix *ᵥ generatedAxisGlobalFifthShortRootCoordinates k =
      generatedAxisGlobalFifthShortRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalFifthShortRootPhysical k i)^2) = 32 ∧
    leechHyperbolicInverse *ᵥ integerParity (generatedAxisGlobalFifthShortRootCoordinates k) =
      generatedAxisGlobalFifthShortRootBinary k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
