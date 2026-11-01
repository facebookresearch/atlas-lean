/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! Six actual norm-four representatives for the odd-axis transition
roots. Integral basis coordinates, norms, and binary classes are kernel checked. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Root masks in the actual hyperbolic coordinate basis, not external runtime coordinates. -/
def generatedAxisGlobalOddShortRootMask : Fin 6 → ℕ :=
  ![3, 2049, 4096, 122880, 8388608, 8392710]

/-- The corresponding actual binary vectors. -/
def generatedAxisGlobalOddShortRootBinary (k : Fin 6) (i : Fin 24) : ZMod 2 :=
  if (generatedAxisGlobalOddShortRootMask k).testBit i.val then 1 else 0

/-- Concrete physical integer representatives of the six candidate roots. -/
def generatedAxisGlobalOddShortRootPhysical : Fin 6 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, -2, -2, -2, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 3, -1, -1, -1]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalOddShortRootCoordinates : Fin 6 → Fin 24 → ℤ :=
  ![![3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, -1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![12, -2, -2, -3, -3, -2, -2, 0, -3, -2, -2, 0, -2, 1, 1, 1, -2, 1, 1, 1, 2, 0, 0, -1]]

set_option maxHeartbeats 12000000 in
-- Check six complete lattice-coordinate, norm, and binary identities.
/-- Every displayed root has the exact basis coordinates, norm four, and stated binary class. -/
theorem generatedAxisGlobalOddShortRoot_certificate : ∀ k : Fin 6,
    leechBasisMatrix *ᵥ generatedAxisGlobalOddShortRootCoordinates k =
      generatedAxisGlobalOddShortRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalOddShortRootPhysical k i)^2) = 32 ∧
    leechHyperbolicInverse *ᵥ integerParity (generatedAxisGlobalOddShortRootCoordinates k) =
      generatedAxisGlobalOddShortRootBinary k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
