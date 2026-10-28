/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! Nine actual norm-eight representatives for the odd-axis transition
roots. Integral basis coordinates, norms, and binary classes are kernel checked. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Root masks in the actual hyperbolic coordinate basis, not external runtime coordinates. -/
def generatedAxisGlobalOddRootMask : Fin 9 → ℕ :=
  ![1, 17, 19, 258, 1106, 2048, 28672, 8388609, 8388688]

/-- The corresponding actual binary vectors. -/
def generatedAxisGlobalOddRootBinary (k : Fin 9) (i : Fin 24) : ZMod 2 :=
  if (generatedAxisGlobalOddRootMask k).testBit i.val then 1 else 0

/-- Concrete physical integer representatives of the nine candidate roots. -/
def generatedAxisGlobalOddRootPhysical : Fin 9 → Fin 24 → ℤ :=
  ![![-6, -2, -2, -2, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-2, -2, -2, -2, 4, 0, 0, 0, 2, -2, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2],
    ![0, -4, 0, 0, 0, -4, 0, 0, -2, 2, 0, 0, -2, 2, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2],
    ![-2, 2, 0, 0, 0, 4, 0, 0, 0, -4, 0, 0, -2, 2, 0, 0, 0, 2, 2, 0, 0, 2, 0, 2],
    ![0, 6, 2, 2, 0, 2, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0],
    ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
    ![3, 3, 3, 3, 1, 1, 1, 1, 3, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![-5, 3, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 3, -1, -1, -1, -1, 1, 1, -1, -1, 1, -1, 1]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalOddRootCoordinates : Fin 9 → Fin 24 → ℤ :=
  ![![1, -1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-7, 2, 1, 1, 2, 1, 1, -1, 2, 1, 0, -1, 1, -1, 0, 0, 1, -1, 0, 0, -1, -1, 0, 2],
    ![-7, 1, 2, 2, 1, 0, 2, -1, 1, 2, 1, -1, 1, 0, -1, -1, 1, -1, 0, 0, -1, -1, 0, 2],
    ![-9, 2, 2, 2, 2, 2, 2, -1, 1, 0, 2, -1, 1, 0, -1, -1, 1, 0, 0, -1, -1, 0, -1, 2],
    ![2, 1, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![-2, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![-9, 2, 1, 1, 2, 1, 2, 0, 1, 1, 2, 0, 3, -1, -1, -1, 1, 0, 0, -1, -1, 0, -1, 1]]

set_option maxHeartbeats 12000000 in
-- Check nine complete lattice-coordinate, norm, and binary identities.
/-- Every displayed root has the exact basis coordinates, norm eight, and stated binary class. -/
theorem generatedAxisGlobalOddRoot_certificate : ∀ k : Fin 9,
    leechBasisMatrix *ᵥ generatedAxisGlobalOddRootCoordinates k =
      generatedAxisGlobalOddRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalOddRootPhysical k i)^2) = 64 ∧
    leechHyperbolicInverse *ᵥ integerParity (generatedAxisGlobalOddRootCoordinates k) =
      generatedAxisGlobalOddRootBinary k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
