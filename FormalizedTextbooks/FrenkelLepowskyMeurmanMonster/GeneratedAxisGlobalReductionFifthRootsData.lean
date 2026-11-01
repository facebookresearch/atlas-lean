/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! Fourteen actual norm-eight representatives for the fifth-axis transition
roots. Integral basis coordinates, norms, and binary classes are kernel checked. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Root masks in the actual hyperbolic coordinate basis, not external runtime coordinates. -/
def generatedAxisGlobalFifthRootMask : Fin 14 → ℕ :=
  ![1, 4, 17, 22, 96, 97, 176, 177, 272, 273, 274, 2048, 2051, 196612]

/-- The corresponding actual binary vectors. -/
def generatedAxisGlobalFifthRootBinary (k : Fin 14) (i : Fin 24) : ZMod 2 :=
  if (generatedAxisGlobalFifthRootMask k).testBit i.val then 1 else 0

/-- Concrete physical integer representatives of the fourteen candidate roots. -/
def generatedAxisGlobalFifthRootPhysical : Fin 14 → Fin 24 → ℤ :=
  ![![-6, -2, -2, -2, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-6, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0],
    ![-2, -2, -2, -2, 4, 0, 0, 0, 2, -2, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2],
    ![0, 0, 0, -4, 0, 0, -4, 0, 0, 0, 2, 2, -2, 2, 0, 0, -2, 2, 0, 0, 0, 0, 2, 2],
    ![2, 2, 2, -2, 2, 2, 0, 0, 2, 0, 2, 0, 2, 0, 0, 2, -2, 2, 2, 2, 2, 2, 0, 0],
    ![-2, 2, 2, -2, 0, 0, 2, 2, 2, 0, -2, 0, 0, 2, 2, 0, -4, 0, 0, 0, 0, 0, 2, 2],
    ![2, -2, 2, 2, 2, 0, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, -2, 2, 2, 2, 2, 0, 2, 0],
    ![-2, 2, 2, -2, 0, 2, 0, 2, -2, 0, 0, 2, 0, 0, -2, -2, 0, 0, 4, 0, 0, 2, 0, 2],
    ![0, 0, 2, 2, 0, -4, 0, 0, 0, 0, 2, 2, 4, 0, 0, 0, 0, 2, 0, 2, 0, 2, 2, 0],
    ![0, 0, -2, 2, -2, 2, -2, -2, 0, 0, 2, -2, 2, -2, 2, 2, 2, 0, 2, 0, -2, 0, 0, -2],
    ![2, -2, 0, 0, 0, 4, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0],
    ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-2, 2, 2, 2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 2, -2, 2, 2, 2],
    ![2, -2, -2, -2, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalFifthRootCoordinates : Fin 14 → Fin 24 → ℤ :=
  ![![1, -1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![5, -1, -1, -2, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0, 0, 0, -2, 1, 1, 1, 0, 0, 0, 0],
    ![-7, 2, 1, 1, 2, 1, 1, -1, 2, 1, 0, -1, 1, -1, 0, 0, 1, -1, 0, 0, -1, -1, 0, 2],
    ![-7, 1, 2, 1, 2, 1, 1, -1, 1, 1, 2, 0, 1, 0, -1, -1, 1, 0, -1, -1, -1, -1, 0, 2],
    ![8, -1, -1, -3, -1, -1, -2, 0, -1, -2, -1, 0, -1, 0, 0, 1, -3, 1, 1, 1, 1, 1, 0, 0],
    ![-9, 2, 2, 2, 1, 1, 2, 0, 2, 2, 1, -1, 1, 0, 0, -1, 1, -1, -1, -1, -1, -1, 0, 2],
    ![10, -3, -1, -2, -2, -2, -1, 0, -2, -2, -2, 1, -1, 1, 0, 0, -3, 1, 1, 1, 1, 0, 1, 0],
    ![-11, 2, 2, 1, 2, 2, 3, 0, 1, 2, 2, 0, 3, -1, -2, -2, 1, -1, 1, -1, -1, 0, -1, 2],
    ![7, -2, -1, -1, -1, -2, -2, 0, -1, -2, -1, 1, 0, 0, 0, 0, -2, 1, 0, 1, 0, 1, 1, 0],
    ![12, -1, -2, -2, -3, -2, -4, 0, -2, -2, -3, 0, -2, 0, 2, 2, -2, 1, 2, 1, 0, 1, 1, -2],
    ![11, -3, -2, -2, -2, -1, -3, 0, -2, -3, -2, 1, -2, 1, 1, 1, -2, 1, 0, 1, 0, 1, 1, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-8, 2, 2, 2, 1, 1, 1, 0, 2, 1, 1, -1, 2, -1, -1, -1, 0, 0, 0, 0, -2, 0, 0, 2],
    ![5, -1, -1, -2, -1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, -2, 1, 1, 1, 0, 0, 0, 0]]

set_option maxHeartbeats 12000000 in
-- Check fourteen complete lattice-coordinate, norm, and binary identities.
/-- Every displayed root has the exact basis coordinates, norm eight, and stated binary class. -/
theorem generatedAxisGlobalFifthRoot_certificate : ∀ k : Fin 14,
    leechBasisMatrix *ᵥ generatedAxisGlobalFifthRootCoordinates k =
      generatedAxisGlobalFifthRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalFifthRootPhysical k i)^2) = 64 ∧
    leechHyperbolicInverse *ᵥ integerParity (generatedAxisGlobalFifthRootCoordinates k) =
      generatedAxisGlobalFifthRootBinary k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
