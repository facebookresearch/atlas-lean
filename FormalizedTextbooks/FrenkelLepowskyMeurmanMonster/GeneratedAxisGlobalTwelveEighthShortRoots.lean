/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! The zero mask and the 14 short-vector roots of the Eighth-family forest are excluded from the
genuine binary Ω orbit. Each short root has an actual norm-four Leech vector, with integral
basis coordinates, norm and binary class kernel checked. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The 14 short root masks in the actual hyperbolic coordinate basis. -/
def generatedAxisGlobalTwelveEighthShortRootMask : Fin 14 → ℕ :=
  ![3, 5, 7, 10, 252, 432, 4096, 16384, 32768, 49152, 122880, 8388608, 8392710, 8392716]

/-- The corresponding actual binary vectors. -/
def generatedAxisGlobalTwelveEighthShortRootBinary (k : Fin 14) (i : Fin 24) : ZMod 2 :=
  if (generatedAxisGlobalTwelveEighthShortRootMask k).testBit i.val then 1 else 0

/-- Concrete physical integer representatives of the short roots. -/
def generatedAxisGlobalTwelveEighthShortRootPhysical : Fin 14 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, -2, 2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, -2, 2, 2, 2],
    ![0, 0, 0, 0, 0, 2, -2, 0, 0, -2, 2, 0, 0, 0, 0, 0, -2, 0, -2, 0, 2, 2, 0, 0],
    ![0, 0, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -4, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -3, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -3, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalTwelveEighthShortRootCoordinates : Fin 14 → Fin 24 → ℤ :=
  ![![3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, -1, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0, 0, 0, -2, 1, 1, 1, 0, 0, 0, 0],
    ![-14, 3, 3, 4, 4, 2, 2, -2, 3, 2, 2, -1, 2, -1, -1, -1, 2, -1, -1, -1, -2, 0, 0, 2],
    ![-17, 3, 3, 4, 4, 3, 3, -1, 4, 3, 3, -1, 4, -2, -2, -2, 2, -1, -1, -1, -2, 0, 0, 2],
    ![2, -1, -1, 0, 0, 1, -1, 0, 0, -1, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 1, 1, 0, 0],
    ![1, 0, 0, -1, -1, -1, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    ![-4, 1, 1, 1, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0],
    ![-4, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![-12, 2, 2, 3, 3, 2, 2, 0, 3, 2, 2, 0, 2, -1, -1, -1, 2, -1, -1, -1, -2, 0, 0, 1],
    ![5, -1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, -1]]

set_option maxHeartbeats 40000000 in
-- Check the complete lattice-coordinate, norm, and binary identities.
/-- Every displayed root has the exact basis coordinates, norm four, and stated binary class. -/
theorem generatedAxisGlobalTwelveEighthShortRoot_certificate : ∀ k : Fin 14,
    leechBasisMatrix *ᵥ generatedAxisGlobalTwelveEighthShortRootCoordinates k =
      generatedAxisGlobalTwelveEighthShortRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalTwelveEighthShortRootPhysical k i)^2) = 32 ∧
    leechHyperbolicInverse *ᵥ
        integerParity (generatedAxisGlobalTwelveEighthShortRootCoordinates k) =
      generatedAxisGlobalTwelveEighthShortRootBinary k := by
  decide +kernel

/-- The genuine integral Leech vectors in the exact proved lattice model. -/
def generatedAxisGlobalTwelveEighthShortRootLattice (k : Fin 14) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalTwelveEighthShortRootCoordinates k)

/-- Their actual physical coordinates are exactly the finite checked representatives. -/
theorem generatedAxisGlobalTwelveEighthShortRootLattice_physical (k : Fin 14) :
    (generatedAxisGlobalTwelveEighthShortRootLattice k).val =
      generatedAxisGlobalTwelveEighthShortRootPhysical k :=
  (generatedAxisGlobalTwelveEighthShortRoot_certificate k).1

/-- The actual quotient coordinates are the displayed hyperbolic binary vectors. -/
theorem generatedAxisGlobalTwelveEighthShortRootLattice_binary (k : Fin 14) :
    leechHyperbolicCoordinates
        (leechReduction (generatedAxisGlobalTwelveEighthShortRootLattice k)) =
      generatedAxisGlobalTwelveEighthShortRootBinary k := by
  rw [leechHyperbolicCoordinates_explicit]
  have hc : leechExplicitCoordinates (generatedAxisGlobalTwelveEighthShortRootLattice k) =
      generatedAxisGlobalTwelveEighthShortRootCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  rw [hc]
  exact (generatedAxisGlobalTwelveEighthShortRoot_certificate k).2.2

/-- Every short root is excluded from the actual binary Ω orbit. -/
theorem generatedAxisGlobalTwelveEighthShortRoot_not_mem_orbit (k : Fin 14) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveEighthShortRootMask k) ∉
      generatedAxisGlobalBinaryOrbit := by
  have hb : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveEighthShortRootMask k) =
        generatedAxisGlobalTwelveEighthShortRootBinary k := rfl
  rw [hb, ← generatedAxisGlobalTwelveEighthShortRootLattice_binary]
  apply generatedAxisGlobalBinary_short_excluded
  rw [generatedAxisGlobalTwelveEighthShortRootLattice_physical]
  exact (generatedAxisGlobalTwelveEighthShortRoot_certificate k).2.1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
