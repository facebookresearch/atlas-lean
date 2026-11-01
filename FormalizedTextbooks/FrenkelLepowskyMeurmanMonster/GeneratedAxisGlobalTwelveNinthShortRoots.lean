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

/-! The zero mask and the five short-vector roots of the Ninth-family forest are excluded
from the genuine binary Ω orbit. Each short root has an actual norm-four Leech vector,
with integral basis coordinates, norm and binary class kernel checked. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The five short root masks in the actual hyperbolic coordinate basis. -/
def generatedAxisGlobalTwelveNinthShortRootMask : Fin 5 → ℕ :=
  ![3, 16, 64, 186, 157547]

/-- The corresponding actual binary vectors. -/
def generatedAxisGlobalTwelveNinthShortRootBinary (k : Fin 5) (i : Fin 24) : ZMod 2 :=
  if (generatedAxisGlobalTwelveNinthShortRootMask k).testBit i.val then 1 else 0

/-- Concrete physical integer representatives of the five short roots. -/
def generatedAxisGlobalTwelveNinthShortRootPhysical : Fin 5 → Fin 24 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, -2, 2, 0, 0, -2, 2, 0, 0, -2, 2],
    ![0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, -2, 2, 0, 2, 0, -2, 0, -2, 2, 0],
    ![0, 0, 0, 0, 0, 2, 0, -2, 0, 2, -2, 0, -2, -2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0],
    ![0, 0, 0, -2, 0, -2, 0, 0, 2, -2, 0, 2, -2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0]]

/-- Their integral coordinates in the proved Leech lattice basis. -/
def generatedAxisGlobalTwelveNinthShortRootCoordinates : Fin 5 → Fin 24 → ℤ :=
  ![![3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, -2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-14, 3, 2, 2, 4, 3, 3, -1, 3, 1, 2, 0, 3, -1, -2, 0, 3, -1, -2, 0, -1, -1, -2, 2],
    ![2, -1, 1, -1, 0, -2, -1, 1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 1, 0, -1, 0, -1, 1, 0],
    ![1, 0, 0, 0, 0, 1, 0, -1, 0, 1, -1, 0, -1, -1, 0, 0, -1, 0, 0, 0, 1, 0, 1, 0],
    ![5, -1, -1, -2, -1, -1, 0, 0, -1, -1, -1, 1, -1, 0, 0, 0, -1, 0, 1, 0, 1, 0, 0, 0]]

set_option maxHeartbeats 12000000 in
-- Check five complete lattice-coordinate, norm, and binary identities.
/-- Every displayed root has the exact basis coordinates, norm four, and stated binary class. -/
theorem generatedAxisGlobalTwelveNinthShortRoot_certificate : ∀ k : Fin 5,
    leechBasisMatrix *ᵥ generatedAxisGlobalTwelveNinthShortRootCoordinates k =
      generatedAxisGlobalTwelveNinthShortRootPhysical k ∧
    (∑ i : Fin 24, (generatedAxisGlobalTwelveNinthShortRootPhysical k i)^2) = 32 ∧
    leechHyperbolicInverse *ᵥ integerParity (generatedAxisGlobalTwelveNinthShortRootCoordinates k) =
      generatedAxisGlobalTwelveNinthShortRootBinary k := by
  decide +kernel

/-- The five genuine integral Leech vectors in the exact proved lattice model. -/
def generatedAxisGlobalTwelveNinthShortRootLattice (k : Fin 5) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalTwelveNinthShortRootCoordinates k)

/-- Their actual physical coordinates are exactly the finite checked representatives. -/
theorem generatedAxisGlobalTwelveNinthShortRootLattice_physical (k : Fin 5) :
    (generatedAxisGlobalTwelveNinthShortRootLattice k).val =
      generatedAxisGlobalTwelveNinthShortRootPhysical k :=
  (generatedAxisGlobalTwelveNinthShortRoot_certificate k).1

/-- The actual quotient coordinates are the displayed five hyperbolic binary vectors. -/
theorem generatedAxisGlobalTwelveNinthShortRootLattice_binary (k : Fin 5) :
    leechHyperbolicCoordinates (leechReduction (generatedAxisGlobalTwelveNinthShortRootLattice k)) =
      generatedAxisGlobalTwelveNinthShortRootBinary k := by
  rw [leechHyperbolicCoordinates_explicit]
  have hc : leechExplicitCoordinates (generatedAxisGlobalTwelveNinthShortRootLattice k) =
      generatedAxisGlobalTwelveNinthShortRootCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  rw [hc]
  exact (generatedAxisGlobalTwelveNinthShortRoot_certificate k).2.2

/-- Every short root is excluded from the actual binary Ω orbit. -/
theorem generatedAxisGlobalTwelveNinthShortRoot_not_mem_orbit (k : Fin 5) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthShortRootMask k) ∉
      generatedAxisGlobalBinaryOrbit := by
  have hb : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalTwelveNinthShortRootMask k) =
        generatedAxisGlobalTwelveNinthShortRootBinary k := rfl
  rw [hb, ← generatedAxisGlobalTwelveNinthShortRootLattice_binary]
  apply generatedAxisGlobalBinary_short_excluded
  rw [generatedAxisGlobalTwelveNinthShortRootLattice_physical]
  exact (generatedAxisGlobalTwelveNinthShortRoot_certificate k).2.1

/-- The zero mask is excluded from the actual binary Ω orbit. -/
theorem generatedAxisGlobalTwelveNinthZeroRoot_not_mem_orbit :
    monsterCo1GeometryBinaryMaskDecode (n := 24) 0 ∉ generatedAxisGlobalBinaryOrbit := by
  intro hz
  exact generatedAxisGlobalBinary_ne_zero ⟨_, hz⟩ (monsterCo1GeometryBinaryMaskDecode_zero)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
