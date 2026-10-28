/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- An actual norm-eight lattice representative of Norton's four-point cocode. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightReduction
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Integral basis coordinates of the norm-eight representative. -/
def monsterNortonFourPointLatticeCoordinates : Fin 24 → ℤ :=
  ![2,0,0,-1,0,-1,0,0,0,0,-1,0,-1,0,0,2,0,0,0,0,0,0,0,0]

/-- The vector is constructed inside the actual integral Leech lattice by its proved basis. -/
noncomputable def monsterNortonFourPointLattice : leechIntegral :=
  leechExplicitCoordinateMap monsterNortonFourPointLatticeCoordinates

/-- Its physical integer coordinates have four entries equal to four. -/
theorem monsterNortonFourPointLattice_vector :
    monsterNortonFourPointLattice.val =
      ![4,0,0,0,0,0,4,0,0,4,0,0,0,0,0,4,0,0,0,0,0,0,0,0] := by
  change leechBasisMatrix *ᵥ monsterNortonFourPointLatticeCoordinates = _
  decide +kernel

/-- Its coordinates in the genuine integral lattice basis are the displayed integers. -/
theorem monsterNortonFourPointLattice_coordinates :
    leechExplicitCoordinates monsterNortonFourPointLattice =
      monsterNortonFourPointLatticeCoordinates := by
  change leechExplicitCoordinates
    (leechExplicitCoordinates.symm monsterNortonFourPointLatticeCoordinates) = _
  exact leechExplicitCoordinates.apply_symm_apply _

/-- The actual unscaled square norm is sixty-four, hence the Leech norm is eight. -/
theorem monsterNortonFourPointLattice_squareSum :
    leechSquareSum monsterNortonFourPointLattice.val = 64 := by
  rw [monsterNortonFourPointLattice_vector]
  decide +kernel

/-- The four-point cocode is exactly the binary class of this actual norm-eight vector. -/
theorem monsterNortonFourPointLattice_binary :
    Multiplicative.toAdd (qQuotHom (sourceQCocode (golayLabelCoefficients 924))) =
      leechHyperbolicCoordinates (leechReduction monsterNortonFourPointLattice) := by
  rw [leechHyperbolicCoordinates_explicit, monsterNortonFourPointLattice_coordinates]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
