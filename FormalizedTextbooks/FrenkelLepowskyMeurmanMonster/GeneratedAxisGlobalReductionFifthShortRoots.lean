/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthShortRootsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes

/-! The seven short-vector roots cannot occur in the genuine binary Ω orbit.
The exclusion uses actual lattice norms and the proved minimum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The seven genuine integral Leech vectors in the exact proved lattice model. -/
def generatedAxisGlobalFifthShortRootLattice (k : Fin 7) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalFifthShortRootCoordinates k)

/-- Their actual physical coordinates are exactly the finite checked representatives. -/
theorem generatedAxisGlobalFifthShortRootLattice_physical (k : Fin 7) :
    (generatedAxisGlobalFifthShortRootLattice k).val =
      generatedAxisGlobalFifthShortRootPhysical k :=
  (generatedAxisGlobalFifthShortRoot_certificate k).1

/-- Every candidate root has genuine Leech norm four. -/
theorem generatedAxisGlobalFifthShortRootLattice_norm (k : Fin 7) :
    leechSquareSum (generatedAxisGlobalFifthShortRootLattice k).val = 32 := by
  rw [generatedAxisGlobalFifthShortRootLattice_physical]
  exact (generatedAxisGlobalFifthShortRoot_certificate k).2.1

/-- The actual quotient coordinates are the displayed seven hyperbolic binary vectors. -/
theorem generatedAxisGlobalFifthShortRootLattice_binary (k : Fin 7) :
    leechHyperbolicCoordinates (leechReduction (generatedAxisGlobalFifthShortRootLattice k)) =
      generatedAxisGlobalFifthShortRootBinary k := by
  rw [leechHyperbolicCoordinates_explicit]
  have hc : leechExplicitCoordinates (generatedAxisGlobalFifthShortRootLattice k) =
      generatedAxisGlobalFifthShortRootCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  rw [hc]
  exact (generatedAxisGlobalFifthShortRoot_certificate k).2.2

/-- Every checked short root is excluded from the actual binary Ω orbit. -/
theorem generatedAxisGlobalFifthShortRoot_not_mem_orbit (k : Fin 7) :
    generatedAxisGlobalFifthShortRootBinary k ∉ generatedAxisGlobalBinaryOrbit := by
  rw [← generatedAxisGlobalFifthShortRootLattice_binary]
  exact generatedAxisGlobalBinary_short_excluded
    (generatedAxisGlobalFifthShortRootLattice k) (generatedAxisGlobalFifthShortRootLattice_norm k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
