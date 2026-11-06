/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddShortRootsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryTypes

/-! The six short-vector roots cannot occur in the genuine binary Ω orbit.
The exclusion uses actual lattice norms and the proved minimum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The six genuine integral Leech vectors in the exact proved lattice model. -/
def generatedAxisGlobalOddShortRootLattice (k : Fin 6) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalOddShortRootCoordinates k)

/-- Their actual physical coordinates are exactly the finite checked representatives. -/
theorem generatedAxisGlobalOddShortRootLattice_physical (k : Fin 6) :
    (generatedAxisGlobalOddShortRootLattice k).val =
      generatedAxisGlobalOddShortRootPhysical k :=
  (generatedAxisGlobalOddShortRoot_certificate k).1

/-- Every candidate root has genuine Leech norm four. -/
theorem generatedAxisGlobalOddShortRootLattice_norm (k : Fin 6) :
    leechSquareSum (generatedAxisGlobalOddShortRootLattice k).val = 32 := by
  rw [generatedAxisGlobalOddShortRootLattice_physical]
  exact (generatedAxisGlobalOddShortRoot_certificate k).2.1

/-- The actual quotient coordinates are the displayed six hyperbolic binary vectors. -/
theorem generatedAxisGlobalOddShortRootLattice_binary (k : Fin 6) :
    leechHyperbolicCoordinates (leechReduction (generatedAxisGlobalOddShortRootLattice k)) =
      generatedAxisGlobalOddShortRootBinary k := by
  rw [leechHyperbolicCoordinates_explicit]
  have hc : leechExplicitCoordinates (generatedAxisGlobalOddShortRootLattice k) =
      generatedAxisGlobalOddShortRootCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  rw [hc]
  exact (generatedAxisGlobalOddShortRoot_certificate k).2.2

/-- Every checked short root is excluded from the actual binary Ω orbit. -/
theorem generatedAxisGlobalOddShortRoot_not_mem_orbit (k : Fin 6) :
    generatedAxisGlobalOddShortRootBinary k ∉ generatedAxisGlobalBinaryOrbit := by
  rw [← generatedAxisGlobalOddShortRootLattice_binary]
  exact generatedAxisGlobalBinary_short_excluded
    (generatedAxisGlobalOddShortRootLattice k) (generatedAxisGlobalOddShortRootLattice_norm k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
