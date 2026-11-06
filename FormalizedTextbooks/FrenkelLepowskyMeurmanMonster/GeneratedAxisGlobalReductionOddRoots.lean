/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddRootsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaNormEight

/-! Every candidate odd transition root belongs to the genuine binary Ω
orbit, using its actual norm-eight Leech vector and proved lattice transitivity. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The nine genuine integral Leech vectors in the exact proved lattice model. -/
def generatedAxisGlobalOddRootLattice (k : Fin 9) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalOddRootCoordinates k)

/-- Their actual physical coordinates are exactly the finite checked representatives. -/
theorem generatedAxisGlobalOddRootLattice_physical (k : Fin 9) :
    (generatedAxisGlobalOddRootLattice k).val = generatedAxisGlobalOddRootPhysical k :=
  (generatedAxisGlobalOddRoot_certificate k).1

/-- Every candidate root has genuine Leech norm eight. -/
theorem generatedAxisGlobalOddRootLattice_norm (k : Fin 9) :
    leechSquareSum (generatedAxisGlobalOddRootLattice k).val = 64 := by
  rw [generatedAxisGlobalOddRootLattice_physical]
  exact (generatedAxisGlobalOddRoot_certificate k).2.1

/-- The actual quotient coordinates are the displayed nine hyperbolic binary vectors. -/
theorem generatedAxisGlobalOddRootLattice_binary (k : Fin 9) :
    leechHyperbolicCoordinates (leechReduction (generatedAxisGlobalOddRootLattice k)) =
      generatedAxisGlobalOddRootBinary k := by
  rw [leechHyperbolicCoordinates_explicit]
  have hc : leechExplicitCoordinates (generatedAxisGlobalOddRootLattice k) =
      generatedAxisGlobalOddRootCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  rw [hc]
  exact (generatedAxisGlobalOddRoot_certificate k).2.2

/-- Positive extraspecial lifts of the nine genuine binary roots. -/
def generatedAxisGlobalOddRootQ (k : Fin 9) : Q :=
  ⟨ofAdd (generatedAxisGlobalOddRootBinary k), 1⟩

/-- Each root admits genuine Conway transport to Ω, independently of its expected orbit size. -/
theorem generatedAxisGlobalOddRoot_transport (k : Fin 9) :
    ∃ c : Co1, co1BinaryAction c (generatedAxisGlobalOddRootBinary k) =
      toAdd (qQuotHom sourceOmegaQ) := by
  exact localOmega_binary_transport_of_normEight (generatedAxisGlobalOddRootQ k)
    (generatedAxisGlobalOddRootLattice k) (generatedAxisGlobalOddRootLattice_norm k)
    (generatedAxisGlobalOddRootLattice_binary k).symm

/-- All nine roots are members of the actual binary Ω orbit. -/
theorem generatedAxisGlobalOddRoot_mem_orbit (k : Fin 9) :
    generatedAxisGlobalOddRootBinary k ∈ generatedAxisGlobalBinaryOrbit := by
  obtain ⟨c, hc⟩ := generatedAxisGlobalOddRoot_transport k
  refine ⟨c⁻¹, ?_⟩
  change co1BinaryAction c⁻¹ (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← hc, map_inv]
  exact LinearEquiv.symm_apply_apply _ _

/-- The nine genuine Ω roots used in a odd-family descending-edge certificate. -/
def generatedAxisGlobalOddRoot (k : Fin 9) : generatedAxisGlobalBinaryOrbit :=
  ⟨generatedAxisGlobalOddRootBinary k, generatedAxisGlobalOddRoot_mem_orbit k⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
