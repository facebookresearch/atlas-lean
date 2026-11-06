/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthRootsData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaNormEight

/-! Every candidate fifth transition root belongs to the genuine binary Ω
orbit, using its actual norm-eight Leech vector and proved lattice transitivity. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The fourteen genuine integral Leech vectors in the exact proved lattice model. -/
def generatedAxisGlobalFifthRootLattice (k : Fin 14) : leechIntegral :=
  leechExplicitCoordinateMap (generatedAxisGlobalFifthRootCoordinates k)

/-- Their actual physical coordinates are exactly the finite checked representatives. -/
theorem generatedAxisGlobalFifthRootLattice_physical (k : Fin 14) :
    (generatedAxisGlobalFifthRootLattice k).val = generatedAxisGlobalFifthRootPhysical k :=
  (generatedAxisGlobalFifthRoot_certificate k).1

/-- Every candidate root has genuine Leech norm eight. -/
theorem generatedAxisGlobalFifthRootLattice_norm (k : Fin 14) :
    leechSquareSum (generatedAxisGlobalFifthRootLattice k).val = 64 := by
  rw [generatedAxisGlobalFifthRootLattice_physical]
  exact (generatedAxisGlobalFifthRoot_certificate k).2.1

/-- The actual quotient coordinates are the displayed fourteen hyperbolic binary vectors. -/
theorem generatedAxisGlobalFifthRootLattice_binary (k : Fin 14) :
    leechHyperbolicCoordinates (leechReduction (generatedAxisGlobalFifthRootLattice k)) =
      generatedAxisGlobalFifthRootBinary k := by
  rw [leechHyperbolicCoordinates_explicit]
  have hc : leechExplicitCoordinates (generatedAxisGlobalFifthRootLattice k) =
      generatedAxisGlobalFifthRootCoordinates k :=
    leechExplicitCoordinates.apply_symm_apply _
  rw [hc]
  exact (generatedAxisGlobalFifthRoot_certificate k).2.2

/-- Positive extraspecial lifts of the fourteen genuine binary roots. -/
def generatedAxisGlobalFifthRootQ (k : Fin 14) : Q :=
  ⟨ofAdd (generatedAxisGlobalFifthRootBinary k), 1⟩

/-- Each root admits genuine Conway transport to Ω, independently of its expected orbit size. -/
theorem generatedAxisGlobalFifthRoot_transport (k : Fin 14) :
    ∃ c : Co1, co1BinaryAction c (generatedAxisGlobalFifthRootBinary k) =
      toAdd (qQuotHom sourceOmegaQ) := by
  exact localOmega_binary_transport_of_normEight (generatedAxisGlobalFifthRootQ k)
    (generatedAxisGlobalFifthRootLattice k) (generatedAxisGlobalFifthRootLattice_norm k)
    (generatedAxisGlobalFifthRootLattice_binary k).symm

/-- All fourteen roots are members of the actual binary Ω orbit. -/
theorem generatedAxisGlobalFifthRoot_mem_orbit (k : Fin 14) :
    generatedAxisGlobalFifthRootBinary k ∈ generatedAxisGlobalBinaryOrbit := by
  obtain ⟨c, hc⟩ := generatedAxisGlobalFifthRoot_transport k
  refine ⟨c⁻¹, ?_⟩
  change co1BinaryAction c⁻¹ (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← hc, map_inv]
  exact LinearEquiv.symm_apply_apply _ _

/-- The fourteen genuine Ω roots used in a fifth-family descending-edge certificate. -/
def generatedAxisGlobalFifthRoot (k : Fin 14) : generatedAxisGlobalBinaryOrbit :=
  ⟨generatedAxisGlobalFifthRootBinary k, generatedAxisGlobalFifthRoot_mem_orbit k⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
