/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryActualTransitionCounts

/-! A genuine whole-octad extraspecial fixer with nonzero phase on the outside first root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original hyperbolic vector with support at coordinates seven and nine. -/
def generatedFeasibleOutsideOctadPhaseVector : Fin 24 → ZMod 2 :=
  fun i => if i = 7 ∨ i = 9 then 1 else 0

/-- A genuine original extraspecial-group element on that vector. -/
def generatedFeasibleOutsideOctadPhaseQ : Q :=
  ⟨ofAdd generatedFeasibleOutsideOctadPhaseVector, 1⟩

private def firstIntegerCoordinates : Fin 24 → ℤ :=
  fun i => if i = 0 then 1 else if i = 1 then -1 else 0

private theorem first_integer_certificate :
    leechBasisMatrix *ᵥ firstIntegerCoordinates =
      griessShortIntegral (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  simp only [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates]
  decide +kernel

private theorem first_coordinates :
    leechExplicitCoordinates
      (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
      firstIntegerCoordinates := by
  apply leechBasisMatrix_injective
  change leechBasisMatrix *ᵥ leechExplicitCoordinates
      (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
    leechBasisMatrix *ᵥ firstIntegerCoordinates
  rw [leechExplicitCoordinates_vector]
  exact first_integer_certificate.symm

/-- The actual first preferred-root base is the original hyperbolic vector e21+e22. -/
theorem generatedFeasibleOutsideOctad_first_base :
    toAdd (griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).base =
      (fun i : Fin 24 => if i = 21 ∨ i = 22 then (1 : ZMod 2) else 0) := by
  change leechHyperbolicCoordinates (leechReduction
    (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))) = _
  rw [leechHyperbolicCoordinates_explicit, first_coordinates]
  decide +kernel

/-- The literal original vector has zero commutator phase on all eight actual octad roots. -/
theorem generatedFeasibleOutsideOctad_phase_basis :
    generatedOctadBasisBinaryPhases generatedFeasibleOutsideOctadPhaseVector = 0 := by
  decide +kernel

/-- The actual extraspecial witness belongs to the entire original whole-octad phase kernel. -/
theorem generatedFeasibleOutsideOctad_phase_kernel :
    generatedFeasibleOutsideOctadPhaseQ ∈ generatedOctadBasisQPhases.ker := by
  apply MonoidHom.mem_ker.mpr
  apply toAdd.injective
  rw [generatedOctadBasis_Q_phases_apply]
  exact generatedFeasibleOutsideOctad_phase_basis

/-- The same actual whole-octad fixer has nonzero phase at the outside first axis. -/
theorem generatedFeasibleOutsideOctad_phase_first :
    toAdd (localAxisQPhase (Sum.inl (0, generatedFeasiblePhysicalRootPair))
      generatedFeasibleOutsideOctadPhaseQ) = 1 := by
  change qBeta generatedFeasibleOutsideOctadPhaseVector
      (toAdd (griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).base) +
    qBeta (toAdd (griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).base)
      generatedFeasibleOutsideOctadPhaseVector = 1
  rw [generatedFeasibleOutsideOctad_first_base]
  decide +kernel

/-- All original coordinates of the actual positive octad axis are fixed by the witness. -/
theorem generatedFeasibleOutsideOctad_phase_whole_axis :
    rhoLocal (inclQ generatedFeasibleOutsideOctadPhaseQ)
      (generatedOctadLocalAxis 0 0) = generatedOctadLocalAxis 0 0 := by
  exact generatedOctad_phase_kernel_le_axis_stabilizer 0 0
    generatedFeasibleOutsideOctad_phase_kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
