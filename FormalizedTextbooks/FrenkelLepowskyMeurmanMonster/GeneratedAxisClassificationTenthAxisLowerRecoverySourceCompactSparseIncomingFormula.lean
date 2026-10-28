/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactDeltaPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceInitialTensorSparseActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMatrixCoordinates

/-! Ungated complete paired sparse compact source formula; no finite cache proof is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The full original compact integer phase on one incoming paired atom's lower source delta. -/
def generatedTenthSourceCompactSparseIncomingLowSign
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (t : SpinIndex) : ℤ :=
  generatedAxisGlobalIntSign (generatedTenthSourceCompactDeltaPhase
    (golayLabelCoefficients (generatedTenthSourceInitialTensorSparseLow p)) t)

/-- The upper source delta retains its own actual full-Q phase;
its source coefficient is negative. -/
def generatedTenthSourceCompactSparseIncomingHighSign
    (p : GeneratedTenthSourceInitialTensorSparseIndex) (t : SpinIndex) : ℤ :=
  generatedAxisGlobalIntSign (generatedTenthSourceCompactDeltaPhase
    (golayLabelCoefficients (generatedTenthSourceInitialTensorSparseHigh p)) t)

/-- Every rational incoming numerator is the complete sum of64 genuine paired source terms. -/
def generatedTenthSourceCompactSparseIncomingQ (k : Fin 4096) (i : Fin 24) : ℚ :=
  ∑ p : GeneratedTenthSourceInitialTensorSparseIndex,
    (generatedTenthSourceInitialTensorSparseSign p : ℚ) *
      ((generatedTenthSourceCompactSparseIncomingLowSign p (golayLabelCoefficients k) : ℚ) -
        (generatedTenthSourceCompactSparseIncomingHighSign p (golayLabelCoefficients k) : ℚ)) *
          generatedAxisGlobalFifthSpatialWordMatrix 2 i
            (generatedTenthSourceInitialTensorSparseCoordinate p)

/-- Each original paired atom is a genuine normalized rank-one tensor in physical coordinates. -/
theorem generatedTenth_source_compact_sparse_initial_atom
    (p : GeneratedTenthSourceInitialTensorSparseIndex) :
    generatedTenthSourceInitialTensorSparseAtom p =
      ((generatedTenthSourceInitialTensorSparseSign p : ℝ) / Real.sqrt 2) •
        (fun t i =>
          ((((Pi.single (golayLabelCoefficients (generatedTenthSourceInitialTensorSparseLow p))
              (1 : ℝ)) : SpinSpace) -
            ((Pi.single (golayLabelCoefficients (generatedTenthSourceInitialTensorSparseHigh p))
              (1 : ℝ)) : SpinSpace)) t) *
            (((Pi.single (generatedTenthSourceInitialTensorSparseCoordinate p) (1 : ℝ)) :
              Fin 24 → ℝ) i)) := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  simp only [generatedTenthSourceInitialTensorSparseAtom,
    generatedTenthSourceInitialTensorSparseIntegerAtom, generatedAxisGlobalSpinLabel_coeff,
    generatedTwelfthTensorSourceSpatial, generatedTenthSourceInitialTensorSparseCoordinate,
    Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply,
    golayLabelCoefficients_bijective.1.eq_iff]
  push_cast
  split_ifs <;> ring

/-- Every genuine physical source column is its exact rational original word column. -/
theorem generatedTenth_source_compact_sparse_spatial_column (c i : Fin 24) :
    (generatedAxisGlobalFifthShortSpatialWord 2).val (Pi.single c (1 : ℝ)) i =
      (generatedAxisGlobalFifthSpatialWordMatrix 2 i c : ℝ) := by
  change leechIsomMatrix (generatedAxisGlobalFifthShortSpatialWord 2) i c = _
  rw [generatedAxisGlobalFifthSpatialWordMatrix_coordinate]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
