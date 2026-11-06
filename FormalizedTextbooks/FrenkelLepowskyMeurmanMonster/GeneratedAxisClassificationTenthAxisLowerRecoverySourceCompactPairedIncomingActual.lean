/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactIncomingAtoms
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactSparseIncomingActual

/-! Complete actual compact incoming tensor formula without an original spin-sign premise. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- All actual compact incoming tensor coordinates are the complete64 paired source terms. -/
theorem generatedTenth_source_compact_paired_incoming_actual (k : Fin 4096) (i : Fin 24) :
    generatedTenthSourceCompactIncomingPacket.2.2 (golayLabelCoefficients k) i =
      (generatedTenthSourceCompactSparseIncomingQ k i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedTenth_source_compact_incoming_paired_atoms]
  simp only [Finset.sum_apply]
  simp_rw [generatedTenth_source_compact_sparse_atom_actual]
  unfold generatedTenthSourceCompactSparseIncomingQ
  push_cast
  rw [Finset.sum_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
