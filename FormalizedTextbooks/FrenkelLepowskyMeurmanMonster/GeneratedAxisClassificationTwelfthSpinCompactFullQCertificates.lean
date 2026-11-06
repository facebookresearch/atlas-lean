/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactFullQData

/-! Every complete compact candidate has its exact full original extraspecial cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Compare all original central coefficients of the twelve full coordinate actions.
/-- Every actual compact generator image retains precisely its complete central phase. -/
theorem generatedTwelfth_spin_compact_full_Q_phase_certificate : ∀ (g : Fin 12) (j : Fin 24),
    toAdd (generatedTwelfthSpinCompactQImage g (qCoordinateGenerator j)).coeff =
      generatedTwelfthSpinCompactFullQPhase g j := by
  decide +kernel

/-- All full extraspecial generator images equal their cache, including their central phases. -/
theorem generatedTwelfth_spin_compact_full_Q_generator (g : Fin 12) (j : Fin 24) :
    spinConjugation (generatedTwelfthSpinCompact g) (qCoordinateGenerator j) =
      generatedTwelfthSpinCompactFullQCache g j := by
  rw [generatedTwelfth_spin_compact_conjugation]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact generatedTwelfth_spin_compact_binary_certificate g j
  · apply toAdd.injective
    exact generatedTwelfth_spin_compact_full_Q_phase_certificate g j

/-- The exact cache evaluates the entire actual extraspecial action on every input. -/
theorem generatedTwelfth_spin_compact_full_Q_fast (g : Fin 12) (q : Q) :
    spinConjugation (generatedTwelfthSpinCompact g) q =
      generatedTwelfthSpinCompactFullQFast g q :=
  monsterNortonCoordinateEvaluation_eq _ _
    (generatedTwelfth_spin_compact_full_Q_generator g) q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
