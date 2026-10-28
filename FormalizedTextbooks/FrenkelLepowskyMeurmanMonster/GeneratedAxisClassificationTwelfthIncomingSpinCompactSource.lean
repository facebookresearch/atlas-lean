/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinCompactConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQFastBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache09

/-! The genuine compact incoming operator has exactly the full original source conjugation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Complete coordinate and central coefficients are compared for all twenty-four source lifts.
/-- All twenty-four full extraspecial images agree with the checked original root-nine source. -/
theorem generatedTwelfth_incoming_spin_compact_source_certificate : ∀ j : Fin 24,
    generatedTwelfthIncomingSpinCompactQImage 0 (qCoordinateGenerator j) =
      generatedAxisGlobalFifthQCache 9 j := by
  intro j
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext k
    have h : ∀ j k : Fin 24,
        toAdd (generatedTwelfthIncomingSpinCompactQImage 0 (qCoordinateGenerator j)).base k =
          toAdd (generatedAxisGlobalFifthQCache 9 j).base k := by
      decide +kernel
    exact h j k
  · apply toAdd.injective
    have h : ∀ j : Fin 24,
        toAdd (generatedTwelfthIncomingSpinCompactQImage 0 (qCoordinateGenerator j)).coeff =
          toAdd (generatedAxisGlobalFifthQCache 9 j).coeff := by
      decide +kernel
    exact h j

/-- The complete compact action on every extraspecial element is the genuine source action. -/
theorem generatedTwelfth_incoming_spin_compact_source_Q (q : Q) :
    spinConjugation (generatedTwelfthIncomingSpinCompact 0) q =
      spinConjugation (generatedTenthQWordFiber 9).val.1 q := by
  have hc := monsterNortonCoordinateEvaluation_eq (generatedTwelfthIncomingSpinCompact 0)
    (generatedAxisGlobalFifthQCache 9)
    (fun j => (generatedTwelfth_incoming_spin_compact_conjugation 0 _).trans
      (generatedTwelfth_incoming_spin_compact_source_certificate j)) q
  rw [generatedTenth_Q_word_image,
    generatedTenth_Q_word_fast 9 generatedAxisGlobalFifthQCache09_actual]
  exact hc

/-- Equality of full Q conjugation retains every original central phase. -/
theorem generatedTwelfth_incoming_spin_compact_source_conjugation :
    spinConjugation (generatedTwelfthIncomingSpinCompact 0) =
      spinConjugation (generatedTenthQWordFiber 9).val.1 :=
  MulEquiv.ext generatedTwelfth_incoming_spin_compact_source_Q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
