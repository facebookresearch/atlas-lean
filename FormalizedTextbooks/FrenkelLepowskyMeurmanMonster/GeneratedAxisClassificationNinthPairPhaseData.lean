/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPairData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortQ

/-! Compact actual nonzero source rows and preferred-Q phase certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Exactly the eight original inverse rows with nonzero fifth short coefficients. -/
def generatedNinthPairSupportedRow : Fin 8 → Fin 552 :=
  ![45, 74, 92, 267, 308, 375, 463, 534]

/-- The recorded central phase, used only on genuinely supported input rows. -/
def generatedNinthPairPhaseCache (r : Fin 552) : ZMod 2 :=
  if r.val ∈ ([74, 92, 267, 463] : List ℕ) then 1 else 0

/-- Sixteen times every original local fifth-image pair coefficient. -/
def generatedNinthPairCoefficientNumerator (r : Fin 552) : ℤ :=
  if r.val ∈ ([45, 267, 375, 463] : List ℕ) then 2 else
    if r.val ∈ ([74, 92, 308, 534] : List ℕ) then -2 else 0

set_option maxHeartbeats 16000000 in
-- Support is checked against the complete actual fifth short-coefficient formulas.
/-- Every nonzero original source row occurs in the eight displayed rows. -/
theorem generatedNinth_pair_supported_row : ∀ r : Fin 552,
    generatedNinthInputShortNumerator (generatedNinthPairSource r) ≠ 0 →
      ∃ j : Fin 8, generatedNinthPairSupportedRow j = r := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Evaluate the actual nine original Q conjugations on only the nonzero source rows.
/-- Every recorded phase is the true preferred-Q central coefficient of the original source word. -/
theorem generatedNinth_pair_phase_certificate : ∀ j : Fin 8,
    toAdd (generatedNinthQImage (generatedNinthInputShortQ
      (generatedNinthPairSource (generatedNinthPairSupportedRow j)))).coeff =
        generatedNinthPairPhaseCache (generatedNinthPairSupportedRow j) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The signed numerator equation preserves the actual source Fourier and Parker phases.
/-- The complete pair coefficient table has its actual signed source numerator. -/
theorem generatedNinth_pair_coefficient_certificate : ∀ r : Fin 552,
    (if generatedNinthPairPhaseCache r = 0 then (1 : ℤ) else -1) *
      generatedNinthInputShortNumerator (generatedNinthPairSource r) =
        generatedNinthPairCoefficientNumerator r := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
