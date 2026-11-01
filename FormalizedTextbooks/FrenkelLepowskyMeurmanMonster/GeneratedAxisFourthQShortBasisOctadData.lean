/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisPairData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenPhaseCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine seven-basis character on every sign of each listed octad, in finite source data. -/
def generatedFourthQShortBasisOctadPhase (i : Fin 7) (j : Fin 63) (e : Fin 64) : ZMod 2 :=
  spinDot (golayLabelCoefficients (generatedFourthQAffineParameterBasisTranslationLabels i))
    (sourceWordTheta (generatedFourthEvenRootCode j) + golaySyndrome
      (fun k => if (generatedFourthEvenOctadSignMask j e).testBit k.val then 1 else 0)) +
    spinDot (golayLabelCoefficients (generatedFourthQAffineParameterBasisModulationLabels i))
      (golayLabelCoefficients (generatedFourthEvenRootCode j))

/-- Exact integer numerator of each octad coordinate after the last original DH operation. -/
def generatedFourthQShortBasisOctadNumerator (d : Fin 4096) (e : Fin 64) : ℤ :=
  ∑ j : Fin 63, if generatedFourthEvenRootCode j = d then
    trialityIntegerMatrix e (generatedFourthEvenRootSign j) *
      (if generatedFourthEvenCoefficientCache j = 0 then 1 else -1) else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 24000000 in
-- The kernel checks actual binary signs and the 63-term integer Fourier numerator.
/-- Every nontrivial genuine basis phase has zero actual final octad numerator. -/
theorem generatedFourthQShortBasis_octad_zero_certificate :
    ∀ i : Fin 7, ∀ j : Fin 63, ∀ e : Fin 64,
    generatedFourthQShortBasisOctadPhase i j e ≠ 0 →
      generatedFourthQShortBasisOctadNumerator (generatedFourthEvenRootCode j) e = 0 := by
  intro i j
  revert i
  fin_cases j <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
