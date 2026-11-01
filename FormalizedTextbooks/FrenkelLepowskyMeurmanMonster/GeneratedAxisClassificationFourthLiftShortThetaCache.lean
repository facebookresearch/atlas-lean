/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortSource

/-! Literal evaluation of the original Parker theta on the sixty-three listed code rows. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Candidate original theta labels, checked against the actual Parker code operation. -/
def generatedFourthLiftShortThetaLabels : Fin 63 → Fin 4096 :=
  ![1025, 11, 1034, 103, 1126, 1025, 0, 1025, 0, 93, 1116, 1276,
    253, 1178, 155, 1258, 235, 1206, 183, 1030, 7, 215, 1238, 123,
    1146, 1025, 0, 173, 1196, 1036, 13, 64, 64, 279, 279, 2044,
    2044, 1658, 1658, 1996, 1996, 539, 539, 128, 128, 1414, 1414, 1610,
    1610, 813, 813, 1462, 1462, 0, 0, 295, 295, 192, 192, 555,
    555, 797, 797]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check every original theta coefficient, with no phase reconstruction assumption.
/-- Every literal theta entry is exactly the genuine preferred-lift theta coefficient. -/
theorem generatedFourth_lift_short_theta_cache :
    ∀ j : Fin 63, sourceWordTheta (generatedFourthEvenRootCode j) =
      golayLabelCoefficients (generatedFourthLiftShortThetaLabels j) := by
  decide +kernel

/-- The original preferred octad lift, evaluated with its certified theta label. -/
def generatedFourthLiftShortOctadQFast (j : Fin 63) (e : Fin 64) : Q :=
  ⟨Multiplicative.ofAdd (Fin.append
    (golayLabelCoefficients (generatedFourthEvenRootCode j) +
      griessOctadOmegaCoefficient e • Pi.single 11 1)
    (golayLabelCoefficients (generatedFourthLiftShortThetaLabels j) +
      golaySyndrome (integerParity (fun i : Fin 24 =>
        if (generatedFourthLiftShortSignMask j e).testBit i.val then (1 : ℤ) else 0)))), 1⟩

/-- Cached evaluation retains every original preferred-Q binary coordinate and central bit. -/
theorem generatedFourth_lift_short_octad_q_fast (j : Fin 63) (e : Fin 64) :
    generatedFourthLiftShortSourceQ j e = generatedFourthLiftShortOctadQFast j e := by
  simp only [generatedFourthLiftShortSourceQ, generatedFourthLiftShortOctadQFast,
    generatedFourth_lift_short_theta_cache]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
