/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightIncomingShortCertificates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality

/-! Complete actual root-eight outgoing octad coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every incoming octad row retains the actual signed source cache. -/
theorem generatedFifthRootEight_incoming_octad_cache (o : Fin 759) (f : Fin 64) :
    (griessConwayEncode (rhoLocal generatedFifthRootEightLocal generatedFifthAxis)).2.1
      (Sum.inr (Sum.inl (o, f))) =
        (generatedFifthRootEightIncomingShortCoefficient (Sum.inr (Sum.inl (o, f))) : ℝ) / 16 := by
  change (griessConwayEncode
    (rhoLocal (generatedAxisGlobalFifthShortLocalWord 8) generatedFifthAxis)).2.1 _ = _
  rw [generatedAxisGlobalFifthRoot08Packet_actual, generatedFifthRootEight_incoming_short_actual]

/-- The entire sixty-four-term signed integer triality sum at each physical outgoing octad. -/
def generatedFifthRootEightFinalOctadNumerator (o : Fin 759) (e : Fin 64) : ℤ :=
  ∑ f : Fin 64, trialityIntegerMatrix e f *
    generatedFifthRootEightIncomingShortCoefficient (Sum.inr (Sum.inl (o, f)))

/-- Every original outgoing octad coefficient is its complete source sum divided by128. -/
theorem generatedFifthRootEight_final_octad_numerator (o : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedFifthRootEightAxis).2.1 (Sum.inr (Sum.inl (o, e))) =
      (generatedFifthRootEightFinalOctadNumerator o e : ℝ) / 128 := by
  rw [generatedFifthRootEightAxis_local_expression, generatedFourthQShortBasis_triality_octad]
  simp_rw [generatedFifthRootEight_incoming_octad_cache]
  rw [generatedFifthRootEightFinalOctadNumerator]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro f _
  simp only [trialityRealMatrix, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  change ((1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ)) *
      ((generatedFifthRootEightIncomingShortCoefficient
        (Sum.inr (Sum.inl (o, f))) : ℝ) / 16) = _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
