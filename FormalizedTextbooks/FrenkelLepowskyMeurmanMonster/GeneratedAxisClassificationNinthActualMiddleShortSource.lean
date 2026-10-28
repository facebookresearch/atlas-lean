/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowComplete
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerTensorSourceFormulaGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerShortSourceFormulaGeneric

/-! Complete original row and dictionary certificates give unconditional whole source formulas. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual middle short coordinate, including zeros, has its complete signed source value. -/
theorem generatedNinth_actual_middle_short_source (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 r =
        (generatedNinthLowerMiddleShortCoefficient r : ℝ) / 16 :=
  generatedNinth_lower_middle_short_actual generatedNinth_short_row_certificate_all r

/-- Every actual incoming odd coordinate has the corresponding complete signed source value. -/
theorem generatedNinth_actual_incoming_short_source (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inr (d, i))) =
        (generatedNinthLowerIncomingCoefficient d i : ℝ) / 16 :=
  generatedNinth_actual_middle_short_source _

/-- Every actual normalized tensor coordinate has its full original XYZ source numerator. -/
theorem generatedNinth_actual_tensor_source_formula (t : SpinIndex) (i : Fin 24) :
    64 * Real.sqrt 2 * (griessConwayEncode generatedNinthAxis).2.2 t i =
      (generatedNinthLowerTensorSourceInteger (nortonUIntegerLabel t) i : ℝ) :=
  generatedNinth_lower_tensor_source_generic_actual generatedNinth_actual_middle_short_source t i

/-- Every actual normalized preferred short coordinate has its full original triality numerator. -/
theorem generatedNinth_actual_short_source_formula (r : GriessShortIndex) :
    256 * (griessConwayEncode generatedNinthAxis).2.1 r =
      (generatedNinthLowerShortSourceInteger r : ℝ) :=
  generatedNinth_lower_short_source_generic_actual generatedNinth_actual_middle_short_source r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
