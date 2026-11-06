/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerTensorSourceFormulaGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortSource

/-! The complete original row certificates instantiate the full source arithmetic formula. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual normalized tensor coordinate has its complete original integer XYZ formula. -/
theorem generatedNinth_lower_tensor_source_actual
    (hrows : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (t : SpinIndex) (i : Fin 24) :
    64 * Real.sqrt 2 * (griessConwayEncode generatedNinthAxis).2.2 t i =
      (generatedNinthLowerTensorSourceInteger (nortonUIntegerLabel t) i : ℝ) :=
  generatedNinth_lower_tensor_source_generic_actual
    (generatedNinth_lower_middle_short_actual hrows) t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
