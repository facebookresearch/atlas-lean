/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerShortSourceFormulaGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortSource

/-! The complete original row certificates instantiate the full source arithmetic formula. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All original rows bind every actual preferred short coordinate to its full source numerator. -/
theorem generatedNinth_lower_short_source_actual
    (hrows : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
    (r : GriessShortIndex) :
    256 * (griessConwayEncode generatedNinthAxis).2.1 r =
      (generatedNinthLowerShortSourceInteger r : ℝ) :=
  generatedNinth_lower_short_source_generic_actual
    (generatedNinth_lower_middle_short_actual hrows) r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
