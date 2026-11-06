/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddData

/-! Exact original source and constant preferred phases for all displayed odd code families. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
-- Check all 512 original source code addresses against the full actual matrix transform.
/-- The displayed normalized source family is the original full-code image modulo all-one. -/
theorem generatedSixth_monomial_odd_source1 :
    ∀ f : Fin 512,
      (generatedSixthMonomialOddCode (generatedSixthMonomialOddSourceFamily 1 f)).val =
        (generatedSixthMonomialOddFullSourceCode 1 f).val % 2048 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check the complete original quadratic, theta and Q modulation on all 512 target code labels.
/-- Every displayed constant phase retains the entire original preferred-Q contribution. -/
theorem generatedSixth_monomial_odd_phase_base1 :
    ∀ f : Fin 512,
      monsterMonomialQuadratic (representativeMatrix (generatedSixthMonomialMaskPhaseRows 1))
        (golayLabelCoefficients ⟨(generatedSixthMonomialOddCode f).val, by omega⟩) +
      spinDot (golayLabelCoefficients (generatedSixthMonomialMaskTranslation 1))
        (sourceWordTheta ⟨(generatedSixthMonomialOddCode f).val, by omega⟩) +
      spinDot (golayLabelCoefficients (generatedSixthMonomialMaskModulation 1))
        (golayLabelCoefficients ⟨(generatedSixthMonomialOddCode f).val, by omega⟩) =
      generatedSixthMonomialOddPhaseBase 1 f := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
