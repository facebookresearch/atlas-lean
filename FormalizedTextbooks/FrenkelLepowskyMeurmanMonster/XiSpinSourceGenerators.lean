/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The grey spin generators are the actual normalized source Q generators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinGray
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceQGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The grey code subgroup uses the checked source normalization (5.3.4). -/
theorem xiGrayTranslation_source (a : XiGrayIndex) :
    xiGrayTranslation (ofAdd a) = sourceQTranslation (xiGrayCode a) 0 := rfl

/-- The grey cocode subgroup uses the actual source cocode generators. -/
theorem xiGrayModulation_source (a : XiGrayIndex) :
    xiGrayModulation (ofAdd a) = sourceQCocode (xiGrayCocode a) := rfl

/-- Each standard grey code generator is the published g_i. -/
theorem xiGrayCode_single (i : Fin 6) :
    xiGrayCode (Pi.single i 1) = golayLabelCoefficients (xiGrayCodeLabel i) := by
  change (∑ j : Fin 6, (Pi.single i 1 : XiGrayIndex) j • xiGrayCodeBasis j) = _
  simp [Pi.single_apply, xiGrayCodeBasis]

/-- Positive code lifts are corrected by the actual Parker theta cocode. -/
theorem xiGrayTranslation_basis_source (i : Fin 6) :
    xiGrayTranslation (ofAdd (Pi.single i 1)) =
      sourceQCode (xiGrayCodeLabel i) 0 *
        sourceQCocode (sourceCodeThetaPolynomial (golayLabelCoefficients (xiGrayCodeLabel i))) := by
  rw [sourceQCode_theta_normalization, xiGrayTranslation_source, xiGrayCode_single]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
