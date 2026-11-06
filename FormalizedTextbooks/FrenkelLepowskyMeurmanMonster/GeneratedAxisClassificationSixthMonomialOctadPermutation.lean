/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadSignCertificates

/-! Actual preferred octad-label transport follows
from complete original physical sign certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact original source dictionary maps to its genuine preferred target octad label. -/
theorem generatedSixth_monomial_octad_source_permutation (k : Fin 4) (f : Fin 231)
    (e : Fin 64) :
    griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2
      (Sum.inr (Sum.inl
        (generatedSixthFinalOctadCacheOctad (generatedSixthMonomialOctadSourceFamily k f),
          generatedSixthMonomialOctadSourceSign k f e))) =
      Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e)) := by
  apply generatedSixth_monomial_octad_permutation_of_integral
  exact generatedSixth_monomial_octad_integral_transport k f e
    (generatedSixth_monomial_octad_sign_certificate k f e)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
