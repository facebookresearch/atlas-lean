/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthShortSupportCertificate

/-! Complete actual support fixation and the original invariant norm recover the whole short
block. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each corrected original monomial fixes every short coefficient, including every zero. -/
theorem generatedSixth_monomial_short_fixed (k : Fin 4) :
    localShortOperator (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      (griessConwayEncode generatedSixthAxis).2.1 =
    (griessConwayEncode generatedSixthAxis).2.1 := by
  let X := (griessConwayEncode generatedSixthAxis).2.1
  let Y := localShortOperator (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)) X
  have hn : (∑ r : GriessShortIndex, Y r ^ 2) = ∑ r : GriessShortIndex, X r ^ 2 := by
    have h := localShortRepresentation_pairing (generatedSixthCorrectedGenerator (Fin.castAdd 1 k))
      X X
    change (∑ r, Y r * Y r) = ∑ r, X r * X r at h
    simpa only [pow_two] using h
  apply generatedFourth_real_eq_of_norm_support X Y hn
  intro r hr
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, j⟩)
  · exact generatedSixth_monomial_pair_fixed k s p
  · exact generatedSixth_monomial_octad_supported_fixed k o e hr
  · exact generatedSixth_monomial_odd_supported_fixed k d j hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
