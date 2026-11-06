/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortSupportActions

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeShortSupportCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! Every genuine candidate lift fixes the complete actual candidate short constituent. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- All original signed short coefficients of the actual candidate axis are preserved. -/
theorem generatedTwelfth_three_certified_candidate_short_support_fix (g : Fin 3) :
    (griessConwayEncode (rhoLocal (generatedTwelfthCertifiedLocal (generatedTwelfthThreeCandidateIndex g))
      generatedTwelfthIncomingCandidateAxis)).2.1 =
      (griessConwayEncode generatedTwelfthIncomingCandidateAxis).2.1 := by
  rw [generatedTwelfthCertifiedLocal, generatedFourth_local_short]
  exact generatedTwelfth_complete_short_fix_of_support_cache (generatedTwelfthThreeCandidateIndex g)
    (generatedTwelfth_three_complete_short_support_original_certificates g) _
    generatedTwelfth_candidate_short_source_actual

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
