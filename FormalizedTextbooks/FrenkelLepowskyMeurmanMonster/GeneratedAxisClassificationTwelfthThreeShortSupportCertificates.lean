/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortPackedActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeCandidateIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortSupportPackedCertificates00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortSupportPackedCertificates01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortSupportPackedCertificates02

/-! Every nonzero original source coordinate has its complete actual signed transport certificate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Every nonzero original source coordinate retains its entire binary and central certificate. -/
theorem generatedTwelfth_three_complete_short_support_packed_certificates :
    ∀ (g : Fin 3) a, generatedTwelfthCompleteShortSupportPackedCondition (generatedTwelfthThreeCandidateIndex g) a := by
  intro g a
  fin_cases g
  · exact generatedTwelfth_complete_short_support_packed_certificate_00 a
  · exact generatedTwelfth_complete_short_support_packed_certificate_01 a
  · exact generatedTwelfth_complete_short_support_packed_certificate_02 a

/-- Every finite packet proves the unchanged genuine preferred-Q image and exact signed coefficient. -/
theorem generatedTwelfth_three_complete_short_support_original_certificates :
    ∀ (g : Fin 3) a, generatedTwelfthCompleteShortInputInteger
      (generatedNinthLowerSpinShortIndex a) ≠ 0 → generatedTwelfthCompleteShortCondition (generatedTwelfthThreeCandidateIndex g) a := by
  intro g a hnonzero
  exact generatedTwelfth_complete_short_condition_of_packed (generatedTwelfthThreeCandidateIndex g) a
    (generatedTwelfth_three_complete_short_support_packed_certificates g a hnonzero)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
