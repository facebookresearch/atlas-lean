/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportCertificates00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportCertificates09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortSupportCertificates10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinThreeProjectionGeneration

/-! Full original preferred-Q support checks for the three genuine generating projections. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Each selected actual lift satisfies every original signed support transport condition. -/
theorem generatedNinth_lower_spin_three_short_support_certificates :
    ∀ g : Fin 3, ∀ a, generatedNinthLowerSpinShortSupportCondition
      (generatedNinthLowerSpinThreeCandidateIndex g) a := by
  intro g a
  fin_cases g
  · exact generatedNinth_lower_spin_short_support_certificate_00 a
  · exact generatedNinth_lower_spin_short_support_certificate_09 a
  · exact generatedNinth_lower_spin_short_support_certificate_10 a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
