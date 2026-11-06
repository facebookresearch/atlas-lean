/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanCertificate2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanCertificate3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanSoundness

/-! The four bounded signed model certificates imply the exact original spin actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original monomial word has its entire finite signed matrix plan verified. -/
theorem generatedFourth_monomial_spin_plans_valid (k : Fin 4) :
    representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFourthMonomialSpinPlan k) := by
  fin_cases k
  · exact generatedFourth_monomial_spin_plan_certificate_0
  · exact generatedFourth_monomial_spin_plan_certificate_1
  · exact generatedFourth_monomial_spin_plan_certificate_2
  · exact generatedFourth_monomial_spin_plan_certificate_3

/-- Unconditional full original spin action, retaining every intermediate Parker phase. -/
theorem generatedFourth_monomial_spin_model_certificate (k : Fin 4) :
    representativeSpinCertificate (generatedFourthMonomialFiber k).val.1
      (generatedFourthMonomialSpinModel k).coordinate
      (generatedFourthMonomialSpinModel k).phase :=
  generatedFourth_monomial_spin_plan_sound k (generatedFourth_monomial_spin_plans_valid k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
