/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded kernel certificates of complete spin coordinate and sign actions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsNodePlanCertificates

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates9
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPermutationCertificates13

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000 in
/-- Every target plan passes the full finite coordinate and phase checks. -/
theorem representativePermutationSpin_plan_certificate : ∀ n : Fin 83,
    representativeSpinPlanValid representativeNodeSpinModel
      (representativePermutationStartModel n)
      (representativePermutationSpinPlan n) := by
  intro n
  fin_cases n
  · exact representativePermutationSpin_plan_certificate0
  · exact representativePermutationSpin_plan_certificate1
  · exact representativePermutationSpin_plan_certificate2
  · exact representativePermutationSpin_plan_certificate3
  · exact representativePermutationSpin_plan_certificate4
  · exact representativePermutationSpin_plan_certificate5
  · exact representativePermutationSpin_plan_certificate6
  · exact representativePermutationSpin_plan_certificate7
  · exact representativePermutationSpin_plan_certificate8
  · exact representativePermutationSpin_plan_certificate9
  · exact representativePermutationSpin_plan_certificate10
  · exact representativePermutationSpin_plan_certificate11
  · exact representativePermutationSpin_plan_certificate12
  · exact representativePermutationSpin_plan_certificate13
  · exact representativePermutationSpin_plan_certificate14
  · exact representativePermutationSpin_plan_certificate15
  · exact representativePermutationSpin_plan_certificate16
  · exact representativePermutationSpin_plan_certificate17
  · exact representativePermutationSpin_plan_certificate18
  · exact representativePermutationSpin_plan_certificate19
  · exact representativePermutationSpin_plan_certificate20
  · exact representativePermutationSpin_plan_certificate21
  · exact representativePermutationSpin_plan_certificate22
  · exact representativePermutationSpin_plan_certificate23
  · exact representativePermutationSpin_plan_certificate24
  · exact representativePermutationSpin_plan_certificate25
  · exact representativePermutationSpin_plan_certificate26
  · exact representativePermutationSpin_plan_certificate27
  · exact representativePermutationSpin_plan_certificate28
  · exact representativePermutationSpin_plan_certificate29
  · exact representativePermutationSpin_plan_certificate30
  · exact representativePermutationSpin_plan_certificate31
  · exact representativePermutationSpin_plan_certificate32
  · exact representativePermutationSpin_plan_certificate33
  · exact representativePermutationSpin_plan_certificate34
  · exact representativePermutationSpin_plan_certificate35
  · exact representativePermutationSpin_plan_certificate36
  · exact representativePermutationSpin_plan_certificate37
  · exact representativePermutationSpin_plan_certificate38
  · exact representativePermutationSpin_plan_certificate39
  · exact representativePermutationSpin_plan_certificate40
  · exact representativePermutationSpin_plan_certificate41
  · exact representativePermutationSpin_plan_certificate42
  · exact representativePermutationSpin_plan_certificate43
  · exact representativePermutationSpin_plan_certificate44
  · exact representativePermutationSpin_plan_certificate45
  · exact representativePermutationSpin_plan_certificate46
  · exact representativePermutationSpin_plan_certificate47
  · exact representativePermutationSpin_plan_certificate48
  · exact representativePermutationSpin_plan_certificate49
  · exact representativePermutationSpin_plan_certificate50
  · exact representativePermutationSpin_plan_certificate51
  · exact representativePermutationSpin_plan_certificate52
  · exact representativePermutationSpin_plan_certificate53
  · exact representativePermutationSpin_plan_certificate54
  · exact representativePermutationSpin_plan_certificate55
  · exact representativePermutationSpin_plan_certificate56
  · exact representativePermutationSpin_plan_certificate57
  · exact representativePermutationSpin_plan_certificate58
  · exact representativePermutationSpin_plan_certificate59
  · exact representativePermutationSpin_plan_certificate60
  · exact representativePermutationSpin_plan_certificate61
  · exact representativePermutationSpin_plan_certificate62
  · exact representativePermutationSpin_plan_certificate63
  · exact representativePermutationSpin_plan_certificate64
  · exact representativePermutationSpin_plan_certificate65
  · exact representativePermutationSpin_plan_certificate66
  · exact representativePermutationSpin_plan_certificate67
  · exact representativePermutationSpin_plan_certificate68
  · exact representativePermutationSpin_plan_certificate69
  · exact representativePermutationSpin_plan_certificate70
  · exact representativePermutationSpin_plan_certificate71
  · exact representativePermutationSpin_plan_certificate72
  · exact representativePermutationSpin_plan_certificate73
  · exact representativePermutationSpin_plan_certificate74
  · exact representativePermutationSpin_plan_certificate75
  · exact representativePermutationSpin_plan_certificate76
  · exact representativePermutationSpin_plan_certificate77
  · exact representativePermutationSpin_plan_certificate78
  · exact representativePermutationSpin_plan_certificate79
  · exact representativePermutationSpin_plan_certificate80
  · exact representativePermutationSpin_plan_certificate81
  · exact representativePermutationSpin_plan_certificate82

set_option maxRecDepth 20000 in
/-- The target plans retain exactly the recorded signed generator order. -/
theorem representativePermutationSpin_plan_letters : ∀ n : Fin 83,
    (representativePermutationSpinPlan n).map Prod.fst = representativePermutationWord n := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- Every corrected plan ends at the expected standard target matrix and full phase. -/
theorem representativePermutationSpin_plan_end : ∀ n : Fin 83,
    representativeSpinPlanEnd (representativePermutationStartModel n)
      (representativePermutationSpinPlan n) =
        representativeSpinRowsModel (representativePermutationCoordinateRows n)
          (representativePermutationPhaseRows n) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
