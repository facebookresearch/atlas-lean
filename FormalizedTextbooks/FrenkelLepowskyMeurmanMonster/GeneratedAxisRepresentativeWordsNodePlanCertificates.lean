/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded kernel certificates of complete spin coordinate and sign actions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsOriginalCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsInverseCertificates0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsInverseCertificates1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsInverseCertificates2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsNodeCertificates0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsNodeCertificates1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsNodeCertificates2

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000 in
/-- Every inverse phase agrees with the full pullback of the forward phase. -/
theorem representativeNodeSpin_inverse_phase_certificate : ∀ n : Fin 15,
    (∀ i : Fin 12,
      monsterMonomialQuadratic (representativeMatrix (representativeNodeInversePhaseRows n))
        (Pi.single i 1) =
      monsterMonomialQuadratic (representativeMatrix (representativeNodePhaseRows n))
        ((representativeMatrix (representativeNodeInverseRows n)).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic (representativeMatrix (representativeNodeInversePhaseRows n))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic (representativeMatrix (representativeNodePhaseRows n))
        ((representativeMatrix (representativeNodeInverseRows n)).col i +
          (representativeMatrix (representativeNodeInverseRows n)).col j)) := by
  intro n
  fin_cases n
  · exact representativeNodeSpin_inverse_phase_certificate0
  · exact representativeNodeSpin_inverse_phase_certificate1
  · exact representativeNodeSpin_inverse_phase_certificate2
  · exact representativeNodeSpin_inverse_phase_certificate3
  · exact representativeNodeSpin_inverse_phase_certificate4
  · exact representativeNodeSpin_inverse_phase_certificate5
  · exact representativeNodeSpin_inverse_phase_certificate6
  · exact representativeNodeSpin_inverse_phase_certificate7
  · exact representativeNodeSpin_inverse_phase_certificate8
  · exact representativeNodeSpin_inverse_phase_certificate9
  · exact representativeNodeSpin_inverse_phase_certificate10
  · exact representativeNodeSpin_inverse_phase_certificate11
  · exact representativeNodeSpin_inverse_phase_certificate12
  · exact representativeNodeSpin_inverse_phase_certificate13
  · exact representativeNodeSpin_inverse_phase_certificate14

set_option maxRecDepth 20000 in
/-- All thirteen derived-node plans pass the full finite coordinate and phase checks. -/
theorem representativeNodeSpin_plan_certificate : ∀ n : Fin 15,
    representativeSpinPlanValid representativeNodeSpinModel representativeSpinIdentityModel
      (representativeNodeSpinPlan n) := by
  intro n
  fin_cases n
  · exact representativeNodeSpin_plan_certificate0
  · exact representativeNodeSpin_plan_certificate1
  · exact representativeNodeSpin_plan_certificate2
  · exact representativeNodeSpin_plan_certificate3
  · exact representativeNodeSpin_plan_certificate4
  · exact representativeNodeSpin_plan_certificate5
  · exact representativeNodeSpin_plan_certificate6
  · exact representativeNodeSpin_plan_certificate7
  · exact representativeNodeSpin_plan_certificate8
  · exact representativeNodeSpin_plan_certificate9
  · exact representativeNodeSpin_plan_certificate10
  · exact representativeNodeSpin_plan_certificate11
  · exact representativeNodeSpin_plan_certificate12
  · exact representativeNodeSpin_plan_certificate13
  · exact representativeNodeSpin_plan_certificate14

set_option maxRecDepth 20000 in
/-- The node plans retain exactly the recorded signed generator order. -/
theorem representativeNodeSpin_plan_letters : ∀ n : Fin 15,
    (representativeNodeSpinPlan n).map Prod.fst = representativeNodeWord n := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- The last intermediate node model is exactly its recorded full spin model. -/
theorem representativeNodeSpin_plan_end : ∀ n : Fin 15, 2 ≤ n.val →
    representativeSpinPlanEnd representativeSpinIdentityModel (representativeNodeSpinPlan n) =
      representativeNodeSpinModel (n, false) := by
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
