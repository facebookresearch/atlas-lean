/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual spin certificates for the compact source permutation DAG. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsNodePlanCertificates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanProducts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

private theorem representativeNodeSpin_inverse (n : Fin 15)
    (h : representativeSpinCertificate (representativeNodeFiber n).val.1
      (representativeMatrix (representativeNodeCoordinateRows n))
      (representativeMatrix (representativeNodePhaseRows n))) :
    representativeSpinCertificate ((representativeNodeFiber n)⁻¹).val.1
      (representativeMatrix (representativeNodeInverseRows n))
      (representativeMatrix (representativeNodeInversePhaseRows n)) := by
  let P := representativeMatrix (representativeNodeCoordinateRows n)
  let M := representativeMatrix (representativeNodePhaseRows n)
  let R := representativeMatrix (representativeNodeInverseRows n)
  let N := representativeMatrix (representativeNodeInversePhaseRows n)
  have hi := representativeSpinCertificate_inv (representativeNodeFiber n).val.1 P M R h
    (representativeNodeSpin_inverse_matrix_certificate n)
  have hp (t : SpinIndex) : monsterMonomialQuadratic (Rᵀ * M * R) t =
      monsterMonomialQuadratic N t := by
    apply representativeQuadratic_basis_pairs
    · intro i
      rw [representativeQuadratic_pullback, Matrix.mulVec_single_one]
      exact ((representativeNodeSpin_inverse_phase_certificate n).1 i).symm
    · intro i j
      rw [representativeQuadratic_pullback, Matrix.mulVec_add,
        Matrix.mulVec_single_one, Matrix.mulVec_single_one]
      exact ((representativeNodeSpin_inverse_phase_certificate n).2 i j).symm
  intro f t
  change (representativeNodeFiber n).val.1⁻¹.val f t =
    qSign (monsterMonomialQuadratic N t) * f (R *ᵥ t)
  rw [hi f t, hp]

private theorem representativeNodeSpin_signed (n : Fin 15) (negative : Bool)
    (h : representativeSpinCertificate (representativeNodeFiber n).val.1
      (representativeMatrix (representativeNodeCoordinateRows n))
      (representativeMatrix (representativeNodePhaseRows n))) :
    representativeSpinCertificate (representativeNodeLetterFiber (n, negative)).val.1
      (representativeNodeSpinModel (n, negative)).coordinate
      (representativeNodeSpinModel (n, negative)).phase := by
  cases negative with
  | false => exact h
  | true => exact representativeNodeSpin_inverse n h

/-- Full actual spin action of compact permutation node 0. -/
theorem representativeNodeSpin_certificate0 :
    representativeSpinCertificate (representativeNodeFiber 0).val.1
      (representativeMatrix (representativeNodeCoordinateRows 0))
      (representativeMatrix (representativeNodePhaseRows 0)) := by
  have hc : representativeMatrix (representativeNodeCoordinateRows (0 : Fin 15)) =
      monsterSourcePermutationCodeMatrix (Fin.castAdd 2 (0 : Fin 2)) ∧
      representativeMatrix (representativeNodePhaseRows (0 : Fin 15)) =
        monsterSourcePermutationPhaseData 0 :=
    representativeNodeSpin_original_certificate 0
  rw [hc.1, hc.2]
  exact representativeSpinCertificate_sourcePermutation 0

/-- Full actual spin action of compact permutation node 1. -/
theorem representativeNodeSpin_certificate1 :
    representativeSpinCertificate (representativeNodeFiber 1).val.1
      (representativeMatrix (representativeNodeCoordinateRows 1))
      (representativeMatrix (representativeNodePhaseRows 1)) := by
  have hc : representativeMatrix (representativeNodeCoordinateRows (1 : Fin 15)) =
      monsterSourcePermutationCodeMatrix (Fin.castAdd 2 (1 : Fin 2)) ∧
      representativeMatrix (representativeNodePhaseRows (1 : Fin 15)) =
        monsterSourcePermutationPhaseData 1 :=
    representativeNodeSpin_original_certificate 1
  rw [hc.1, hc.2]
  exact representativeSpinCertificate_sourcePermutation 1

/-- Full actual spin action of compact permutation node 2. -/
theorem representativeNodeSpin_certificate2 :
    representativeSpinCertificate (representativeNodeFiber 2).val.1
      (representativeMatrix (representativeNodeCoordinateRows 2))
      (representativeMatrix (representativeNodePhaseRows 2)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 2,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 2 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(0, false), (1, false), (0, true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeSpin_signed 0 false
        representativeNodeSpin_certificate0
    · rw [h1]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
    · rw [h2]
      exact representativeNodeSpin_signed 0 true
        representativeNodeSpin_certificate0
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 2) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 2)
  rw [representativeNodeSpin_plan_end 2 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 2).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 2))
    (representativeMatrix (representativeNodePhaseRows 2)) at h
  have hw : ((representativeNodeWord 2).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 2 := by
    change ([representativeNodeFiber0, representativeNodeFiber1, representativeNodeFiber0⁻¹] : List
      localFiberSubgroup).prod =
      representativeNodeFiber2
    rw [representativeNodeFiber2]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 2).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 2).val.1 =
    ((representativeNodeWord 2).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 3. -/
theorem representativeNodeSpin_certificate3 :
    representativeSpinCertificate (representativeNodeFiber 3).val.1
      (representativeMatrix (representativeNodeCoordinateRows 3))
      (representativeMatrix (representativeNodePhaseRows 3)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 3,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 3 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(0, false), (0, false), (1, false), (0, true), (0, true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4
    · rw [h0]
      exact representativeNodeSpin_signed 0 false
        representativeNodeSpin_certificate0
    · rw [h1]
      exact representativeNodeSpin_signed 0 false
        representativeNodeSpin_certificate0
    · rw [h2]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
    · rw [h3]
      exact representativeNodeSpin_signed 0 true
        representativeNodeSpin_certificate0
    · rw [h4]
      exact representativeNodeSpin_signed 0 true
        representativeNodeSpin_certificate0
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 3) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 3)
  rw [representativeNodeSpin_plan_end 3 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 3).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 3))
    (representativeMatrix (representativeNodePhaseRows 3)) at h
  have hw : ((representativeNodeWord 3).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 3 := by
    change ([representativeNodeFiber0, representativeNodeFiber0, representativeNodeFiber1,
      representativeNodeFiber0⁻¹, representativeNodeFiber0⁻¹] : List localFiberSubgroup).prod =
      representativeNodeFiber3
    rw [representativeNodeFiber3]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 3).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 3).val.1 =
    ((representativeNodeWord 3).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 4. -/
theorem representativeNodeSpin_certificate4 :
    representativeSpinCertificate (representativeNodeFiber 4).val.1
      (representativeMatrix (representativeNodeCoordinateRows 4))
      (representativeMatrix (representativeNodePhaseRows 4)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 4,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 4 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(1, false), (3, false), (1, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
    · rw [h1]
      exact representativeNodeSpin_signed 3 false
        representativeNodeSpin_certificate3
    · rw [h2]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 4) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 4)
  rw [representativeNodeSpin_plan_end 4 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 4).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 4))
    (representativeMatrix (representativeNodePhaseRows 4)) at h
  have hw : ((representativeNodeWord 4).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 4 := by
    change ([representativeNodeFiber1, representativeNodeFiber3, representativeNodeFiber1] : List
      localFiberSubgroup).prod =
      representativeNodeFiber4
    rw [representativeNodeFiber4]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 4).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 4).val.1 =
    ((representativeNodeWord 4).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 5. -/
theorem representativeNodeSpin_certificate5 :
    representativeSpinCertificate (representativeNodeFiber 5).val.1
      (representativeMatrix (representativeNodeCoordinateRows 5))
      (representativeMatrix (representativeNodePhaseRows 5)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 5,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 5 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(3, false), (1, false), (3, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeSpin_signed 3 false
        representativeNodeSpin_certificate3
    · rw [h1]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
    · rw [h2]
      exact representativeNodeSpin_signed 3 false
        representativeNodeSpin_certificate3
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 5) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 5)
  rw [representativeNodeSpin_plan_end 5 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 5).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 5))
    (representativeMatrix (representativeNodePhaseRows 5)) at h
  have hw : ((representativeNodeWord 5).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 5 := by
    change ([representativeNodeFiber3, representativeNodeFiber1, representativeNodeFiber3] : List
      localFiberSubgroup).prod =
      representativeNodeFiber5
    rw [representativeNodeFiber5]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 5).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 5).val.1 =
    ((representativeNodeWord 5).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 6. -/
theorem representativeNodeSpin_certificate6 :
    representativeSpinCertificate (representativeNodeFiber 6).val.1
      (representativeMatrix (representativeNodeCoordinateRows 6))
      (representativeMatrix (representativeNodePhaseRows 6)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 6,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 6 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(1, false), (2, false), (3, false), (2, false), (1, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4
    · rw [h0]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
    · rw [h1]
      exact representativeNodeSpin_signed 2 false
        representativeNodeSpin_certificate2
    · rw [h2]
      exact representativeNodeSpin_signed 3 false
        representativeNodeSpin_certificate3
    · rw [h3]
      exact representativeNodeSpin_signed 2 false
        representativeNodeSpin_certificate2
    · rw [h4]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 6) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 6)
  rw [representativeNodeSpin_plan_end 6 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 6).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 6))
    (representativeMatrix (representativeNodePhaseRows 6)) at h
  have hw : ((representativeNodeWord 6).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 6 := by
    change ([representativeNodeFiber1, representativeNodeFiber2, representativeNodeFiber3,
      representativeNodeFiber2, representativeNodeFiber1] : List localFiberSubgroup).prod =
      representativeNodeFiber6
    rw [representativeNodeFiber6]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 6).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 6).val.1 =
    ((representativeNodeWord 6).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 7. -/
theorem representativeNodeSpin_certificate7 :
    representativeSpinCertificate (representativeNodeFiber 7).val.1
      (representativeMatrix (representativeNodeCoordinateRows 7))
      (representativeMatrix (representativeNodePhaseRows 7)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 7,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 7 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [
      (2, false), (3, false), (2, false), (3, false), (1, false), (2, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4 | h5
    · rw [h0]
      exact representativeNodeSpin_signed 2 false
        representativeNodeSpin_certificate2
    · rw [h1]
      exact representativeNodeSpin_signed 3 false
        representativeNodeSpin_certificate3
    · rw [h2]
      exact representativeNodeSpin_signed 2 false
        representativeNodeSpin_certificate2
    · rw [h3]
      exact representativeNodeSpin_signed 3 false
        representativeNodeSpin_certificate3
    · rw [h4]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
    · rw [h5]
      exact representativeNodeSpin_signed 2 false
        representativeNodeSpin_certificate2
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 7) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 7)
  rw [representativeNodeSpin_plan_end 7 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 7).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 7))
    (representativeMatrix (representativeNodePhaseRows 7)) at h
  have hw : ((representativeNodeWord 7).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 7 := by
    change ([representativeNodeFiber2, representativeNodeFiber3, representativeNodeFiber2,
      representativeNodeFiber3, representativeNodeFiber1, representativeNodeFiber2] : List
      localFiberSubgroup).prod =
      representativeNodeFiber7
    rw [representativeNodeFiber7]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 7).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 7).val.1 =
    ((representativeNodeWord 7).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 8. -/
theorem representativeNodeSpin_certificate8 :
    representativeSpinCertificate (representativeNodeFiber 8).val.1
      (representativeMatrix (representativeNodeCoordinateRows 8))
      (representativeMatrix (representativeNodePhaseRows 8)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 8,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 8 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(4, false), (7, false), (4, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeSpin_signed 4 false
        representativeNodeSpin_certificate4
    · rw [h1]
      exact representativeNodeSpin_signed 7 false
        representativeNodeSpin_certificate7
    · rw [h2]
      exact representativeNodeSpin_signed 4 false
        representativeNodeSpin_certificate4
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 8) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 8)
  rw [representativeNodeSpin_plan_end 8 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 8).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 8))
    (representativeMatrix (representativeNodePhaseRows 8)) at h
  have hw : ((representativeNodeWord 8).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 8 := by
    change ([representativeNodeFiber4, representativeNodeFiber7, representativeNodeFiber4] : List
      localFiberSubgroup).prod =
      representativeNodeFiber8
    rw [representativeNodeFiber8]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 8).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 8).val.1 =
    ((representativeNodeWord 8).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 9. -/
theorem representativeNodeSpin_certificate9 :
    representativeSpinCertificate (representativeNodeFiber 9).val.1
      (representativeMatrix (representativeNodeCoordinateRows 9))
      (representativeMatrix (representativeNodePhaseRows 9)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 9,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 9 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(5, false), (8, false), (5, false), (8, true), (5, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4
    · rw [h0]
      exact representativeNodeSpin_signed 5 false
        representativeNodeSpin_certificate5
    · rw [h1]
      exact representativeNodeSpin_signed 8 false
        representativeNodeSpin_certificate8
    · rw [h2]
      exact representativeNodeSpin_signed 5 false
        representativeNodeSpin_certificate5
    · rw [h3]
      exact representativeNodeSpin_signed 8 true
        representativeNodeSpin_certificate8
    · rw [h4]
      exact representativeNodeSpin_signed 5 false
        representativeNodeSpin_certificate5
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 9) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 9)
  rw [representativeNodeSpin_plan_end 9 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 9).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 9))
    (representativeMatrix (representativeNodePhaseRows 9)) at h
  have hw : ((representativeNodeWord 9).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 9 := by
    change ([representativeNodeFiber5, representativeNodeFiber8, representativeNodeFiber5,
      representativeNodeFiber8⁻¹, representativeNodeFiber5] : List localFiberSubgroup).prod =
      representativeNodeFiber9
    rw [representativeNodeFiber9]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 9).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 9).val.1 =
    ((representativeNodeWord 9).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 10. -/
theorem representativeNodeSpin_certificate10 :
    representativeSpinCertificate (representativeNodeFiber 10).val.1
      (representativeMatrix (representativeNodeCoordinateRows 10))
      (representativeMatrix (representativeNodePhaseRows 10)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 10,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 10 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(7, false), (4, false), (7, true), (8, true), (8, true), (9, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4 | h5
    · rw [h0]
      exact representativeNodeSpin_signed 7 false
        representativeNodeSpin_certificate7
    · rw [h1]
      exact representativeNodeSpin_signed 4 false
        representativeNodeSpin_certificate4
    · rw [h2]
      exact representativeNodeSpin_signed 7 true
        representativeNodeSpin_certificate7
    · rw [h3]
      exact representativeNodeSpin_signed 8 true
        representativeNodeSpin_certificate8
    · rw [h4]
      exact representativeNodeSpin_signed 8 true
        representativeNodeSpin_certificate8
    · rw [h5]
      exact representativeNodeSpin_signed 9 false
        representativeNodeSpin_certificate9
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 10) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 10)
  rw [representativeNodeSpin_plan_end 10 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 10).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 10))
    (representativeMatrix (representativeNodePhaseRows 10)) at h
  have hw : ((representativeNodeWord 10).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 10 := by
    change ([representativeNodeFiber7, representativeNodeFiber4, representativeNodeFiber7⁻¹,
      representativeNodeFiber8⁻¹, representativeNodeFiber8⁻¹, representativeNodeFiber9] : List
      localFiberSubgroup).prod =
      representativeNodeFiber10
    rw [representativeNodeFiber10]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 10).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 10).val.1 =
    ((representativeNodeWord 10).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 11. -/
theorem representativeNodeSpin_certificate11 :
    representativeSpinCertificate (representativeNodeFiber 11).val.1
      (representativeMatrix (representativeNodeCoordinateRows 11))
      (representativeMatrix (representativeNodePhaseRows 11)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 11,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 11 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(0, false), (0, false), (0, false), (1, false), (0, true), (0, true), (0,
      true), (3, false), (2, false), (1, false), (3, false), (2, false), (6, false), (7, true), (5,
      false), (6, false), (4, false), (8, true), (8, true), (5, false), (8, true), (9, false), (10,
      true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 |
      h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22
    · rw [h0]
      exact representativeNodeSpin_signed 0 false
        representativeNodeSpin_certificate0
    · rw [h1]
      exact representativeNodeSpin_signed 0 false
        representativeNodeSpin_certificate0
    · rw [h2]
      exact representativeNodeSpin_signed 0 false
        representativeNodeSpin_certificate0
    · rw [h3]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
    · rw [h4]
      exact representativeNodeSpin_signed 0 true
        representativeNodeSpin_certificate0
    · rw [h5]
      exact representativeNodeSpin_signed 0 true
        representativeNodeSpin_certificate0
    · rw [h6]
      exact representativeNodeSpin_signed 0 true
        representativeNodeSpin_certificate0
    · rw [h7]
      exact representativeNodeSpin_signed 3 false
        representativeNodeSpin_certificate3
    · rw [h8]
      exact representativeNodeSpin_signed 2 false
        representativeNodeSpin_certificate2
    · rw [h9]
      exact representativeNodeSpin_signed 1 false
        representativeNodeSpin_certificate1
    · rw [h10]
      exact representativeNodeSpin_signed 3 false
        representativeNodeSpin_certificate3
    · rw [h11]
      exact representativeNodeSpin_signed 2 false
        representativeNodeSpin_certificate2
    · rw [h12]
      exact representativeNodeSpin_signed 6 false
        representativeNodeSpin_certificate6
    · rw [h13]
      exact representativeNodeSpin_signed 7 true
        representativeNodeSpin_certificate7
    · rw [h14]
      exact representativeNodeSpin_signed 5 false
        representativeNodeSpin_certificate5
    · rw [h15]
      exact representativeNodeSpin_signed 6 false
        representativeNodeSpin_certificate6
    · rw [h16]
      exact representativeNodeSpin_signed 4 false
        representativeNodeSpin_certificate4
    · rw [h17]
      exact representativeNodeSpin_signed 8 true
        representativeNodeSpin_certificate8
    · rw [h18]
      exact representativeNodeSpin_signed 8 true
        representativeNodeSpin_certificate8
    · rw [h19]
      exact representativeNodeSpin_signed 5 false
        representativeNodeSpin_certificate5
    · rw [h20]
      exact representativeNodeSpin_signed 8 true
        representativeNodeSpin_certificate8
    · rw [h21]
      exact representativeNodeSpin_signed 9 false
        representativeNodeSpin_certificate9
    · rw [h22]
      exact representativeNodeSpin_signed 10 true
        representativeNodeSpin_certificate10
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 11) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 11)
  rw [representativeNodeSpin_plan_end 11 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 11).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 11))
    (representativeMatrix (representativeNodePhaseRows 11)) at h
  have hw : ((representativeNodeWord 11).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 11 := by
    change ([representativeNodeFiber0, representativeNodeFiber0, representativeNodeFiber0,
      representativeNodeFiber1, representativeNodeFiber0⁻¹, representativeNodeFiber0⁻¹,
      representativeNodeFiber0⁻¹, representativeNodeFiber3, representativeNodeFiber2,
      representativeNodeFiber1, representativeNodeFiber3, representativeNodeFiber2,
      representativeNodeFiber6, representativeNodeFiber7⁻¹, representativeNodeFiber5,
      representativeNodeFiber6, representativeNodeFiber4, representativeNodeFiber8⁻¹,
      representativeNodeFiber8⁻¹, representativeNodeFiber5, representativeNodeFiber8⁻¹,
      representativeNodeFiber9, representativeNodeFiber10⁻¹] : List localFiberSubgroup).prod =
      representativeNodeFiber11
    rw [representativeNodeFiber11]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 11).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 11).val.1 =
    ((representativeNodeWord 11).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 12. -/
theorem representativeNodeSpin_certificate12 :
    representativeSpinCertificate (representativeNodeFiber 12).val.1
      (representativeMatrix (representativeNodeCoordinateRows 12))
      (representativeMatrix (representativeNodePhaseRows 12)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 12,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 12 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(10, false), (11, false), (10, true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeSpin_signed 10 false
        representativeNodeSpin_certificate10
    · rw [h1]
      exact representativeNodeSpin_signed 11 false
        representativeNodeSpin_certificate11
    · rw [h2]
      exact representativeNodeSpin_signed 10 true
        representativeNodeSpin_certificate10
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 12) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 12)
  rw [representativeNodeSpin_plan_end 12 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 12).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 12))
    (representativeMatrix (representativeNodePhaseRows 12)) at h
  have hw : ((representativeNodeWord 12).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 12 := by
    change ([representativeNodeFiber10, representativeNodeFiber11, representativeNodeFiber10⁻¹] :
      List localFiberSubgroup).prod =
      representativeNodeFiber12
    rw [representativeNodeFiber12]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 12).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 12).val.1 =
    ((representativeNodeWord 12).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 13. -/
theorem representativeNodeSpin_certificate13 :
    representativeSpinCertificate (representativeNodeFiber 13).val.1
      (representativeMatrix (representativeNodeCoordinateRows 13))
      (representativeMatrix (representativeNodePhaseRows 13)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 13,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 13 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(9, false), (11, false), (9, false)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeSpin_signed 9 false
        representativeNodeSpin_certificate9
    · rw [h1]
      exact representativeNodeSpin_signed 11 false
        representativeNodeSpin_certificate11
    · rw [h2]
      exact representativeNodeSpin_signed 9 false
        representativeNodeSpin_certificate9
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 13) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 13)
  rw [representativeNodeSpin_plan_end 13 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 13).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 13))
    (representativeMatrix (representativeNodePhaseRows 13)) at h
  have hw : ((representativeNodeWord 13).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 13 := by
    change ([representativeNodeFiber9, representativeNodeFiber11, representativeNodeFiber9] : List
      localFiberSubgroup).prod =
      representativeNodeFiber13
    rw [representativeNodeFiber13]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 13).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 13).val.1 =
    ((representativeNodeWord 13).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- Full actual spin action of compact permutation node 14. -/
theorem representativeNodeSpin_certificate14 :
    representativeSpinCertificate (representativeNodeFiber 14).val.1
      (representativeMatrix (representativeNodeCoordinateRows 14))
      (representativeMatrix (representativeNodePhaseRows 14)) := by
  have hletters : ∀ step ∈ representativeNodeSpinPlan 14,
      representativeSpinCertificate (representativeNodeLetterFiber step.1).val.1
        (representativeNodeSpinModel step.1).coordinate
        (representativeNodeSpinModel step.1).phase := by
    intro step hstep
    have hletter : step.1 ∈ representativeNodeWord 14 := by
      rw [← representativeNodeSpin_plan_letters]
      exact List.mem_map_of_mem hstep
    change step.1 ∈ [(10, false), (13, false), (10, true)] at hletter
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hletter
    rcases hletter with h0 | h1 | h2
    · rw [h0]
      exact representativeNodeSpin_signed 10 false
        representativeNodeSpin_certificate10
    · rw [h1]
      exact representativeNodeSpin_signed 13 false
        representativeNodeSpin_certificate13
    · rw [h2]
      exact representativeNodeSpin_signed 10 true
        representativeNodeSpin_certificate10
  have h := representativeSpinPlan_certificate
    (fun a => (representativeNodeLetterFiber a).val.1) representativeNodeSpinModel
    (representativeNodeSpinPlan 14) 1 representativeSpinIdentityModel
    representativeSpinCertificate_one hletters (representativeNodeSpin_plan_certificate 14)
  rw [representativeNodeSpin_plan_end 14 (by decide +kernel),
    representativeSpinPlanEvaluate_eq_product, one_mul,
    representativeNodeSpin_plan_letters] at h
  change representativeSpinCertificate
    (((representativeNodeWord 14).map (fun a => (representativeNodeLetterFiber a).val.1)).prod)
    (representativeMatrix (representativeNodeCoordinateRows 14))
    (representativeMatrix (representativeNodePhaseRows 14)) at h
  have hw : ((representativeNodeWord 14).map representativeNodeLetterFiber).prod =
      representativeNodeFiber 14 := by
    change ([representativeNodeFiber10, representativeNodeFiber13, representativeNodeFiber10⁻¹] :
      List localFiberSubgroup).prod =
      representativeNodeFiber14
    rw [representativeNodeFiber14]
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hs := representativeFiberSpin_list_prod
    ((representativeNodeWord 14).map representativeNodeLetterFiber)
  rw [hw] at hs
  simp only [List.map_map] at hs
  change (representativeNodeFiber 14).val.1 =
    ((representativeNodeWord 14).map (fun a => (representativeNodeLetterFiber a).val.1)).prod at hs
  rw [← hs] at h
  exact h

/-- All fifteen compact DAG nodes have their actual full signed operator certificates. -/
theorem representativeNodeSpin_certificate (n : Fin 15) :
    representativeSpinCertificate (representativeNodeFiber n).val.1
      (representativeMatrix (representativeNodeCoordinateRows n))
      (representativeMatrix (representativeNodePhaseRows n)) := by
  fin_cases n
  · exact representativeNodeSpin_certificate0
  · exact representativeNodeSpin_certificate1
  · exact representativeNodeSpin_certificate2
  · exact representativeNodeSpin_certificate3
  · exact representativeNodeSpin_certificate4
  · exact representativeNodeSpin_certificate5
  · exact representativeNodeSpin_certificate6
  · exact representativeNodeSpin_certificate7
  · exact representativeNodeSpin_certificate8
  · exact representativeNodeSpin_certificate9
  · exact representativeNodeSpin_certificate10
  · exact representativeNodeSpin_certificate11
  · exact representativeNodeSpin_certificate12
  · exact representativeNodeSpin_certificate13
  · exact representativeNodeSpin_certificate14

/-- Both powers of every DAG node are certified, including their full central phases. -/
theorem representativeNodeSpin_signed_certificate (letter : RepresentativeNodeLetter) :
    representativeSpinCertificate (representativeNodeLetterFiber letter).val.1
      (representativeNodeSpinModel letter).coordinate (representativeNodeSpinModel letter).phase :=
  representativeNodeSpin_signed letter.1 letter.2 (representativeNodeSpin_certificate letter.1)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
