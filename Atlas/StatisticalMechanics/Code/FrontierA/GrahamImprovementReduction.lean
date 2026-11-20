/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.GrahamImprovementBridge

namespace StatMech.FrontierA

open Finset
open scoped symmDiff
open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def grahamLeadingSurplus
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  grahamLeadingTerm E J i j k l m - grahamUrsell4 E J i j k l



noncomputable def grahamCorrectionDemand
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (i j k l m : V) : ℝ :=
  -(grahamKCorrection E J i j k l m +
    grahamICorrection E J i j k l m)



theorem grahamCorrectionDemand_eq
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (i j k l m : V) :
    grahamCorrectionDemand E J i j k l m =
      2 * (grahamBridgeGap E J i k m * grahamBridgeGap E J j k m *
        grahamTwoPoint E J k l) +
      2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
        grahamBridgeGap E J i k m * grahamBridgeGap E J i l m) := by
  unfold grahamCorrectionDemand grahamKCorrection grahamICorrection
  ring


theorem grahamCorrectionDemand_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ)
    (hJ : ∀ e ∈ E, 0 ≤ J e) (i j k l m : V) :
    0 ≤ grahamCorrectionDemand E J i j k l m := by
  unfold grahamCorrectionDemand
  linarith [grahamKCorrection_nonpos E J hJ i j k l m,
    grahamICorrection_nonpos E J hJ i j k l m]



theorem grahamCorrectedBound_iff_demand_le_surplus
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (i j k l m : V) :
    grahamUrsell4 E J i j k l ≤ grahamCorrectedRHS E J i j k l m ↔
      grahamCorrectionDemand E J i j k l m ≤
        grahamLeadingSurplus E J i j k l m := by
  unfold grahamCorrectionDemand grahamLeadingSurplus grahamCorrectedRHS
  constructor <;> intro h <;> linarith



theorem grahamImprovement_eq_of_aux_eq_first_third
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (i j l : V) :
    grahamUrsell4 E J i j i l = grahamCorrectedRHS E J i j i l i := by
  have hsupport : grahamFourSupport i j i l = grahamPairSupport j l := by
    rw [grahamFourSupport]
    have hcomm : grahamPairSupport i j = grahamPairSupport j i := by
      unfold grahamPairSupport
      rw [symmDiff_comm]
    rw [hcomm, grahamPairSupport_chain]
  have hfour : grahamFourPoint E J i j i l = grahamTwoPoint E J j l := by
    unfold grahamFourPoint grahamTwoPoint
    rw [hsupport]
  rw [grahamUrsell4, hfour]
  simp [grahamCorrectedRHS, grahamLeadingTerm,
    grahamKCorrection, grahamICorrection, grahamBridgeGap,
    grahamTwoPoint_self, grahamTwoPoint_comm]
  ring



theorem grahamImprovement_eq_of_aux_eq_first_fourth
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (i j k : V) :
    grahamUrsell4 E J i j k i = grahamCorrectedRHS E J i j k i i := by
  have hsupport : grahamFourSupport i j k i = grahamPairSupport j k := by
    rw [grahamFourSupport]
    have hcomm : grahamPairSupport i j = grahamPairSupport j i := by
      unfold grahamPairSupport
      rw [symmDiff_comm]
    have hcomm2 : grahamPairSupport k i = grahamPairSupport i k := by
      unfold grahamPairSupport
      rw [symmDiff_comm]
    rw [hcomm, hcomm2, grahamPairSupport_chain]
  have hfour : grahamFourPoint E J i j k i = grahamTwoPoint E J j k := by
    unfold grahamFourPoint grahamTwoPoint
    rw [hsupport]
  rw [grahamUrsell4, hfour]
  simp [grahamCorrectedRHS, grahamLeadingTerm,
    grahamKCorrection, grahamICorrection, grahamBridgeGap,
    grahamTwoPoint_self, grahamTwoPoint_comm]
  ring



theorem grahamImprovement_eq_of_aux_eq_first_second
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (i k l : V) :
    grahamUrsell4 E J i i k l = grahamCorrectedRHS E J i i k l i := by
  have hfour : grahamFourPoint E J i i k l = grahamTwoPoint E J k l := by
    unfold grahamFourPoint grahamTwoPoint
    rw [show grahamFourSupport i i k l = grahamPairSupport k l by
      simp [grahamFourSupport, grahamPairSupport]]
  rw [grahamUrsell4, hfour]
  simp [grahamCorrectedRHS, grahamLeadingTerm,
    grahamKCorrection, grahamICorrection, grahamBridgeGap,
    grahamTwoPoint_self, grahamTwoPoint_comm]
  ring



theorem grahamImprovement_eq_of_aux_eq_second_third
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (i j l : V) :
    grahamUrsell4 E J i j j l = grahamCorrectedRHS E J i j j l j := by
  have hsupport : grahamFourSupport i j j l = grahamPairSupport i l := by
    rw [grahamFourSupport, grahamPairSupport_chain]
  have hfour : grahamFourPoint E J i j j l = grahamTwoPoint E J i l := by
    unfold grahamFourPoint grahamTwoPoint
    rw [hsupport]
  rw [grahamUrsell4, hfour]
  simp [grahamCorrectedRHS, grahamLeadingTerm,
    grahamKCorrection, grahamICorrection, grahamBridgeGap,
    grahamTwoPoint_self, grahamTwoPoint_comm]
  ring



theorem grahamImprovement_eq_of_aux_eq_second_fourth
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (i j k : V) :
    grahamUrsell4 E J i j k j = grahamCorrectedRHS E J i j k j j := by
  have hsupport : grahamFourSupport i j k j = grahamPairSupport i k := by
    rw [grahamFourSupport]
    have hcomm : grahamPairSupport k j = grahamPairSupport j k := by
      unfold grahamPairSupport
      rw [symmDiff_comm]
    rw [hcomm, grahamPairSupport_chain]
  have hfour : grahamFourPoint E J i j k j = grahamTwoPoint E J i k := by
    unfold grahamFourPoint grahamTwoPoint
    rw [hsupport]
  rw [grahamUrsell4, hfour]
  simp [grahamCorrectedRHS, grahamLeadingTerm,
    grahamKCorrection, grahamICorrection, grahamBridgeGap,
    grahamTwoPoint_self, grahamTwoPoint_comm]
  ring



theorem grahamImprovement_eq_of_aux_eq_third_fourth
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (i j k : V) :
    grahamUrsell4 E J i j k k = grahamCorrectedRHS E J i j k k k := by
  have hfour : grahamFourPoint E J i j k k = grahamTwoPoint E J i j := by
    unfold grahamFourPoint grahamTwoPoint
    rw [show grahamFourSupport i j k k = grahamPairSupport i j by
      simp [grahamFourSupport, grahamPairSupport]]
  rw [grahamUrsell4, hfour]
  simp [grahamCorrectedRHS, grahamLeadingTerm,
    grahamKCorrection, grahamICorrection, grahamBridgeGap,
    grahamTwoPoint_self]
  ring



theorem grahamImprovement_eq_of_repeated_aux
    (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (i j k l m : V)
    (h : (i = j ∧ m = i) ∨ (i = k ∧ m = i) ∨ (i = l ∧ m = i) ∨
      (j = k ∧ m = j) ∨ (j = l ∧ m = j) ∨ (k = l ∧ m = k)) :
    grahamUrsell4 E J i j k l = grahamCorrectedRHS E J i j k l m := by
  rcases h with hij | hik | hil | hjk | hjl | hkl
  · rcases hij with ⟨hij, hmi⟩
    subst j
    subst m
    exact grahamImprovement_eq_of_aux_eq_first_second E J i k l
  · rcases hik with ⟨hik, hmi⟩
    subst k
    subst m
    exact grahamImprovement_eq_of_aux_eq_first_third E J i j l
  · rcases hil with ⟨hil, hmi⟩
    subst l
    subst m
    exact grahamImprovement_eq_of_aux_eq_first_fourth E J i j k
  · rcases hjk with ⟨hjk, hmj⟩
    subst k
    subst m
    exact grahamImprovement_eq_of_aux_eq_second_third E J i j l
  · rcases hjl with ⟨hjl, hmj⟩
    subst l
    subst m
    exact grahamImprovement_eq_of_aux_eq_second_fourth E J i j k
  · rcases hkl with ⟨hkl, hmk⟩
    subst l
    subst m
    exact grahamImprovement_eq_of_aux_eq_third_fourth E J i j k

end StatMech.FrontierA
