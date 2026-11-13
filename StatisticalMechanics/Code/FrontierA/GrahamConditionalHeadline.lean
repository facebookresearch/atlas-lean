/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamExpectationAssociationClosure
import Code.FrontierA.GrahamGraphAdapter





open Finset SimpleGraph
open scoped symmDiff
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamPairSupport_eq_pair {x y : V} (hxy : x ≠ y) :
    grahamPairSupport x y = {x, y} := by
  ext z
  simp only [grahamPairSupport, Finset.mem_symmDiff, Finset.mem_singleton,
    Finset.mem_insert]
  aesop



theorem grahamFourSupport_eq_quad
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    grahamFourSupport i j k l = {i, j, k, l} := by
  rw [grahamFourSupport, grahamPairSupport_eq_pair hij,
    grahamPairSupport_eq_pair hkl]
  ext z
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  aesop




theorem grahamCorrectedBound_of_cutPositiveAssociation
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (hJ : ∀ e, 0 ≤ J e)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (hassoc : GrahamCutPositiveAssociation (grahamGraph E) 1 J m) :
    grahamUrsell4 E J i j k l ≤ grahamCorrectedRHS E J i j k l m := by
  have hraw := grahamExpectation_correctedBound_of_cutPositiveAssociation
    (grahamGraph E) 1 J (by norm_num) hJ
    hij hik hil him hjk hjl hjm hkl hkm hlm hassoc
  have hpair {x y : V} (hxy : x ≠ y) :
      expectationJ (grahamGraph E) 1 J {x, y} = grahamTwoPoint E J x y := by
    rw [← grahamPairSupport_eq_pair hxy]
    exact grahamGraph_expectationJ_pair E J hdiag x y
  have hfour :
      expectationJ (grahamGraph E) 1 J {i, j, k, l} =
        grahamFourPoint E J i j k l := by
    rw [← grahamFourSupport_eq_quad hij hik hil hjk hjl hkl]
    exact grahamGraph_expectationJ_eq_expJ E J hdiag
      (grahamFourSupport i j k l)
  rw [hfour,
    hpair hij, hpair hkl, hpair hik, hpair hjl, hpair hil, hpair hjk,
    hpair him, hpair hjm, hpair hkm, hpair hlm,
    hpair hkm.symm, hpair hjk.symm, hpair hjm.symm,
    hpair hik.symm, hpair him.symm, hpair hlm.symm] at hraw
  change grahamUrsell4 E J i j k l ≤
    grahamLeadingTerm E J i j k l m +
      -2 * (grahamBridgeGap E J i k m * grahamBridgeGap E J k j m *
        grahamTwoPoint E J k l) +
      -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m *
        grahamBridgeGap E J k i m * grahamBridgeGap E J i l m) at hraw
  rw [grahamBridgeGap_comm E J k j m,
    grahamBridgeGap_comm E J k i m] at hraw
  simpa [grahamCorrectedRHS, grahamKCorrection, grahamICorrection] using hraw

end StatMech.FrontierA
