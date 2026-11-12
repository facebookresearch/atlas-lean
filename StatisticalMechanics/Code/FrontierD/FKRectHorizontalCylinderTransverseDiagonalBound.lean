/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectHorizontalCylinderEndpointLift
import Code.FrontierD.FKRectHorizontalCylinderAdaptiveStep
import Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer











open MeasureTheory SimpleGraph StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section



theorem fkQgt4CriticalFree_ofPairedWitness_embedding_le_sqrt_exact
    {q : Real} (hq : 4 < q)
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (T : Finset (Fin R.width)) (hT : T.Nonempty)
    (psi : ConfigSpace (Sym2 R.Vertex))
    (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi)
    (x : Fin R.width)
    (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T
      (x, fkRectBottomRow R))
    (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T
      (pair x, fkRectTopRow R)) :
    FK.infiniteTwoPointReal
        (fkQgt4CriticalFreeMeasure hq :
          Measure (ConfigSpace (Sym2 (Site 2))))
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
            R psi pair T hT hbase).embedding
          ⟨(x, fkRectBottomRow R), hsource⟩).1
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
            R psi pair T hT hbase).embedding
          ⟨(pair x, fkRectTopRow R), htarget⟩).1 <=
      Real.sqrt
        (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) := by
  let source : FKRectHorizontalCylinderUnexploredVertex R psi T :=
    ⟨(x, fkRectBottomRow R), hsource⟩
  let target : FKRectHorizontalCylinderUnexploredVertex R psi T :=
    ⟨(pair x, fkRectTopRow R), htarget⟩
  let rawDx :=
    (fkRectHorizontalCylinderUnexploredLiftPoint R psi T target).1 -
      (fkRectHorizontalCylinderUnexploredLiftPoint R psi T source).1
  have hdisp :=
    FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness_embedding_sub
      R psi pair T hT hbase source target x (pair x) rfl rfl
  have htranslate :=
    fkQgt4CriticalFree_infiniteTwoPointReal_eq_displacement hq
      ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
          R psi pair T hT hbase).embedding source).1
      ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
          R psi pair T hT hbase).embedding target).1
  rw [htranslate]
  rw [show
      ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
          R psi pair T hT hbase).embedding target).1 -
        ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness
          R psi pair T hT hbase).embedding source).1 =
          fkRectHorizontalCylinderSquareLiftedDisplacement rawDx R.height by
      simpa [rawDx] using hdisp]
  exact
    fkQgt4CriticalFreeTwoPoint_squareLiftedDisplacement_le_sqrt_exact
      hq R rawDx



theorem fkRectHorizontalCylinderDistinctPairedWitness_mass_le_sqrtExact_pow_erase
    {q : Real} (hq : 4 < q)
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (S : Finset (Fin R.width)) (first : Fin R.width) (hfirst : first ∈ S) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R)
          (fkRectCriticalP q) q)
        {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} <=
      Real.sqrt
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^
        (S.erase first).card := by
  let a := Real.sqrt
    (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1))
  apply fkRectHorizontalCylinderDistinctPairedWitness_mass_le_pow_erase_of_twoPoint
    R pair
    (fkRectCriticalP_pos (by linarith : (0 : Real) < q))
    (fkRectCriticalP_lt_one (by linarith : (0 : Real) < q))
    (by linarith : (1 : Real) <= q)
    (Real.sqrt_nonneg _) ?_ S first hfirst
  intro T hT x hx psi hbase hsource htarget
  simpa [a, fkQgt4CriticalFreeMeasure, fkRectCriticalP,
    BeffaraDC.selfDualPoint] using
    fkQgt4CriticalFree_ofPairedWitness_embedding_le_sqrt_exact
      hq R pair T hT psi hbase x hsource htarget





theorem fkRectAfCylinderEvent_mass_le_sqrtExact_pow_pred
    {q : Real} (hq : 4 < q) (R : FKRectTorus) (r : Nat) (hr : 0 < r)
    {I : Finset R.EdgeIndex}
    (hrepair : FKRectAfWindingTailPrescribedCylinderRepair R r I) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R)
          (fkRectCriticalP q) q)
        {rho | FKRectHorizontalCylinderDistinctPairedWitness R
          (fkRectAfPair R) (fkRectAfBottomIndexSet R r) rho} <=
      Real.sqrt
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^
        (r - 1) := by
  let first := fkRectAfBottomIndex R 0
  have hfirst : first ∈ fkRectAfBottomIndexSet R r := by
    apply Finset.mem_image.mpr
    exact ⟨0, Finset.mem_range.mpr hr, rfl⟩
  have hbound :=
    fkRectHorizontalCylinderDistinctPairedWitness_mass_le_sqrtExact_pow_erase
      hq R (fkRectAfPair R) (fkRectAfBottomIndexSet R r) first hfirst
  rw [Finset.card_erase_of_mem hfirst, hrepair.1] at hbound
  exact hbound




theorem fkRectCriticalWindingTailMass_cFE_le_twoPow_mul_sqrtExact_pow_pred
    {q : Real} (hq : 4 < q) (R : FKRectTorus)
    (r perimeter : Nat) (hr : 0 < r)
    (I : Finset R.EdgeIndex) (hI : I.card <= perimeter)
    (hrepair : FKRectAfWindingTailPrescribedCylinderRepair R r I) :
    FK.cFE (fkRectCriticalP q) q ^ perimeter *
        fkRectCriticalWindingTailMass R q r <=
      (2 ^ perimeter : Nat) *
        (Real.sqrt
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1))) ^
            (r - 1) := by
  have htransfer :=
    fkRectCriticalWindingTailMass_cFE_perimeter_le_afCylinderEvent
      R (by linarith : (1 : Real) <= q) r perimeter I hI hrepair
  have hcylinder := fkRectAfCylinderEvent_mass_le_sqrtExact_pow_pred
    hq R r hr hrepair
  have htwo : (0 : Real) <= (2 ^ perimeter : Nat) := by positivity
  exact htransfer.trans (mul_le_mul_of_nonneg_left hcylinder htwo)

end

end StatMech.FrontierD
