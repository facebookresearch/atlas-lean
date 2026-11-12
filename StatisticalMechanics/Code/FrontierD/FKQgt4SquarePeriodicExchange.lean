/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareBufferedIdentification
import Code.FrontierD.FKQgt4SquareDualInfiniteDomination

open Finset Set SimpleGraph MeasureTheory

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK
open StatMech.FK.PeriodicPlanar StatMech.Universality

noncomputable section




theorem fkSquare_freeProbMean_eq_lumpedDual
    {N m : Nat} (hNm : N < m) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real) :
    (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      F (fkSquarePfdSupport m omega) *
        FK.fkProb (FK.boxGraph 2 m) p q omega) =
      ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet,
        F rho * activeBCProb (fkSquareBoxFullDualGraph m) ⊥
          (fkSquareDualLumpedParam N m (dualParam p q)) q rho := by
  have hdual0 : 0 < dualParam p q := dualParam_pos hp hp1 hq
  have hdual1 : dualParam p q < 1 := dualParam_lt_one hp hp1 hq
  calc
    (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      F (fkSquarePfdSupport m omega) *
        FK.fkProb (FK.boxGraph 2 m) p q omega) =
        ∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
          F (fkSquarePfdSupport m omega) *
            pfdDualProb (fkSquareBoxPlanar m) (dualParam p q) q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [fkSquareBox_fkProb_duality m omega hp hp1 hq]
    _ = _ := fkSquare_pfdDualMean_eq_lumped
      hNm hdual0 hdual1 hq F



theorem fkSquare_freeFiniteMeasure_real_faceDualInnerEvent_eq_lumpedDual
    {N m : Nat} (hNm : N < m) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)) :
    (FK.freeFiniteMeasure 2 m hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (fkSquareFaceDualInnerEvent N A) =
      activeBCMean (fkSquareBoxFullDualGraph m) ⊥
        (fkSquareDualLumpedParam N m (dualParam p q)) q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (fkSquareDualInnerActiveRestrict hNm rho)) := by
  let F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real :=
    fun rho => A.indicator (fun _ => (1 : Real))
      (fkSquareDualInnerActiveRestrict hNm rho)
  have hmeas := measurableSet_fkSquareFaceDualInnerEvent N A
  unfold FK.freeFiniteMeasure Measure.real
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply (FK.measurable_extendEdge 2 m) hmeas,
    FK.fkPMF_toMeasure_toReal 2 m hp hp1 hq]
  change (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      A.indicator (fun _ => (1 : Real))
          (fkSquareFaceDualInnerActive N (FK.extendEdge 2 m omega)) *
        FK.fkProb (FK.boxGraph 2 m) p q omega) = _
  calc
    _ = ∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
        F (fkSquarePfdSupport m omega) *
          FK.fkProb (FK.boxGraph 2 m) p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      dsimp only [F]
      rw [fkSquareDualInnerActiveRestrict_pfdSupport_eq_faceDual hNm]
    _ = _ := fkSquare_freeProbMean_eq_lumpedDual hNm hp hp1 hq F




theorem fkSquare_freeBufferedMeasure_real_faceDualInnerEvent_eq_lumpedDual
    {N n : Nat} (hNn : N < square.bufferedRadius n) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)) :
    (square.freeBufferedMeasure n hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (fkSquareFaceDualInnerEvent N A) =
      activeBCMean
        (fkSquareBoxFullDualGraph (square.bufferedRadius n)) ⊥
        (fkSquareDualLumpedParam N (square.bufferedRadius n)
          (dualParam p q)) q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (fkSquareDualInnerActiveRestrict hNn rho)) := by
  rw [fkSquarePeriodic_freeBufferedMeasure_eq n hp hp1 hq]
  exact fkSquare_freeFiniteMeasure_real_faceDualInnerEvent_eq_lumpedDual
    hNn hp hp1 hq A

end

end StatMech.FrontierD
