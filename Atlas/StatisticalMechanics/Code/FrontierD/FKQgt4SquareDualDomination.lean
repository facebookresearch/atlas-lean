/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKQgt4SquareDualLumpedLaw
import Code.OSSS.FKSharpnessWeightedDomainActive









open Finset Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section



def fkSquareDualInnerActiveRestrict
    {N m : Nat} (hNm : N < m)
    (rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet) :
    ConfigSpace (FK.boxGraph 2 N).edgeSet :=
  ocd_innerRestrictActive (FK.boxGraph 2 N)
    (fkSquareBoxFullDualGraph m) (fkSquareBox_innerFaceMap N m)
    (fkSquareBox_innerFaceMap_adjMatch hNm) rho



theorem fkSquare_lumped_inner_dominated_wired
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (fkSquareBoxFullDualGraph m) ⊥
        (fkSquareDualLumpedParam N m p) q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (fkSquareDualInnerActiveRestrict hNm rho)) ≤
      activeBCMean (FK.boxGraph 2 N)
        (boundaryCliqueGraph (FK.boxBoundary 2 N))
        (fun _ => p) q (A.indicator fun _ => (1 : Real)) := by
  have hdom := ocd_wired_inner_dominated_activeBCMean
    (FK.boxGraph 2 N) (fkSquareBoxFullDualGraph m)
    (fkSquareBox_innerFaceMap N m) (fun _ => False)
    (fkSquareBox_innerFaceMap_injective hNm)
    (fkSquareBox_innerFaceMap_adjMatch hNm)
    (FK.boxBoundary 2 N)
    (fkSquareDualLumpedParam_compatible N m p)
    (fun _ => hp) (fun _ => hp1)
    (fkSquareDualLumpedParam_pos hNm hp hp1)
    (fkSquareDualLumpedParam_lt_one hNm hp hp1)
    hq (fkSquareBox_inducedWiring_le_boundaryClique hNm hN) hA
  have hfalse : boundaryCliqueGraph
      (fun _ : kwg_Face (fkSquareBoxPlanar m) => False) = ⊥ := by
    ext x y
    simp [boundaryCliqueGraph_adj]
  simpa only [hfalse, fkSquareDualInnerActiveRestrict] using hdom



theorem fkSquare_pfdDual_inner_dominated_wired
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)}
    (hA : IsIncreasing A) :
    (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      A.indicator (fun _ => (1 : Real))
          (fkSquareDualInnerActiveRestrict hNm
            (fkSquarePfdSupport m omega)) *
        pfdDualProb (fkSquareBoxPlanar m) p q omega) ≤
      activeBCMean (FK.boxGraph 2 N)
        (boundaryCliqueGraph (FK.boxBoundary 2 N))
        (fun _ => p) q (A.indicator fun _ => (1 : Real)) := by
  let F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real :=
    fun rho => A.indicator (fun _ => (1 : Real))
      (fkSquareDualInnerActiveRestrict hNm rho)
  have hmean := fkSquare_pfdDualMean_eq_lumped hNm hp hp1
    (zero_lt_one.trans_le hq) F
  change (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)),
      F (fkSquarePfdSupport m omega) *
        pfdDualProb (fkSquareBoxPlanar m) p q omega) ≤ _
  rw [hmean]
  exact fkSquare_lumped_inner_dominated_wired hNm hN hp hp1 hq hA

end

end StatMech.FrontierD
