/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickDualLumpedLaw
import Code.OSSS.FKSharpnessWeightedDomainActive





open Finset Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

noncomputable section



def triHexBrickDualInnerActiveRestrict
    {N m : Nat} (hNm : N < m)
    (rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet) :
    ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet :=
  ocd_innerRestrictActive (triHexBrickInnerTriangleGraph N)
    (triHexBrickFullDualGraph m) (triHexBrickInnerFaceMap N m)
    (triHexBrickInnerFaceMap_adjMatch hNm) rho



theorem triHexBrick_freeTriangular_dominated_lumped_inner
    {N m : Nat} (hNm : N < m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (triHexBrickInnerTriangleGraph N) ⊥
        (fun _ => p) q (A.indicator fun _ => (1 : Real)) ≤
      activeBCMean (triHexBrickFullDualGraph m) ⊥
        (triHexBrickDualLumpedParam N m p) q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (triHexBrickDualInnerActiveRestrict hNm rho)) := by
  have hdom := ocd_free_inner_dominated_activeBCMean
    (triHexBrickInnerTriangleGraph N) (triHexBrickFullDualGraph m)
    (triHexBrickInnerFaceMap N m) (fun _ => False)
    (triHexBrickInnerFaceMap_injective hNm)
    (triHexBrickInnerFaceMap_adjMatch hNm)
    (triHexBrickDualLumpedParam_compatible N m p)
    (fun _ => hp) (fun _ => hp1)
    (triHexBrickDualLumpedParam_pos hNm hp hp1)
    (triHexBrickDualLumpedParam_lt_one hNm hp hp1)
    hq hA
  have hfalse : boundaryCliqueGraph
      (fun _ : kwg_Face (triHexPlanarFiniteStarPlanar m) => False) = ⊥ := by
    ext x y
    simp [boundaryCliqueGraph_adj]
  simpa only [hfalse, triHexBrickDualInnerActiveRestrict] using hdom



theorem triHexBrick_lumped_inner_dominated_wired
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (triHexBrickFullDualGraph m) ⊥
        (triHexBrickDualLumpedParam N m p) q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (triHexBrickDualInnerActiveRestrict hNm rho)) ≤
      activeBCMean (triHexBrickInnerTriangleGraph N)
        (boundaryCliqueGraph (triHexBrickInnerBoundary N))
        (fun _ => p) q (A.indicator fun _ => (1 : Real)) := by
  have hdom := ocd_wired_inner_dominated_activeBCMean
    (triHexBrickInnerTriangleGraph N) (triHexBrickFullDualGraph m)
    (triHexBrickInnerFaceMap N m) (fun _ => False)
    (triHexBrickInnerFaceMap_injective hNm)
    (triHexBrickInnerFaceMap_adjMatch hNm)
    (triHexBrickInnerBoundary N)
    (triHexBrickDualLumpedParam_compatible N m p)
    (fun _ => hp) (fun _ => hp1)
    (triHexBrickDualLumpedParam_pos hNm hp hp1)
    (triHexBrickDualLumpedParam_lt_one hNm hp hp1)
    hq (triHexBrickInner_inducedWiring_le_boundaryClique hNm hN) hA
  have hfalse : boundaryCliqueGraph
      (fun _ : kwg_Face (triHexPlanarFiniteStarPlanar m) => False) = ⊥ := by
    ext x y
    simp [boundaryCliqueGraph_adj]
  simpa only [hfalse, triHexBrickDualInnerActiveRestrict] using hdom



theorem triHexBrick_pfdDual_inner_dominated_wired
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    (∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      A.indicator (fun _ => (1 : Real))
          (triHexBrickDualInnerActiveRestrict hNm
            (triHexBrickPfdSupport m omega)) *
        pfdDualProb (triHexPlanarFiniteStarPlanar m) p q omega) ≤
      activeBCMean (triHexBrickInnerTriangleGraph N)
        (boundaryCliqueGraph (triHexBrickInnerBoundary N))
        (fun _ => p) q (A.indicator fun _ => (1 : Real)) := by
  let F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real :=
    fun rho => A.indicator (fun _ => (1 : Real))
      (triHexBrickDualInnerActiveRestrict hNm rho)
  have hmean := triHexBrick_pfdDualMean_eq_lumped hNm hp hp1
    (zero_lt_one.trans_le hq) F
  change (∑ omega : ConfigSpace
      (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      F (triHexBrickPfdSupport m omega) *
        pfdDualProb (triHexPlanarFiniteStarPlanar m) p q omega) ≤ _
  rw [hmean]
  exact triHexBrick_lumped_inner_dominated_wired
    hNm hN hp hp1 hq hA



theorem triHexBrick_freeTriangular_dominated_pfdDual_inner
    {N m : Nat} (hNm : N < m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (triHexBrickInnerTriangleGraph N) ⊥
        (fun _ => p) q (A.indicator fun _ => (1 : Real)) ≤
      ∑ omega : ConfigSpace
          (Sym2 (triHexPlanarFiniteStarPlanar m).V),
        A.indicator (fun _ => (1 : Real))
            (triHexBrickDualInnerActiveRestrict hNm
              (triHexBrickPfdSupport m omega)) *
          pfdDualProb (triHexPlanarFiniteStarPlanar m) p q omega := by
  let F : ConfigSpace (triHexBrickFullDualGraph m).edgeSet → Real :=
    fun rho => A.indicator (fun _ => (1 : Real))
      (triHexBrickDualInnerActiveRestrict hNm rho)
  have hmean := triHexBrick_pfdDualMean_eq_lumped hNm hp hp1
    (zero_lt_one.trans_le hq) F
  change _ ≤ ∑ omega : ConfigSpace
      (Sym2 (triHexPlanarFiniteStarPlanar m).V),
    F (triHexBrickPfdSupport m omega) *
      pfdDualProb (triHexPlanarFiniteStarPlanar m) p q omega
  rw [hmean]
  exact triHexBrick_freeTriangular_dominated_lumped_inner
    hNm hp hp1 hq hA

end

end StatMech.FK.PeriodicPlanar
