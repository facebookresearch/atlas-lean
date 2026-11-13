/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickDualDomination





open Finset Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

noncomputable section

theorem triHexBrickInnerTriangleGraph_eq_triangularBoxGraph (N : Nat) :
    triHexBrickInnerTriangleGraph N = triangularBoxGraph N := rfl

theorem triHexBrickInnerBoundary_iff_shell
    (N : Nat) (x : TriangularBoxVertex N) :
    triHexBrickInnerBoundary N x ↔ x ∈ triangularBoxShell N N := by
  simp [triHexBrickInnerBoundary, triangularBoxShell]

theorem triHexBrickInnerBoundaryGraph_eq_triangularBoxBoundaryGraph
    (N : Nat) :
    boundaryCliqueGraph (triHexBrickInnerBoundary N) =
      triangularBoxBoundaryGraph N := rfl



theorem triHexBrick_freeStarDual_inner_dominated_wiredTriangular
    {N m : Nat} (hNm : N < m) (hN : 1 ≤ N)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    (∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      A.indicator (fun _ => (1 : Real))
          (triHexBrickDualInnerActiveRestrict hNm
            (triHexBrickPfdSupport m omega)) *
        fkProb (triHexPlanarFiniteStarPlanar m).G p q omega) ≤
      activeBCMean (triangularBoxGraph N)
        (boundaryCliqueGraph (triHexBrickInnerBoundary N))
        (fun _ => dualParam p q) q
        (A.indicator fun _ => (1 : Real)) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdom := triHexBrick_pfdDual_inner_dominated_wired
    hNm hN (dualParam_pos hp hp1 hq0)
    (dualParam_lt_one hp hp1 hq0) hq hA
  change (∑ omega : ConfigSpace
      (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      A.indicator (fun _ => (1 : Real))
          (triHexBrickDualInnerActiveRestrict hNm
            (triHexBrickPfdSupport m omega)) *
        pfdDualProb (triHexPlanarFiniteStarPlanar m)
          (dualParam p q) q omega) ≤
    activeBCMean (triangularBoxGraph N)
      (boundaryCliqueGraph (triHexBrickInnerBoundary N))
      (fun _ => dualParam p q) q
      (A.indicator fun _ => (1 : Real)) at hdom
  calc
    (∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      A.indicator (fun _ => (1 : Real))
          (triHexBrickDualInnerActiveRestrict hNm
            (triHexBrickPfdSupport m omega)) *
        fkProb (triHexPlanarFiniteStarPlanar m).G p q omega) =
      ∑ omega : ConfigSpace
          (Sym2 (triHexPlanarFiniteStarPlanar m).V),
        A.indicator (fun _ => (1 : Real))
            (triHexBrickDualInnerActiveRestrict hNm
              (triHexBrickPfdSupport m omega)) *
          pfdDualProb (triHexPlanarFiniteStarPlanar m)
            (dualParam p q) q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [pfd_fkProb_duality
        (triHexPlanarFiniteStarPlanar m) omega hp hp1 hq0]
    _ ≤ _ := hdom




theorem triHexBrick_freeTriangular_dominated_freeStarDual_inner
    {N m : Nat} (hNm : N < m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (triangularBoxGraph N) ⊥
        (fun _ => dualParam p q) q
        (A.indicator fun _ => (1 : Real)) ≤
      ∑ omega : ConfigSpace
          (Sym2 (triHexPlanarFiniteStarPlanar m).V),
        A.indicator (fun _ => (1 : Real))
            (triHexBrickDualInnerActiveRestrict hNm
              (triHexBrickPfdSupport m omega)) *
          fkProb (triHexPlanarFiniteStarPlanar m).G p q omega := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdom := triHexBrick_freeTriangular_dominated_pfdDual_inner
    hNm (dualParam_pos hp hp1 hq0)
    (dualParam_lt_one hp hp1 hq0) hq hA
  change activeBCMean (triangularBoxGraph N) ⊥
      (fun _ => dualParam p q) q
      (A.indicator fun _ => (1 : Real)) ≤
    ∑ omega : ConfigSpace
        (Sym2 (triHexPlanarFiniteStarPlanar m).V),
      A.indicator (fun _ => (1 : Real))
          (triHexBrickDualInnerActiveRestrict hNm
            (triHexBrickPfdSupport m omega)) *
        pfdDualProb (triHexPlanarFiniteStarPlanar m)
          (dualParam p q) q omega at hdom
  calc
    activeBCMean (triangularBoxGraph N) ⊥
        (fun _ => dualParam p q) q
        (A.indicator fun _ => (1 : Real)) ≤
      ∑ omega : ConfigSpace
          (Sym2 (triHexPlanarFiniteStarPlanar m).V),
        A.indicator (fun _ => (1 : Real))
            (triHexBrickDualInnerActiveRestrict hNm
              (triHexBrickPfdSupport m omega)) *
          pfdDualProb (triHexPlanarFiniteStarPlanar m)
            (dualParam p q) q omega := hdom
    _ = ∑ omega : ConfigSpace
          (Sym2 (triHexPlanarFiniteStarPlanar m).V),
        A.indicator (fun _ => (1 : Real))
            (triHexBrickDualInnerActiveRestrict hNm
              (triHexBrickPfdSupport m omega)) *
          fkProb (triHexPlanarFiniteStarPlanar m).G p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [pfd_fkProb_duality
        (triHexPlanarFiniteStarPlanar m) omega hp hp1 hq0]

end

end StatMech.FK.PeriodicPlanar
