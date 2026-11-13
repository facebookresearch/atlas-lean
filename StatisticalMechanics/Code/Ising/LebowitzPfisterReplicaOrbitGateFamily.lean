/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaBalancedOrbit



open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _





theorem lpReplicaDisconnFamilies_partialReflect_offdiag_swapRows
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b))
    (hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites ∅ a)
    (hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) b) :
    let m := lpReplicaCollisionProfile G sites a b
    let tag := lpReplicaCollisionRowTag G sites a b Sa Sb
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K := lpReplicaRowCopies G sites m tag true
    let P := edgeComponent e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let movedTag := lpReplicaSwapRowsTag
      (lpReplicaPartialReflectTagRaw G sites m P tag)
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    (LPReplicaRowGate G sites target Si ∅ movedTag ∧
        (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T) ∨
      (LPReplicaRowGate G sites target Sj ∅ movedTag ∧
        (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T) := by
  dsimp only
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let m := lpReplicaCollisionProfile G sites a b
  let tag := lpReplicaCollisionRowTag G sites a b Sa Sb
  have hgate0 := lpReplicaCollisionRowGate_of_mem_disconnFamilies
    G sites a b Sa Sb ∅ (Si ∆ Sj ∆ T) hSa hSb
  have hfixed := lpReplicaCurrentReflect_offdiagSource G sites i j
  have hgate : LPReplicaRowGate G sites m ∅ (Si ∆ Sj ∆ T) tag := by
    simpa only [m, tag, Si, Sj, T, hfixed] using hgate0
  simpa only [m, tag, Si, Sj, T] using
    lpReplicaRowGate_partialReflect_offdiag_swapRows
      G sites hsite hij m tag hgate

end

end StatMech.Ising
