/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.GenusOneRibbonEulerDefect

open Finset Equiv

namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {D E : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


theorem genusZeroRibbonEulerDefect_univ
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (clusters : Finset E -> Nat)
    (hgenus : C.genus = 0)
    (hclusters : clusters Finset.univ = 1)
    (hboundary : R.boundaryComponents Finset.univ = C.dualVertexCount) :
    genusOneRibbonEulerDefect R C.primalVertexCount clusters Finset.univ = 0 := by
  unfold genusOneRibbonEulerDefect
  rw [hclusters, hboundary, Finset.card_univ]
  have hEuler := C.cellularEuler
  rw [hgenus] at hEuler
  push_cast
  omega




theorem genusZeroRibbonEulerDefect_eq_zero
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (clusters : Finset E -> Nat)
    (hgenus : C.genus = 0)
    (hempty : clusters ∅ = C.primalVertexCount)
    (hfullClusters : clusters Finset.univ = 1)
    (hfullBoundary :
      R.boundaryComponents Finset.univ = C.dualVertexCount)
    (hmonoInsert : ∀ (F : Finset E) (e : E), e ∉ F →
      genusOneRibbonEulerDefect R C.primalVertexCount clusters F <=
        genusOneRibbonEulerDefect R C.primalVertexCount clusters (insert e F))
    (F : Finset E) :
    genusOneRibbonEulerDefect R C.primalVertexCount clusters F = 0 := by
  let defect : Finset E -> Int :=
    genusOneRibbonEulerDefect R C.primalVertexCount clusters
  have hmono : Monotone defect :=
    Finset.monotone_iff_forall_le_insert.mpr hmonoInsert
  have hempty' : defect ∅ = 0 :=
    genusOneRibbonEulerDefect_empty R C clusters hempty
  have hfull : defect Finset.univ = 0 :=
    genusZeroRibbonEulerDefect_univ R C clusters hgenus
      hfullClusters hfullBoundary
  have hlower : 0 <= defect F := by
    rw [← hempty']
    exact hmono (Finset.empty_subset F)
  have hupper : defect F <= 0 := by
    rw [← hfull]
    exact hmono (Finset.subset_univ F)
  simpa only [defect] using le_antisymm hupper hlower

end

end StatMech.FrontierD
