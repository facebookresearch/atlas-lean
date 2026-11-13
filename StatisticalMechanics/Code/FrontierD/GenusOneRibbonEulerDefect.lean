/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsoradialCellularRibbonDuality
import Mathlib.Data.Finset.Interval

open Finset Equiv

namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {D E : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]




def genusOneRibbonEulerDefect (R : RibbonPermutationSystem E D)
    (vertexCount : Nat) (clusters : Finset E → Nat)
    (F : Finset E) : Int :=
  2 * (clusters F : Int) + (F.card : Int) -
    (R.boundaryComponents F : Int) - (vertexCount : Int)

theorem genusOneRibbonEulerDefect_empty
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (clusters : Finset E → Nat)
    (hclusters : clusters ∅ = C.primalVertexCount) :
    genusOneRibbonEulerDefect R C.primalVertexCount clusters ∅ = 0 := by
  unfold genusOneRibbonEulerDefect
  rw [hclusters, R.boundaryComponents_empty,
    C.rotationCycles_eq_primalVertexCount]
  simp only [Finset.card_empty, Nat.cast_zero]
  ring

theorem genusOneRibbonEulerDefect_univ
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (clusters : Finset E → Nat)
    (hgenus : C.genus = 1)
    (hclusters : clusters Finset.univ = 1)
    (hboundary : R.boundaryComponents Finset.univ = C.dualVertexCount) :
    genusOneRibbonEulerDefect R C.primalVertexCount clusters Finset.univ = 2 := by
  unfold genusOneRibbonEulerDefect
  rw [hclusters, hboundary, Finset.card_univ]
  have hEuler := C.cellularEuler
  rw [hgenus] at hEuler
  push_cast
  omega


theorem genusOneRibbonEulerDefect_even
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (clusters : Finset E → Nat) (hgenus : C.genus = 1)
    (F : Finset E) :
    Even (genusOneRibbonEulerDefect
      R C.primalVertexCount clusters F) := by
  have hparity := C.boundaryParity F
  have hcard : F.card + Fᶜ.card = Fintype.card E := by
    exact Finset.card_add_card_compl F
  have hEuler := C.cellularEuler
  rw [hgenus] at hEuler
  unfold genusOneRibbonEulerDefect
  rw [Int.even_iff]
  omega








theorem genusOneRibbonEulerDefect_classified
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (clusters : Finset E → Nat)
    (hgenus : C.genus = 1)
    (hempty : clusters ∅ = C.primalVertexCount)
    (hfullClusters : clusters Finset.univ = 1)
    (hfullBoundary :
      R.boundaryComponents Finset.univ = C.dualVertexCount)
    (hmonoInsert : ∀ (F : Finset E) (e : E), e ∉ F →
      genusOneRibbonEulerDefect R C.primalVertexCount clusters F ≤
        genusOneRibbonEulerDefect R C.primalVertexCount clusters (insert e F))
    (F : Finset E) :
    genusOneRibbonEulerDefect R C.primalVertexCount clusters F = 0 ∨
      genusOneRibbonEulerDefect R C.primalVertexCount clusters F = 2 := by
  let defect : Finset E → Int :=
    genusOneRibbonEulerDefect R C.primalVertexCount clusters
  have hmono : Monotone defect :=
    Finset.monotone_iff_forall_le_insert.mpr hmonoInsert
  have hzero : defect ∅ = 0 :=
    genusOneRibbonEulerDefect_empty R C clusters hempty
  have htwo : defect Finset.univ = 2 :=
    genusOneRibbonEulerDefect_univ R C clusters hgenus
      hfullClusters hfullBoundary
  have hlower : 0 ≤ defect F := by
    rw [← hzero]
    exact hmono (Finset.empty_subset F)
  have hupper : defect F ≤ 2 := by
    rw [← htwo]
    exact hmono (Finset.subset_univ F)
  have heven : Even (defect F) :=
    genusOneRibbonEulerDefect_even R C clusters hgenus F
  rcases heven with ⟨z, hz⟩
  change defect F = 0 ∨ defect F = 2
  omega

end

end StatMech.FrontierD
