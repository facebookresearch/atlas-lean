/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeMappingPath
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidNativeLoopComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.DiagonalMappingFibreStandardLoopMap
import MathlibExt.AlgebraicTopology.SimplicialSpace.DiagonalMappingHomotopyFibrePath

/-!
# The actual native mapping-loop formula

The original native contraction comparison is the standard original edge
loop followed by the constant loop at the same original object. This is an
equality of the full original compact-open paths, including the half-interval
parameter introduced by the actual homotopy-fibre return construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

set_option backward.isDefEq.respectTransparency false in
/-- The full native comparison is the standard original edge loop followed by its actual constant tail. -/
theorem nativeMappingLoopComparison_formula (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (z : SSet.toTop.obj (mappingFibre W x x)) :
    nativeMappingLoopComparison W x z =
      (standardDiagonalLoopMap W x z).trans (Path.refl (realizedDiagonalPoint W x)) := by
  apply Path.ext
  funext t
  have h := TopCat.homotopyFiberToLoopsOfBasedContraction_apply
    (realizedDiagonalProjection W x) (SSet.realizedVertex (diagonalBasepoint W x))
    (realizedDiagonalPoint W x) (realizedBasepoint_projection W x) (nativeBasedContraction W x)
    (mappingToDiagonalHomotopyFibre W x x z) t
  have htot : TopCat.homotopyFiberToTotal (realizedDiagonalProjection W x) (realizedDiagonalPoint W x)
      (mappingToDiagonalHomotopyFibre W x x z) = SSet.toTop.map (mappingToPathDiagonal W x x) z :=
    ConcreteCategory.congr_hom (mappingToDiagonalHomotopyFibre_toTotal W x x) z
  have hpath := ConcreteCategory.congr_hom (mappingToDiagonalHomotopyFibre_path W x x) z
  change TopCat.homotopyFiberToLoopsOfBasedContraction (realizedDiagonalProjection W x)
    (SSet.realizedVertex (diagonalBasepoint W x)) (realizedDiagonalPoint W x)
    (realizedBasepoint_projection W x) (nativeBasedContraction W x)
    (mappingToDiagonalHomotopyFibre W x x z) t = _
  rw [Path.trans_apply]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [dite_eq_left ht, htot] at h
    let s : unitInterval := ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
    have hc : (nativeBasedContraction W x).homotopy.symm.toContinuousMap
        (s, SSet.toTop.map (mappingToPathDiagonal W x x) z) =
      realizedNativePointContraction W x (s, SSet.toTop.map (mappingToPathDiagonal W x x) z) :=
      nativeBasedContraction_reverse_apply W x s _
    have hp := nativeMappingPath_apply W x x z s
    rw [dite_eq_left ht]
    exact h.trans ((congrArg (fun a => realizedDiagonalProjection W x a) hc).trans hp)
  · rw [dite_eq_right ht] at h ⊢
    exact h.trans (congrArg (fun p : TopCat.pathObject
      (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram)) =>
        p (TopCat.I.homeomorph.symm
          ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩)) hpath)

end SimplicialSpace.LeftDecalageObject
