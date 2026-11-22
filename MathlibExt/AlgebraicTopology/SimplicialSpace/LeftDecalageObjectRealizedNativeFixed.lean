/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectRealizedNativeContraction
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeContractionMap
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMapPrecomp
import MathlibExt.Topology.Category.TopCat.ProdMapPointwise

/-!
# The actual realized native contraction fixes its original basepoint

Precompose the actual original contraction with its retained basepoint.
The proved whole interval fixed equation and realization precomposition
identify it with the original constant-in-time map at that same point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

set_option backward.isDefEq.respectTransparency false in
/-- The actual original native contraction realized after its same basepoint is constant in time. -/
theorem realizedNativeContraction_stationaryMap (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map (diagonalBasepointMap W x)) ≫
        SSet.realizeHomotopyMap _ _ (SSet.const (diagonalBasepoint W x))
          (𝟙 (SSet.simplicialDiagonalFunctor.obj (diagram W x))) (nativeDiagonalPointContraction W x) =
      prod.snd ≫ SSet.toTop.map (diagonalBasepointMap W x) := by
  let H := nativeDiagonalPointContraction W x
  let k := diagonalBasepointMap W x
  have hk : k ≫ SSet.const (diagonalBasepoint W x) = k := by
    dsimp only [k]
    rw [diagonalBasepointMap_eq_const]
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  have hh : (H.precomp k).h = CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
      (k ≫ SSet.const (diagonalBasepoint W x)) := by
    have h0 : (H.precomp k).h =
        CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ k := by
      rw [SSet.Homotopy.precomp_h]
      dsimp only [H, k]
      have hw : diagonalBasepointMap W x ▷ (Δ[1] : SSet.{u}) =
          diagonalBasepointMap W x ⊗ₘ 𝟙 (Δ[1] : SSet.{u}) := by
        apply NatTrans.ext
        funext n
        apply ConcreteCategory.hom_ext
        intro z
        rfl
      rw [hw]
      rw [nativeDiagonalPointContraction_h]
      exact nativeDiagonalContraction_fixed_basepoint W x
    exact h0.trans (congrArg (fun q =>
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ q) hk).symm
  rw [SSet.realizeHomotopyMap_precomp]
  rw [SSet.realizeHomotopyMap_of_h_eq_fst (H.precomp k) hh, hk]

end SimplicialSpace.LeftDecalageObject
