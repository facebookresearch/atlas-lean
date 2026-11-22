/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectRealizedNativeFixed
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectRealizedContractionMap

/-!
# The actual original based path-diagonal contraction

The original realized interval homotopy fixes the retained identity-edge
point at every time. Reversing that same homotopy gives the actual based
contraction used for the native edge-loop comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The actual native realized point contraction fixes the original identity-edge point at every time. -/
theorem realizedNativePointContraction_fixed (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (t : unitInterval) :
    realizedNativePointContraction W x (t, SSet.realizedVertex (diagonalBasepoint W x)) =
      SSet.realizedVertex (diagonalBasepoint W x) := by
  let K := SSet.simplicialDiagonalFunctor.obj (diagram W x)
  let k := diagonalBasepointMap W x
  let p0 := (TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj (Δ[0] : SSet.{u}))).inv
    (TopCat.I.homeomorph.symm t, (default : SSet.toTop.obj (Δ[0] : SSet.{u})))
  have hk : SSet.toTop.map k (default : SSet.toTop.obj (Δ[0] : SSet.{u})) =
      SSet.realizedVertex (diagonalBasepoint W x) := by
    have he : k = SSet.yonedaEquiv.symm (diagonalBasepoint W x) := by
      exact (SSet.yonedaEquiv.symm_apply_apply _).symm
    rw [he]
    rfl
  have hp : (prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k)) p0 =
      (TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj K)).inv
        (TopCat.I.homeomorph.symm t, SSet.realizedVertex (diagonalBasepoint W x)) := by
    dsimp [p0]
    rw [TopCat.prodMap_prodIso_inv_apply, hk]
  have h := ConcreteCategory.congr_hom (realizedNativeContraction_stationaryMap W x) p0
  rw [realizedNativePointContraction_apply]
  change SSet.realizeHomotopyMap K K (SSet.const (diagonalBasepoint W x)) (𝟙 K)
    (nativeDiagonalPointContraction W x)
      ((TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj K)).inv
        (TopCat.I.homeomorph.symm t, SSet.realizedVertex (diagonalBasepoint W x))) = _
  rw [← hp]
  have hv : SSet.toTop.map k
      ((prod.snd : TopCat.I.{u} ⨯ SSet.toTop.obj (Δ[0] : SSet.{u}) ⟶
        SSet.toTop.obj (Δ[0] : SSet.{u})) p0) = SSet.realizedVertex (diagonalBasepoint W x) := by
    dsimp [p0]
    rw [TopCat.prodIsoProd_inv_snd_apply]
    exact hk
  exact h.trans hv

/-- The same original interval homotopy reversed gives the actual native based contraction. -/
def nativeBasedContraction (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.BasedContraction (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x)))
      (SSet.realizedVertex (diagonalBasepoint W x)) where
  homotopy := (realizedNativePointContraction W x).symm
  fixed t := realizedNativePointContraction_fixed W x (unitInterval.symm t)

end SimplicialSpace.LeftDecalageObject
