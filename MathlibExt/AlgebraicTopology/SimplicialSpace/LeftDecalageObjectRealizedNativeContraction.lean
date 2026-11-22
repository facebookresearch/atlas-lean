/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeBasepointFixed
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy

/-!
# The realized actual original path-diagonal contraction

Realize the literal original extra-degeneracy interval homotopy. Its
endpoints are the original identity-edge constant map and the identity on
the entire original diagonal. All carried points and interval values are
the original realized cylinder values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The actual original point contraction realized as a whole continuous homotopy. -/
def realizedNativePointContraction (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    ContinuousMap.Homotopy
      (ContinuousMap.const (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x)))
        (SSet.realizedVertex (diagonalBasepoint W x)))
      (ContinuousMap.id (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj (diagram W x)))) := by
  let K := SSet.simplicialDiagonalFunctor.obj (diagram W x)
  have h := SSet.realizeHomotopy K K (SSet.const (diagonalBasepoint W x)) (𝟙 K)
    (nativeDiagonalPointContraction W x)
  have he : (SSet.toTop.map (SSet.const (diagonalBasepoint W x))).hom =
      ContinuousMap.const (SSet.toTop.obj K) (SSet.realizedVertex (diagonalBasepoint W x)) := by
    apply ContinuousMap.ext
    intro z
    have hf : (SSet.const (diagonalBasepoint W x) : K ⟶ K) =
        SSet.stdSimplex.isTerminalObj₀.from K ≫ SSet.yonedaEquiv.symm (diagonalBasepoint W x) := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    rw [hf, SSet.toTop.map_comp, SSet.toTop_map_point]
    rfl
  rw [he, SSet.toTop.map_id] at h
  exact h

end SimplicialSpace.LeftDecalageObject
