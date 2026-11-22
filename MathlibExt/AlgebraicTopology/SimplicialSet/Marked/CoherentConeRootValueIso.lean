/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentFreeEmptyValue

/-!
# Actual root and upper values of the original root-cell square

At the original root the two free identity extensions are precisely the
native free self-value projection isomorphisms. At every larger original
vertex the two free root sources are genuinely initial, and the positive
maximum inclusion is the actual whole marked upper-value isomorphism.
These concrete maps prove the pointwise attachment geometry without
supplying a projective-class or colimit outcome.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual original root identity extension component is its whole native free self-value projection. -/
theorem coneRootFreeMap_self (n : ℕ) :
    (coneRootFreeMap.{u} n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) =
      (coherentFreeSelfValueIso (⊥ : Vertex.{u} n) (coneWeight (⊥ : Vertex.{u} n))).hom := by
  apply (cancel_epi (coherentFreeSelfValueIso (⊥ : Vertex.{u} n) (coneWeight (⊥ : Vertex.{u} n))).inv).mp
  exact (coneRootFreeMap_unit n).trans
    (coherentFreeSelfValueIso (⊥ : Vertex.{u} n) (coneWeight (⊥ : Vertex.{u} n))).inv_hom_id.symm

/-- The actual positive-maximum root identity extension component is precisely its native free self-value projection. -/
theorem coneAfterRootFreeMap_self (n : ℕ) :
    (coneAfterRootFreeMap.{u} n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n))) =
      (coherentFreeSelfValueIso (⊥ : Vertex.{u} n) (coneAfterWeight (⊥ : Vertex.{u} n) ⊥)).hom := by
  apply (cancel_epi (coherentFreeSelfValueIso (⊥ : Vertex.{u} n) (coneAfterWeight (⊥ : Vertex.{u} n) ⊥)).inv).mp
  exact (coneAfterRootFreeMap_unit n).trans
    (coherentFreeSelfValueIso (⊥ : Vertex.{u} n) (coneAfterWeight (⊥ : Vertex.{u} n) ⊥)).inv_hom_id.symm

/-- Both actual original root identity components are genuine marked isomorphisms, using their unchanged
  native unit inverses. -/
theorem coneRootFreeMap_isIso_self (n : ℕ) :
    IsIso ((coneRootFreeMap.{u} n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) :=
  (coneRootFreeMap_self n).symm ▸ (coherentFreeSelfValueIso (⊥ : Vertex.{u} n)
    (coneWeight (⊥ : Vertex.{u} n))).isIso_hom

/-- The whole positive-maximum root identity component is a genuine marked isomorphism, not a chosen
  equivalent source. -/
theorem coneAfterRootFreeMap_isIso_self (n : ℕ) :
    IsIso ((coneAfterRootFreeMap.{u} n).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} n)))) :=
  (coneAfterRootFreeMap_self n).symm ▸ (coherentFreeSelfValueIso (⊥ : Vertex.{u} n)
    (coneAfterWeight (⊥ : Vertex.{u} n) ⊥)).isIso_hom

end SSet.Marked.CoherentWeight
