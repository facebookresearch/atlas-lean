/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomMapping
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpacePi

/-!
# The exact original edge of the coherent Hom comparison

The actual right-mapping vertex of an original Hom vertex is its
represented coherent-nerve edge. Its entire enriched-simplex readback
retains the supplied individual objects and original Hom vertex. This
construction needs no Kan or comparison weak-equivalence assumption.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingEdges
open SimplicialEnrichment
variable {C : Carrier.{u}}

/-- The actual coherent-nerve edge representing a supplied individual original Hom vertex. -/
def edge (x y : C) (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    (coherentNerveFunctor.obj C).Edge (SSet.yonedaEquiv (HomSimplexEndpoints.vertex x))
      (SSet.yonedaEquiv (HomSimplexEndpoints.vertex y)) :=
  SSet.mappingSpaceRight.zeroSimplexEquivEdge _ _ _ ((HomMapping.map x y).app (op ⦋0⦌) τ)

/-- The entire represented edge is precisely the original enriched coherent simplex carrying the supplied Hom vertex. -/
theorem edge_readback (x y : C) (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    (edge x y τ).edge = HomSimplex.simplex x y (SSet.yonedaEquiv.symm τ) :=
  (congrArg (fun f => SSet.yonedaEquiv f) (HomMapping.map_readback x y τ)).trans
    (SSet.yonedaEquiv.apply_symm_apply _)

end CategoryTheory.CoherentRealization.MappingEdges
