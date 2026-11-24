/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.BoundaryRLPSingularRLP
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject

/-!
# Realized simplicial monomorphisms have boundary LLP

The realization of an arbitrary simplicial monomorphism has the left lifting
property against every topological map with right lifting property against the
realized boundary inclusions.  The proof transports the lifting problem across
the realization--singular adjunction and uses the boundary small-object
identity `I.rlp.llp = monomorphisms` in simplicial sets.

This is a property-level adapter only.  It installs no model-category or
cofibrancy instance and makes no left-properness or weak-equivalence claim.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u

namespace SSet

/-- Realization sends every simplicial monomorphism into the left class of the
realized-boundary weak factorization system. -/
theorem toTop_map_mem_realizedBoundaryLLP
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    TopCat.realizedBoundaryInclusions.rlp.llp (SSet.toTop.map f) := by
  have hf : modelCategoryQuillen.I.rlp.llp f := by
    rw [modelCategoryQuillen.llp_rlp_I]
    infer_instance
  intro A B p hp
  apply (sSetTopAdj.hasLiftingProperty_iff f p).mpr
  apply hf
  intro K L i hi
  exact TopCat.boundaryRLP_toSSet_mem_I_rlp hp hi

end SSet

end
