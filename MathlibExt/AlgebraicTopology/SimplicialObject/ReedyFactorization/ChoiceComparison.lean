/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyFactorization.Historical
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyFactorization

/-!
# The simplex factorization used in the historical Reedy tower

The historical tower and the generic Reedy construction use the same factorization of a
simplex operator. This comparison is of the entire epi–mono factorization, including
its image object and both arrows; it does not compare the two towers' chosen middle objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.ReedyR4OneDegreeFunctorPreflight

/-- The simplex-operator factorization used by the historical choice equals the native Reedy
factorization, including its selected intermediate simplex and its epi and mono maps. -/
theorem canonicalSimplexFactor_eq_native {a b : ℕ} (g : op ⦋a⦌ ⟶ op ⦋b⦌) :
    canonicalSimplexFactor g = SimplexCategory.reedyStructure.mapFactorizationData g.unop :=
  Subsingleton.elim _ _

end CategoryTheory.SimplicialObject.ReedyR4OneDegreeFunctorPreflight
