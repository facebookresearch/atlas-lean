/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorSmallObject

/-!
# Relative-cell generator colimit-smallness client

Thin public inference client for the
`IsCardinalForSmallObjectArgument.preservesColimit` field at
`realizedGeneratorCardinal` for
`TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions`: a map out
of a generator domain preserves the colimit of the transfinite functor of a
`RelativeCellComplex` with the pinned shape. Inference application only; no new
proof, and no presentability, small-object, factorization, cofibration,
weak-equivalence, or model-structure claim.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Limits Topology

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatGeneratorRelativeCellSmallnessTests

universe u u_1

theorem union_preservesColimit_field_client
    {A B X Y : TopCat.{u}} (i : A ⟶ B)
    (hi : (TopCat.realizedBoundaryInclusions ⊔
      TopCat.realizedHornInclusions) i)
    (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u}
      (fun (_ : realizedGeneratorCardinal.{u}.ord.ToType) ↦
        (TopCat.realizedBoundaryInclusions ⊔
          TopCat.realizedHornInclusions).homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) :=
  (inferInstance : MorphismProperty.IsCardinalForSmallObjectArgument
    (TopCat.realizedBoundaryInclusions.{u} ⊔
      TopCat.realizedHornInclusions.{u})
    realizedGeneratorCardinal.{u}).preservesColimit i hi f hf

#print axioms union_preservesColimit_field_client

end TopCatGeneratorRelativeCellSmallnessTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
