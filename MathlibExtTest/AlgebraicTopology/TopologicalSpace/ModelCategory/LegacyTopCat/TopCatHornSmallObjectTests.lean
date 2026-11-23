/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornSmallObject

@[expose] public section

/-!
# Realized horn small-object client

Minimal public client for `TopCatHornSmallObject`: Lean infers the
`IsCardinalForSmallObjectArgument` and `HasSmallObjectArgument` instances
for realized horn inclusions at `realizedGeneratorCardinal`.
No further claim is made here.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace TopCatHornSmallObjectTests

universe u

#check (inferInstance :
    CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
      TopCat.realizedHornInclusions.{u} realizedGeneratorCardinal.{u})
#synth CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
  TopCat.realizedHornInclusions.{u} realizedGeneratorCardinal.{u}

#check (inferInstance :
    CategoryTheory.MorphismProperty.HasSmallObjectArgument.{u}
      TopCat.realizedHornInclusions.{u})
#synth CategoryTheory.MorphismProperty.HasSmallObjectArgument.{u}
  TopCat.realizedHornInclusions.{u}

theorem hornCardinal_client :
    CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
      TopCat.realizedHornInclusions.{u} realizedGeneratorCardinal.{u} :=
  inferInstance

theorem hornSmallObject_client :
    CategoryTheory.MorphismProperty.HasSmallObjectArgument.{u}
      TopCat.realizedHornInclusions.{u} :=
  inferInstance

theorem hornOne_mem_client (i : Fin 2) :
    TopCat.realizedHornInclusions.{u} (SSet.toTop.map (SSet.horn 1 i).ι) := by
  have : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  exact TopCat.horn_mem_realizedHornInclusions 1 i

#print axioms hornCardinal_client
#print axioms hornSmallObject_client
#print axioms hornOne_mem_client

end TopCatHornSmallObjectTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
