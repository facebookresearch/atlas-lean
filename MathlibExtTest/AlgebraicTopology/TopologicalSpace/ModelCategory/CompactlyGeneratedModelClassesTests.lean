/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedModelClasses

/-!
# Tests for model classes on compactly generated spaces

These owners verify that all three properties are literal inverse images of
the selected `TopCat` classes, including mixed probe/carrier universes.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty

universe u v

namespace MathlibExtTest.CompactlyGeneratedModelClasses

#check @CompactlyGenerated.weakHomotopyEquivalences
#check @CompactlyGenerated.modelCofibrations
#check @CompactlyGenerated.modelFibrations

section Symbolic

variable {X Y : CompactlyGenerated.{u, v}} (f : X ⟶ Y)

example : CompactlyGenerated.weakHomotopyEquivalences f ↔
    TopCat.weakHomotopyEquivalences
      (CompactlyGenerated.compactlyGeneratedToTop.map f) :=
  Iff.rfl

example : CompactlyGenerated.modelCofibrations f ↔
    TopCat.realizedBoundaryInclusions.rlp.llp
      (CompactlyGenerated.compactlyGeneratedToTop.map f) :=
  Iff.rfl

example : CompactlyGenerated.modelFibrations f ↔
    TopCat.realizedHornInclusions.rlp
      (CompactlyGenerated.compactlyGeneratedToTop.map f) :=
  Iff.rfl

example : CompactlyGenerated.weakHomotopyEquivalences.{u, v} =
    TopCat.weakHomotopyEquivalences.{v}.inverseImage
      CompactlyGenerated.compactlyGeneratedToTop.{u, v} := rfl

example : CompactlyGenerated.modelCofibrations.{u, v} =
    TopCat.realizedBoundaryInclusions.{v}.rlp.llp.inverseImage
      CompactlyGenerated.compactlyGeneratedToTop.{u, v} := rfl

example : CompactlyGenerated.modelFibrations.{u, v} =
    TopCat.realizedHornInclusions.{v}.rlp.inverseImage
      CompactlyGenerated.compactlyGeneratedToTop.{u, v} := rfl

end Symbolic

section UniverseMatrix

#check @CompactlyGenerated.weakHomotopyEquivalences.{0, 0}
#check @CompactlyGenerated.modelCofibrations.{0, 0}
#check @CompactlyGenerated.modelFibrations.{0, 0}

#check @CompactlyGenerated.weakHomotopyEquivalences.{1, 1}
#check @CompactlyGenerated.modelCofibrations.{1, 1}
#check @CompactlyGenerated.modelFibrations.{1, 1}

#check @CompactlyGenerated.weakHomotopyEquivalences.{0, 1}
#check @CompactlyGenerated.modelCofibrations.{0, 1}
#check @CompactlyGenerated.modelFibrations.{0, 1}

#check @CompactlyGenerated.weakHomotopyEquivalences.{1, 0}
#check @CompactlyGenerated.modelCofibrations.{1, 0}
#check @CompactlyGenerated.modelFibrations.{1, 0}

end UniverseMatrix

#print axioms CompactlyGenerated.weakHomotopyEquivalences
#print axioms CompactlyGenerated.modelCofibrations
#print axioms CompactlyGenerated.modelFibrations

end MathlibExtTest.CompactlyGeneratedModelClasses
