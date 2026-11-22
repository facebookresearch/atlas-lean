/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedGenerators
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Model classes on compactly generated spaces

This file defines the three morphism properties selected for the future
model structure on compactly generated spaces. Each property is created by
the fully faithful inclusion into `TopCat`.

No factorization, weak factorization system, model-category instance, or
Quillen result is installed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty

universe u v

namespace CompactlyGenerated

/-- Weak homotopy equivalences of compactly generated spaces are created by
the inclusion into topological spaces. -/
def weakHomotopyEquivalences :
    MorphismProperty CompactlyGenerated.{u, v} :=
  TopCat.weakHomotopyEquivalences.{v}.inverseImage
    compactlyGeneratedToTop.{u, v}

/-- The selected cofibrations of compactly generated spaces are created by
the inclusion into topological spaces. -/
noncomputable def modelCofibrations :
    MorphismProperty CompactlyGenerated.{u, v} :=
  TopCat.realizedBoundaryInclusions.{v}.rlp.llp.inverseImage
    compactlyGeneratedToTop.{u, v}

/-- The selected fibrations of compactly generated spaces are created by
the inclusion into topological spaces. -/
noncomputable def modelFibrations :
    MorphismProperty CompactlyGenerated.{u, v} :=
  TopCat.realizedHornInclusions.{v}.rlp.inverseImage
    compactlyGeneratedToTop.{u, v}

end CompactlyGenerated
