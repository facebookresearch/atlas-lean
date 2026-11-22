/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHGenerators
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedModelClasses

/-!
# Model classes on CGWH spaces

This file defines the three morphism properties selected for the future
model structure on compactly generated weak Hausdorff spaces. Each property
is created by the immediate fully faithful inclusion into compactly
generated spaces.

No composite comparison with `TopCat`, factorization, weak factorization
system, model-category instance, or Quillen result is installed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty

universe u v

namespace CGWH

/-- Weak homotopy equivalences of CGWH spaces are created by the immediate
inclusion into compactly generated spaces. -/
def weakHomotopyEquivalences : MorphismProperty CGWH.{u, v} :=
  CompactlyGenerated.weakHomotopyEquivalences.{u, v}.inverseImage
    cgwhToCompactlyGenerated.{u, v}

/-- The selected cofibrations of CGWH spaces are created by the immediate
inclusion into compactly generated spaces. -/
noncomputable def modelCofibrations : MorphismProperty CGWH.{u, v} :=
  CompactlyGenerated.modelCofibrations.{u, v}.inverseImage
    cgwhToCompactlyGenerated.{u, v}

/-- The selected fibrations of CGWH spaces are created by the immediate
inclusion into compactly generated spaces. -/
noncomputable def modelFibrations : MorphismProperty CGWH.{u, v} :=
  CompactlyGenerated.modelFibrations.{u, v}.inverseImage
    cgwhToCompactlyGenerated.{u, v}

end CGWH
