/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClasses

/-!
# Tests for model classes on CGWH spaces

These owners verify that all three properties are literal inverse images
through the immediate inclusion into compactly generated spaces, including
mixed probe/carrier universes and the absence of a model instance.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty

universe u v

namespace MathlibExtTest.CGWHModelClasses

#check @CGWH.weakHomotopyEquivalences
#check @CGWH.modelCofibrations
#check @CGWH.modelFibrations

section Symbolic

variable {X Y : CGWH.{u, v}} (f : X ⟶ Y)

example : CGWH.weakHomotopyEquivalences f ↔
    CompactlyGenerated.weakHomotopyEquivalences
      (CGWH.cgwhToCompactlyGenerated.map f) :=
  Iff.rfl

example : CGWH.modelCofibrations f ↔
    CompactlyGenerated.modelCofibrations
      (CGWH.cgwhToCompactlyGenerated.map f) :=
  Iff.rfl

example : CGWH.modelFibrations f ↔
    CompactlyGenerated.modelFibrations
      (CGWH.cgwhToCompactlyGenerated.map f) :=
  Iff.rfl

example : CGWH.weakHomotopyEquivalences.{u, v} =
    CompactlyGenerated.weakHomotopyEquivalences.{u, v}.inverseImage
      CGWH.cgwhToCompactlyGenerated.{u, v} := rfl

example : CGWH.modelCofibrations.{u, v} =
    CompactlyGenerated.modelCofibrations.{u, v}.inverseImage
      CGWH.cgwhToCompactlyGenerated.{u, v} := rfl

example : CGWH.modelFibrations.{u, v} =
    CompactlyGenerated.modelFibrations.{u, v}.inverseImage
      CGWH.cgwhToCompactlyGenerated.{u, v} := rfl

example : True := by
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory CGWH.{u, v} := inferInstance
  trivial

end Symbolic

section UniverseMatrix

#check @CGWH.weakHomotopyEquivalences.{0, 0}
#check @CGWH.modelCofibrations.{0, 0}
#check @CGWH.modelFibrations.{0, 0}

#check @CGWH.weakHomotopyEquivalences.{1, 1}
#check @CGWH.modelCofibrations.{1, 1}
#check @CGWH.modelFibrations.{1, 1}

#check @CGWH.weakHomotopyEquivalences.{0, 1}
#check @CGWH.modelCofibrations.{0, 1}
#check @CGWH.modelFibrations.{0, 1}

#check @CGWH.weakHomotopyEquivalences.{1, 0}
#check @CGWH.modelCofibrations.{1, 0}
#check @CGWH.modelFibrations.{1, 0}

end UniverseMatrix

#print axioms CGWH.weakHomotopyEquivalences
#print axioms CGWH.modelCofibrations
#print axioms CGWH.modelFibrations

end MathlibExtTest.CGWHModelClasses
