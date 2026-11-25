/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # The terminal object of the original small étale category -/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (X : Scheme.{u})

/-- The literal identity morphism is terminal in the original small étale site. -/
def identityEtaleIsTerminal :
    IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  by
    letI : MorphismProperty.ContainsIdentities (@AlgebraicGeometry.Etale.{u}) :=
      ⟨fun Y => inferInstanceAs (Etale (𝟙 Y))⟩
    exact MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale.{u}) X

end AlgebraicGeometry.Scheme.DerivedSections
