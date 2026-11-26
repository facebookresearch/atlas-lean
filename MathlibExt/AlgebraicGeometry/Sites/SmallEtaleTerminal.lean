/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The terminal object of the small étale category

For a scheme X, the object represented by its identity morphism id_X : X → X is terminal in
X.Etale. Every étale object Y → X has its structure morphism as the unique arrow to this
identity object.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (X : Scheme.{u})

/-- For a scheme X of universe u, Scheme.Etale.mk(id_X) is a terminal object of X.Etale. The
unique morphism from an étale object Y → X is its structure morphism to X, regarded as a
morphism over X. -/
def identityEtaleIsTerminal :
    IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  by
    letI : MorphismProperty.ContainsIdentities (@AlgebraicGeometry.Etale.{u}) :=
      ⟨fun Y => inferInstanceAs (Etale (𝟙 Y))⟩
    exact MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale.{u}) X

end AlgebraicGeometry.Scheme.DerivedSections
