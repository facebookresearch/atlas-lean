/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialCofree
public import MathlibExt.CategoryTheory.Functor.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Enough injectives for inverse sequences

If C has finite limits and enough injectives, then the category of inverse
sequences ℕᵒᵖ → C has enough injectives. Pointwise injective presentations give
a discrete family, and its right Kan extension supplies the injective target.
The finite-prefix product description and preservation of monomorphisms by
restriction supply the embedding. The object and morphism universes remain
independent.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

namespace Limits

/-- Finite limits and enough injectives in C give enough injectives in the category of inverse
sequences ℕᵒᵖ ⥤ C. -/
theorem enoughInjectives_sequential [HasFiniteLimits C] [EnoughInjectives C] :
    EnoughInjectives (ℕᵒᵖ ⥤ C) := by
  have : EnoughInjectives (Discrete ℕᵒᵖ ⥤ C) := enoughInjectives_discrete ℕᵒᵖ
  have : (sequentialRestriction C).PreservesMonomorphisms := inferInstance
  exact EnoughInjectives.of_adjunction (sequentialDiscreteInclusion.ranAdjunction C)

end Limits
end CategoryTheory
