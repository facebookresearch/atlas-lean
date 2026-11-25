/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexQuotient

/-!
# Subcomplex quotient consumer tests

Compile-time checks for the quotient's collapse, descent, extensionality, and
finite-instance API as used by downstream model-category code.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SubcomplexQuotientTests

variable {X T : SSet.{u}} (A : X.Subcomplex)

example : A.pointToQuotient = SSet.const A.quotient₀ := by
  simp

example : A.ι ≫ A.toQuotient = SSet.const A.quotient₀ := by
  simp

variable (f : X ⟶ T) (t₀ : T _⦋0⦌) (hf : A.ι ≫ f = SSet.const t₀)

example : A.toQuotient ≫ A.descQuotient f t₀ hf = f := by
  simp

example : (A.descQuotient f t₀ hf).app _ A.quotient₀ = t₀ := by
  simp

example {g h : A.quotient ⟶ T}
    (hX : A.toQuotient ≫ g = A.toQuotient ≫ h)
    (hpt : g.app _ A.quotient₀ = h.app _ A.quotient₀) : g = h :=
  A.quotient_hom_ext hX hpt

example [X.Finite] : A.quotient.Finite := inferInstance

#print axioms SSet.Subcomplex.ι_quotient
#print axioms SSet.Subcomplex.toQuotient_descQuotient
#print axioms SSet.Subcomplex.descQuotient_app_quotient₀
#print axioms SSet.Subcomplex.quotient_hom_ext

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SubcomplexQuotientTests
