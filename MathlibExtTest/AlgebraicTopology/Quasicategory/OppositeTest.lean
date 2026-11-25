/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.Opposite

/-!
# Tests for opposite quasicategories and equivalence edges
-/

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

example {X Y : SSet.{u}} {q : X ⟶ Y} [InnerFibration q] :
    InnerFibration (opFunctor.map q) :=
  InnerFibration.op

example {X : SSet.{u}} [Quasicategory X]
    {x₀ x₁ : X _⦋0⦌} {e : Edge x₀ x₁}
    (h : e.IsEquivalence) : e.op.IsEquivalence :=
  h.op

example {X : SSet.{u}} [Quasicategory X.op]
    {x₀ x₁ : X.op _⦋0⦌} {e : Edge x₀ x₁}
    (h : e.IsEquivalence) : e.unop.IsEquivalence :=
  h.unop

end SSet
