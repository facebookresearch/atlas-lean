/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Limits.Shapes.BiproductFunctor

/-!
# Consumer tests for the bare biproduct functor

Minimal compile-level checks for `CategoryTheory.Limits.biprodFunctor`:
object inference on a pair, one projection computation, and one inclusion
computation. Proofs reuse the public functor lemmas directly.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace MathlibExtTest.CategoryTheory.BiproductFunctorTests

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

example (X : C × C) : (biprodFunctor C).obj X = (X.1 ⊞ X.2) :=
  biprodFunctor_obj C X

example {X Y : C × C} (f : X ⟶ Y) :
    (biprodFunctor C).map f ≫ biprod.fst = biprod.fst ≫ f.1 :=
  biprodFunctor_map_fst C f

example {X Y : C × C} (f : X ⟶ Y) :
    biprod.inl ≫ (biprodFunctor C).map f = f.1 ≫ biprod.inl :=
  biprodFunctor_inl_map C f

end MathlibExtTest.CategoryTheory.BiproductFunctorTests
