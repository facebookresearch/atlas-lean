/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FunctorMapCongruence

@[expose] public section

set_option autoImplicit false

universe uV vV uC uD

open CategoryTheory

namespace MathlibExtTest.CategoryTheory.Enriched.FunctorMapCongruence

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} {D : Type uD}
  [EnrichedCategory V C] [EnrichedCategory V D]

#check @EnrichedFunctor.map_heq_of_eq

section UniverseCorners

#check @EnrichedFunctor.map_heq_of_eq.{0, 0, 0, 0}
#check @EnrichedFunctor.map_heq_of_eq.{1, 0, 0, 1}
#check @EnrichedFunctor.map_heq_of_eq.{0, 1, 1, 0}
#check @EnrichedFunctor.map_heq_of_eq.{1, 1, 0, 1}

end UniverseCorners

example : True := by
  fail_if_success exact inferInstanceAs (Category C)
  fail_if_success exact inferInstanceAs (Category D)
  trivial

example (F G : EnrichedFunctor V C D) (h : F = G) (a b : C) :
    F.map a b ≍ G.map a b := EnrichedFunctor.map_heq_of_eq F G h a b

example (F G : EnrichedFunctor V C D) (h : F = G) (a b : C) :
    HEq
      (F.map a b : (a ⟶[V] b) ⟶ (F.obj a ⟶[V] F.obj b))
      (G.map a b : (a ⟶[V] b) ⟶ (G.obj a ⟶[V] G.obj b)) :=
  EnrichedFunctor.map_heq_of_eq F G h a b

example (F : EnrichedFunctor V C D) (a b : C) :
    F.map a b ≍ F.map a b := EnrichedFunctor.map_heq_of_eq F F rfl a b

#print axioms EnrichedFunctor.map_heq_of_eq

end MathlibExtTest.CategoryTheory.Enriched.FunctorMapCongruence
