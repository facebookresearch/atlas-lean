/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.Core

/-!
# The equivalence-edge core functor

The native restriction `SSet.core.map`, together with its identity and
composition laws, defines a functor on all simplicial sets.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace SSet

/-- The equivalence-edge core functor on all simplicial sets, with its
literal native core objects and restricted maps. -/
@[implicit_reducible, simps obj map]
def coreFunctor : SSet.{u} ⥤ SSet.{u} where
  obj X := (core X : SSet.{u})
  map f := core.map f
  map_id X := core.map_id X
  map_comp f g := core.map_comp f g

end SSet
