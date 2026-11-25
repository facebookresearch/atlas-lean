/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Braid transfer for the SSet realization product comparison

KQ3 only. Universe-polymorphic SSet realization specificity throughout.

For `K L : SSet.{u}`, an `IsIso` hypothesis for
`Limits.prodComparison SSet.toTop K L` yields an `IsIso` proof for the
swapped comparison `Limits.prodComparison SSet.toTop L K`, via the categorical
product braiding on both sides and the pinned
`Limits.map_braiding_hom_comp_prodComparison`. No symmetry preservation is assumed; the swapped iso
is transported along the braiding isomorphisms.

Explicit nonclaims: no arbitrary-functor generality, no finite-product
preservation, no weak-equivalence, and no model-category result.
-/

@[expose] public section

open CategoryTheory Limits Simplicial

universe u

namespace SSet

/-- Swapped product comparison iso from the ordered iso, via product braids. -/
theorem isIso_prodComparison_swap (K L : SSet.{u})
    [IsIso (Limits.prodComparison SSet.toTop K L)] :
    IsIso (Limits.prodComparison SSet.toTop L K) :=
  IsIso.of_isIso_fac_left
    (Limits.map_braiding_hom_comp_prodComparison SSet.toTop (A := L) (B := K))

end SSet
