/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Symmetry of the realization product comparison

If the product comparison for `SSet.toTop` at `K` and `L` is an
isomorphism, the comparison at `L` and `K` is an isomorphism as well.
`isIso_prodComparison_swap` transports the given isomorphism along the
product braidings using `Limits.map_braiding_hom_comp_prodComparison`.
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
