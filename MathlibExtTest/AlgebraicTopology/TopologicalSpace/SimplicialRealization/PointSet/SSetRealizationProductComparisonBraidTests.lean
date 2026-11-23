/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationProductComparisonBraid

@[expose] public section

/-!
# Braid-transfer client test

Minimal direct-import client for `SSetRealizationProductComparisonBraid`.
Universe-polymorphic explicit witness that the swapped iso follows from the
ordered iso by explicit `SSet.isIso_prodComparison_swap` application, without
cyclic typeclass search.
No arbitrary-product preservation, no finite-product theorem,
no weak-equivalence, and no model-category claim.
-/

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace SSetRealizationProductComparisonBraidTests

theorem swap_client (K L : SSet.{u})
    [IsIso (Limits.prodComparison SSet.toTop K L)] :
    IsIso (Limits.prodComparison SSet.toTop L K) :=
  SSet.isIso_prodComparison_swap K L

#print axioms SSet.isIso_prodComparison_swap
#print axioms swap_client

end SSetRealizationProductComparisonBraidTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
