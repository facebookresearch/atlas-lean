/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonFinite

@[expose] public section

/-!
# Finite-by-finite product comparison client

Thin public-signature check for `SSet.isIso_prodComparison_toTop_finite_finite`.

Explicit nonclaims: proves no new comparison, limit, or colimit fact; no
arbitrary-product preservation, no weak-equivalence, no fibration, no
cofibration, no DeltaGenerated-space result, and no model-category result;
does not duplicate the finite-cell induction and adds no symmetric second
theorem.
-/

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

namespace MathlibExtTest
namespace AlgebraicTopology
namespace ModelCategory
namespace SSetRealizationFiniteProductComparisonFiniteTests

theorem finite_finite_client (K L : SSet.{0}) [K.Finite] [L.Finite] :
    IsIso (Limits.prodComparison SSet.toTop K L) :=
  SSet.isIso_prodComparison_toTop_finite_finite K L

#check SSet.isIso_prodComparison_toTop_finite_finite
#check finite_finite_client
#print axioms SSet.isIso_prodComparison_toTop_finite_finite
#print axioms finite_finite_client

end SSetRealizationFiniteProductComparisonFiniteTests
end ModelCategory
end AlgebraicTopology
end MathlibExtTest
