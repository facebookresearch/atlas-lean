/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Reflection
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Limits in compactly generated weak Hausdorff spaces

Same-carrier-universe limits are available through an opt-in scope.  The
instance has low priority so the explicit native product providers remain the
canonical product route even when this scope is open.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CGWH.limits

/-- CGWH spaces have same-carrier-universe limits, opt-in through
`CGWH.limits`. -/
noncomputable scoped instance (priority := 100) instHasLimitsOfSize :
    HasLimitsOfSize.{v, v} CGWH.{u, v} := by
  let _ : HasLimitsOfSize.{v, v} CompactlyGenerated.{u, v} :=
    CategoryTheory.hasLimits_of_coreflective
      CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  exact CategoryTheory.hasLimits_of_reflective
    CGWH.cgwhToCompactlyGenerated.{u, v}

end CGWH.limits
