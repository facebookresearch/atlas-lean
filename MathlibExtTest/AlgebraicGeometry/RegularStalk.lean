/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RegularStalk

/-! # Consumers for stalk regularity under open immersions -/

namespace RegularStalkTest

universe u

open CategoryTheory AlgebraicGeometry

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource {U X : Scheme.{u}} (i : U ⟶ X)
    [IsOpenImmersion i] (u : U) :
    IsRegularLocalRing (X.presheaf.stalk (i.base u)) ↔
      IsRegularLocalRing (U.presheaf.stalk u) :=
  AlgebraicGeometry.IsOpenImmersion.isRegularLocalRing_stalk_iff i u

end RegularStalkTest
