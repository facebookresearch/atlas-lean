/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AffineOpenRegularStalk

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

-- Consumer with the original binders.
example {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (hreg : IsRegularRing Γ(X, U)) (x : X) (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  hU.isRegularLocalRing_stalk_of_isRegularRing hreg x hx

-- Higher-universe consumer.
example {X : Scheme.{v}} {U : X.Opens} (hU : IsAffineOpen U)
    (hreg : IsRegularRing Γ(X, U)) (x : X) (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  hU.isRegularLocalRing_stalk_of_isRegularRing hreg x hx
