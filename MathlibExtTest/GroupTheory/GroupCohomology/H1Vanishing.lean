/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.GroupCohomology.H1Vanishing

@[expose] public section

universe v

open CategoryTheory

-- `exactSource` consumer with the original binders.
example {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hG : IsUnit ((Fintype.card G : k))) :
    Subsingleton (groupCohomology.H1 A) :=
  groupCohomology.H1.subsingleton_of_isUnit_card A hG

-- Higher-universe consumer: the coefficients and group may live in any universe.
example {k G : Type v} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hG : IsUnit ((Fintype.card G : k))) :
    Subsingleton (groupCohomology.H1 A) :=
  groupCohomology.H1.subsingleton_of_isUnit_card A hG

-- Boundary: for the trivial group the hypothesis is automatic (`#G = 1`).
example {k : Type} [CommRing k] (A : Rep k PUnit) :
    Subsingleton (groupCohomology.H1 A) :=
  groupCohomology.H1.subsingleton_of_isUnit_card A (by simp)
