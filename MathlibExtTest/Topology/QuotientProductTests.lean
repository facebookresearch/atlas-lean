/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.QuotientProduct

@[expose] public section

/-!
# Quotient-product kernel signature clients

Minimal clients for `Topology.IsQuotientMap.prodMap_left`,
`.prodMap_right`, and `.prodMap_prod`: one-sided products with the identity on
a locally compact fixed factor preserve quotient maps, and the two-quotient
product does so under local compactness of the intermediate factors `C`
(right source) and `B` (left target). Arbitrary products of quotient maps
without those hypotheses are not proved here.
-/

set_option autoImplicit false

/-- Quotient on the left, identity on a locally compact right factor. -/
example {A B K : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace K] [LocallyCompactSpace K]
    {q : A → B} (hq : Topology.IsQuotientMap q) :
    Topology.IsQuotientMap (Prod.map q (id : K → K)) :=
  hq.prodMap_left

/-- Identity on a locally compact left factor, quotient on the right. -/
example {A B K : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace K] [LocallyCompactSpace K]
    {q : A → B} (hq : Topology.IsQuotientMap q) :
    Topology.IsQuotientMap (Prod.map id q : K × A → K × B) :=
  hq.prodMap_right

/-- Product of two quotient maps under intermediate-factor local compactness. -/
theorem prodMap_prod_client {A B C D : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    [LocallyCompactSpace C] [LocallyCompactSpace B]
    {q : A → B} {r : C → D} (hq : Topology.IsQuotientMap q)
    (hr : Topology.IsQuotientMap r) :
    Topology.IsQuotientMap (Prod.map q r) :=
  hq.prodMap_prod hr

#check @Topology.IsQuotientMap.prodMap_prod
#print axioms Topology.IsQuotientMap.prodMap_left
#print axioms Topology.IsQuotientMap.prodMap_right
#print axioms Topology.IsQuotientMap.prodMap_prod
#print axioms prodMap_prod_client
