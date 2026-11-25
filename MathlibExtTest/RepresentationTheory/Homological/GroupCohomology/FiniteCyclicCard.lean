/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.FiniteCyclicCard

@[expose] public section

open CategoryTheory groupCohomology

universe u

-- Consumer with the original binders.
example {G : Type} [Group G] [Finite G] [IsCyclic G] (A : Rep ℤ G) [Finite A] :
    Finite (H1 A) ∧ Finite (H2 A) ∧ Nat.card (H1 A) = Nat.card (H2 A) :=
  groupCohomology.natCard_H1_eq_natCard_H2_of_finite A

-- Higher-universe consumer.
example {k : Type u} [CommRing k] {G : Type u} [Group G] [Finite G] [IsCyclic G]
    (A : Rep k G) [Finite A] :
    Finite (H1 A) ∧ Finite (H2 A) ∧ Nat.card (H1 A) = Nat.card (H2 A) :=
  groupCohomology.natCard_H1_eq_natCard_H2_of_finite A

-- Boundary use: the finiteness conclusions can be fed back as instances.
example {G : Type} [Group G] [Finite G] [IsCyclic G] (A : Rep ℤ G) [Finite A] :
    Finite (H1 A) ∧ Finite (H2 A) :=
  ⟨(groupCohomology.natCard_H1_eq_natCard_H2_of_finite A).1,
    (groupCohomology.natCard_H1_eq_natCard_H2_of_finite A).2.1⟩
