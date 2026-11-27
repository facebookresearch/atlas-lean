/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.GroupCohomology.TateCardinality

open CategoryTheory

/-- Consumer with the original binders, restated in Mathlib style. -/
example {G : Type} [Group G] [Finite G]
    (X : Rep ℤ G) (u : groupCohomology X 2) (hu : addOrderOf u = Nat.card G)
    (h5 : ∀ (S : Subgroup G) [Fintype S],
      Finite (groupCohomology (Rep.res S.subtype X) 2) ∧
      Nat.card (groupCohomology (Rep.res S.subtype X) 2) ≤ Fintype.card S)
    (cor : ∀ S : Subgroup G,
      groupCohomology (Rep.res S.subtype X) 2 →ₗ[ℤ] groupCohomology X 2)
    (hcor : ∀ (S : Subgroup G) (x : groupCohomology X 2),
      cor S ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x) =
        S.index • x) :
    (∀ (S : Subgroup G) [Fintype S],
      Nat.card (groupCohomology (Rep.res S.subtype X) 2) = Fintype.card S) ∧
    (∀ S : Subgroup G, Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom u} = ⊤) :=
  groupCohomology.natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard X u hu h5 cor hcor

