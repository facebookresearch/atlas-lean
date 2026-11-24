/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Preimages of open normal subgroups

A continuous homomorphism pulls an open normal subgroup back to an open
normal subgroup. This file packages that construction, its membership,
monotonicity, identity, and source-first composition laws, and the induced
change-of-index functor between the opposite open-normal posets.

Source, target, and intermediate group universes are independent. Only the
group structures, topologies, and bundled continuity of the homomorphisms are
used; no IsTopologicalGroup, compactness, or surjectivity assumption is
required.

## Main declarations

* OpenNormalSubgroup.comap
* OpenNormalSubgroup.mem_comap
* OpenNormalSubgroup.comap_mono
* OpenNormalSubgroup.comap_id
* OpenNormalSubgroup.comap_comp
* ContinuousCohomology.openNormalComapFunctor
* ContinuousCohomology.openNormalComapFunctor_id
* ContinuousCohomology.openNormalComapFunctor_comp
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u v w

namespace OpenNormalSubgroup

/-- Preimage of an open normal subgroup under a continuous homomorphism. -/
def comap
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (phi : H →ₜ* G) (U : OpenNormalSubgroup G) :
    OpenNormalSubgroup H where
  toOpenSubgroup := U.toOpenSubgroup.comap phi.toMonoidHom phi.continuous
  isNormal' := U.isNormal'.comap phi.toMonoidHom

/-- Membership in an open-normal preimage is literal preimage membership. -/
@[simp]
theorem mem_comap
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (phi : H →ₜ* G) (U : OpenNormalSubgroup G) (h : H) :
    h ∈ comap phi U ↔ phi h ∈ U :=
  Iff.rfl

/-- Open-normal preimage is monotone in the subgroup. -/
theorem comap_mono
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (phi : H →ₜ* G) {U V : OpenNormalSubgroup G} (hUV : U ≤ V) :
    comap phi U ≤ comap phi V := fun _ h => hUV h

/-- Preimage under the identity homomorphism is the original subgroup. -/
@[simp]
theorem comap_id
    {G : Type u} [Group G] [TopologicalSpace G]
    (U : OpenNormalSubgroup G) :
    comap (ContinuousMonoidHom.id G) U = U := by
  ext g
  rfl

/-- Open-normal preimages compose in source-first homomorphism order. -/
theorem comap_comp
    {G : Type u} {H : Type v} {K : Type w}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    [Group K] [TopologicalSpace K]
    (phi : H →ₜ* G) (psi : K →ₜ* H) (U : OpenNormalSubgroup G) :
    comap (phi.comp psi) U = comap psi (comap phi U) := by
  ext g
  rfl

end OpenNormalSubgroup

namespace ContinuousCohomology

/-- Opposite-index change of variables induced by open-normal preimage. -/
def openNormalComapFunctor
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (phi : H →ₜ* G) :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ (OpenNormalSubgroup H)ᵒᵖ where
  obj U := Opposite.op (OpenNormalSubgroup.comap phi U.unop)
  map {_U _V} f :=
    (homOfLE (OpenNormalSubgroup.comap_mono phi (leOfHom f.unop))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The open-normal preimage functor of the identity is the identity functor. -/
theorem openNormalComapFunctor_id
    {G : Type u} [Group G] [TopologicalSpace G] :
    openNormalComapFunctor (ContinuousMonoidHom.id G) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun U => ?_) ?_
  · change Opposite.op (OpenNormalSubgroup.comap
      (ContinuousMonoidHom.id G) U.unop) = U
    rw [OpenNormalSubgroup.comap_id, Opposite.op_unop]
  · intro U V f
    exact Subsingleton.elim _ _

/-- Open-normal preimage functors compose in source-first homomorphism order. -/
theorem openNormalComapFunctor_comp
    {G : Type u} {H : Type v} {K : Type w}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    [Group K] [TopologicalSpace K]
    (phi : H →ₜ* G) (psi : K →ₜ* H) :
    openNormalComapFunctor (phi.comp psi) =
      openNormalComapFunctor phi ⋙ openNormalComapFunctor psi := by
  refine CategoryTheory.Functor.ext (fun U => ?_) ?_
  · change Opposite.op (OpenNormalSubgroup.comap (phi.comp psi) U.unop) =
      Opposite.op (OpenNormalSubgroup.comap psi
        (OpenNormalSubgroup.comap phi U.unop))
    exact congrArg Opposite.op
      (OpenNormalSubgroup.comap_comp phi psi U.unop)
  · intro U V f
    exact Subsingleton.elim _ _

end ContinuousCohomology

end
