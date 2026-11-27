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
# Open normal subgroup preimages and reverse-inclusion indices

A continuous group homomorphism `φ : H → G` sends an open normal subgroup `U≤G` to its preimage
`φ⁻¹(U)`, an open normal subgroup of `H`. Preimages are monotone, preserve identity maps and
satisfy `(φ∘ψ)⁻¹(U)=ψ⁻¹(φ⁻¹(U))`.

They define the corresponding functor on opposite inclusion posets of open normal subgroups.
Groups need only their topologies and bundled homomorphism continuity; compactness, surjectivity
or continuity of group operations is not required.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u v w

namespace OpenNormalSubgroup

/-- **Open normal subgroup preimage under a continuous homomorphism.** Let `G,H` be groups
with topologies and `φ : H →ₜ* G` a continuous homomorphism. for an open normal subgroup
`U≤G`, `comap φ U=φ⁻¹(U)` is an open normal subgroup of `H`. -/
def comap
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (phi : H →ₜ* G) (U : OpenNormalSubgroup G) :
    OpenNormalSubgroup H where
  toOpenSubgroup := U.toOpenSubgroup.comap phi.toMonoidHom phi.continuous
  isNormal' := U.isNormal'.comap phi.toMonoidHom

/-- **Membership in a continuous open-normal preimage.** Let `G,H` be groups with topologies
and `φ : H →ₜ* G` a continuous homomorphism. for `U≤G` open normal and `h∈H`, `h∈comap φ
U` exactly when `φ(h)∈U`. -/
@[simp]
theorem mem_comap
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (phi : H →ₜ* G) (U : OpenNormalSubgroup G) (h : H) :
    h ∈ comap phi U ↔ phi h ∈ U :=
  Iff.rfl

/-- **Monotonicity of open-normal preimages.** Let `G,H` be groups with topologies and `φ : H
→ₜ* G` a continuous homomorphism. if open normal `U≤V` in `G`, then `comap φ U≤comap φ V`. -/
theorem comap_mono
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (phi : H →ₜ* G) {U V : OpenNormalSubgroup G} (hUV : U ≤ V) :
    comap phi U ≤ comap phi V := fun _ h => hUV h

/-- **Identity preimage of an open normal subgroup.** For a group `G` with topology and open
normal `U≤G`, `comap(id_G,U)=U`. -/
@[simp]
theorem comap_id
    {G : Type u} [Group G] [TopologicalSpace G]
    (U : OpenNormalSubgroup G) :
    comap (ContinuousMonoidHom.id G) U = U := by
  ext g
  rfl

/-- **Composition law of continuous open-normal preimages.** Let `G,H` be groups with
topologies and `φ : H →ₜ* G` a continuous homomorphism. for a group `K` with topology and
continuous homomorphism `ψ : K → H`, `comap (φ∘ψ) U=comap ψ (comap φ U)`. -/
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

/-- **Reverse-inclusion index functor of open-normal preimages.** Let `G,H` be groups with
topologies and `φ : H →ₜ* G` a continuous homomorphism. `openNormalComapFunctor φ :
OpenNormal(G)ᵒᵖ ⥤ OpenNormal(H)ᵒᵖ` sends `U` to `φ⁻¹(U)` and refinement maps to the
corresponding preimage inclusions. -/
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

/-- **Identity law of the open-normal preimage functor.** For a group `G` with topology, the
preimage functor of `id_G` on the opposite open-normal inclusion poset is the identity
functor. -/
theorem openNormalComapFunctor_id
    {G : Type u} [Group G] [TopologicalSpace G] :
    openNormalComapFunctor (ContinuousMonoidHom.id G) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun U => ?_) ?_
  · change Opposite.op (OpenNormalSubgroup.comap
      (ContinuousMonoidHom.id G) U.unop) = U
    rw [OpenNormalSubgroup.comap_id, Opposite.op_unop]
  · intro U V f
    exact Subsingleton.elim _ _

/-- **Functorial composition of open-normal preimages.** Let `G,H` be groups with topologies
and `φ : H →ₜ* G` a continuous homomorphism. for continuous `ψ : K → H`,
`openNormalComapFunctor (φ∘ψ)=openNormalComapFunctor φ ⋙ openNormalComapFunctor ψ`. -/
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
