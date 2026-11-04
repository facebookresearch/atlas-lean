/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/Topology/Algebra/Category/ProfiniteGrp/Limits.lean` (Mathlib):
Copyright (c) 2024 Nailin Guan. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Nailin Guan, Youle Fang, Jujian Zhang, Yuyang Zhao

`Mathlib/Topology/Algebra/Category/ProfiniteGrp/Completion.lean` (Mathlib):
Copyright (c) 2026 Adam Topaz. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Adam Topaz
-/

module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# Open profinite completion from open finite-index normal subgroups.

Corrects the source formalization: an open subgroup of an arbitrary
topological group need not have finite index. We index by open *and*
finite-index normal subgroups.
-/

@[expose] public section

open CategoryTheory
open scoped Pointwise

universe u

namespace ProfiniteGrp.OpenProfiniteCompletion

/-- **Open finite-index normal subgroups.** For a group $G$ with a topology, this is the set of
normal subgroups $H$ of $G$ that have finite index and are open in $G$, ordered by inclusion and
viewed as a category: there is a morphism $H \to K$ exactly when $H \subseteq K$. -/
abbrev Index (G : Type u) [Group G] [TopologicalSpace G] :=
  { H : FiniteIndexNormalSubgroup G // IsOpen (H : Set G) }

/-- **Diagram of finite quotients.** For a group $G$ with a topology, this is the functor from
the category of open finite-index normal subgroups of $G$ to finite groups that sends $H$ to the
quotient group $G/H$ and sends an inclusion $H \subseteq K$ to the projection $G/H \to G/K$,
$gH \mapsto gK$. -/
def finiteGrpDiagram (G : Type u) [Group G]
    [TopologicalSpace G] : Index G ⥤ FiniteGrp.{u} where
  obj H := FiniteGrp.of <| G ⧸ H.1.toSubgroup
  map f :=
    FiniteGrp.ofHom <| QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id H := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

/-- **Diagram of finite quotients as profinite groups.** For a group $G$ with a topology, this is
the functor that sends each open finite-index normal subgroup $H$ of $G$ to the finite quotient
group $G/H$ with the discrete topology, regarded as a profinite group, and each inclusion
$H \subseteq K$ to the projection $G/H \to G/K$, $gH \mapsto gK$. It is the diagram of finite
quotients followed by the inclusion of finite groups into profinite groups. -/
def diagram (G : Type u) [Group G] [TopologicalSpace G] :
    Index G ⥤ ProfiniteGrp.{u} :=
  finiteGrpDiagram G ⋙ forget₂ (FiniteGrp.{u}) (ProfiniteGrp.{u})

/-- **Open profinite completion of a group.** For a group $G$ with a topology, the open profinite
completion of $G$ is the limit, in profinite groups, of the diagram of finite quotients $G/H$,
where $H$ runs over the open finite-index normal subgroups of $G$ and the transition maps are the
projections $G/H \to G/K$ for $H \subseteq K$. Concretely, it is the group of families
$(x_H)_H$ with $x_H \in G/H$ that are compatible under these projections, with the topology of a
subspace of the product of the discrete groups $G/H$. -/
def completion (G : Type u) [Group G] [TopologicalSpace G] :
    ProfiniteGrp.{u} :=
  ProfiniteGrp.limit (diagram G)

/-- **Canonical map into the open profinite completion.** For a group $G$ with a topology, this is
the map from $G$ to its open profinite completion that sends $x \in G$ to the family of cosets
$(xH)_H$, where $H$ runs over the open finite-index normal subgroups of $G$. -/
def etaFn (G : Type u) [Group G] [TopologicalSpace G]
    (x : G) : completion G :=
  ⟨fun _ => QuotientGroup.mk x, fun _ _ _ => rfl⟩

/-- **Coordinates of the canonical map.** Let $G$ be a group with a topology. For every $x \in G$
and every open finite-index normal subgroup $H$ of $G$, the $H$-coordinate of the image of $x$
under the canonical map into the open profinite completion of $G$ is the coset $xH \in G/H$. -/
@[simp]
theorem etaFn_apply (G : Type u) [Group G] [TopologicalSpace G] (x : G)
    (H : Index G) : ((etaFn G x).val H : G ⧸ H.1.toSubgroup) =
    QuotientGroup.mk x :=
  rfl

/-- **Continuity of the canonical map.** Let $G$ be a group with a topology in which
multiplication is separately continuous: $x \mapsto ax$ and $x \mapsto xa$ are continuous for
every $a \in G$. Then the canonical map from $G$ to its open profinite completion is continuous.

Joint continuity of multiplication is not needed. -/
theorem etaFn_continuous (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : Continuous (etaFn G) := by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro H
  apply Continuous.mk
  intro s _hs
  let s' : Set (G ⧸ H.1.toSubgroup) := fun x ↦ s x
  change IsOpen ((QuotientGroup.mk' H.1.toSubgroup) ⁻¹' s')
  rw [← (Set.biUnion_preimage_singleton (QuotientGroup.mk' H.1.toSubgroup) s')]
  refine isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ ?_))
  convert! IsOpen.leftCoset H.2 (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  conv_lhs => rhs; rw [← QuotientGroup.out_eq' i]
  change (↑x : G ⧸ H.1.toSubgroup) = ↑(Quotient.out i) ↔
    x ∈ Quotient.out i • (↑H.1.toSubgroup : Set G)
  rw [eq_comm, QuotientGroup.eq]
  exact Iff.symm Set.mem_smul_set_iff_inv_smul_mem

/-- **Canonical homomorphism into the open profinite completion.** Let $G$ be a group with a
topology in which multiplication is separately continuous. This is the canonical map from $G$
to its open profinite completion, $x \mapsto (xH)_H$ with $H$ running over the open
finite-index normal subgroups of $G$, regarded as a continuous group homomorphism. -/
def eta (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : G →ₜ* completion G where
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := etaFn_continuous G

/-- **The canonical map has dense image.** For every group $G$ with a topology, the image of the
canonical map from $G$ to its open profinite completion is dense.

No compatibility between the multiplication and the topology of $G$ is assumed. -/
theorem denseRange_etaFn (G : Type u) [Group G] [TopologicalSpace G] :
    DenseRange (etaFn G) := by
  unfold etaFn completion
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, _fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) ↦ j.1.1.toSubgroup
  have hMNormal : M.Normal :=
    Subgroup.normal_iInf_normal fun _ ↦ inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  have hMOpen : IsOpen (M : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j ↦ j.1.2
  let m : Index G := ⟨{
    toSubgroup := M
    isNormal' := hMNormal
    isFiniteIndex' := hMFinite }, hMOpen⟩
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use ⟨fun _ ↦ QuotientGroup.mk origin, fun _ _ _ ↦ rfl⟩
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a :=
    (iInf_le (fun (j : J) ↦ j.1.1.toSubgroup) ⟨a, a_in_J⟩).hom
  rw [← (⟨fun _ ↦ QuotientGroup.mk origin, fun _ _ _ ↦ rfl⟩ :
    ProfiniteGrp.limit (diagram G)).property M_to_Na]
  change (finiteGrpDiagram G).map M_to_Na (QuotientGroup.mk' M origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

/-- **Density of the canonical homomorphism.** Let $G$ be a group with a topology in which
multiplication is separately continuous. Then the canonical continuous homomorphism from $G$ to
its open profinite completion has dense image. -/
theorem denseRange_eta (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : DenseRange (eta G) :=
  denseRange_etaFn G

end ProfiniteGrp.OpenProfiniteCompletion
