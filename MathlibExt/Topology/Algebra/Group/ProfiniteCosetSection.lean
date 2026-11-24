/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Algebra.Group.ProfiniteCoset
import MathlibExt.Topology.LocalHomeomorph.ProfiniteSection
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Tactic.Group

/-!
# Continuous sections of finite-index nested coset projections

Let `K ≤ H` be closed subgroups of a profinite group, with `K` of finite
relative index in `H`.  The canonical continuous map from left `K`-cosets
to left `H`-cosets is a surjective local homeomorphism and therefore has a
continuous set-theoretic section.

Neither subgroup is assumed normal.  The section is existential and is not
claimed to be homomorphic, canonical, or natural.  This is only the
finite-index case; no inverse-limit or general closed-subgroup section is
constructed.

## Main declarations

* `QuotientGroup.cosetProjection`
* `QuotientGroup.cosetProjection_mk`
* `QuotientGroup.exists_continuous_section_of_isFiniteRelIndex`

## Reference

This is the finite-index leaf in the proof of J.-P. Serre,
*Galois Cohomology*, Chapter I, Section 1, Proposition 1.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Pointwise

namespace QuotientGroup

universe u

/-- The continuous projection from left `K`-cosets to left `H`-cosets
induced by an inclusion `K ≤ H`.  No normality is required. -/
def cosetProjection
    {G : Type u} [Group G] [TopologicalSpace G]
    {K H : Subgroup G} (h : K ≤ H) : C(G ⧸ K, G ⧸ H) :=
  ⟨Quotient.map' id fun _ _ hab =>
      QuotientGroup.leftRel_apply.mpr
        (h (QuotientGroup.leftRel_apply.mp hab)),
    continuous_id.quotient_map' fun _ _ hab =>
      QuotientGroup.leftRel_apply.mpr
        (h (QuotientGroup.leftRel_apply.mp hab))⟩

/-- The nested coset projection sends the class of a representative to its
class modulo the larger subgroup. -/
@[simp]
theorem cosetProjection_mk
    {G : Type u} [Group G] [TopologicalSpace G]
    {K H : Subgroup G} (h : K ≤ H) (g : G) :
    cosetProjection h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

private theorem cosetProjection_surjective
    {G : Type u} [Group G] [TopologicalSpace G]
    {K H : Subgroup G} (h : K ≤ H) :
    Function.Surjective (cosetProjection h) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨QuotientGroup.mk g, rfl⟩

private theorem cosetProjection_isOpenMap
    {G : Type u} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G]
    {K H : Subgroup G} (h : K ≤ H) :
    IsOpenMap (cosetProjection h) := by
  intro O hO
  have hpre : IsOpen (QuotientGroup.mk ⁻¹' O) :=
    QuotientGroup.continuous_mk.isOpen_preimage O hO
  have himage : IsOpen
      (QuotientGroup.mk '' (QuotientGroup.mk ⁻¹' O) : Set (G ⧸ H)) :=
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ hpre
  convert himage using 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨g, hz, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨QuotientGroup.mk g, hg, rfl⟩

private theorem cosetProjection_isLocalHomeomorph_of_inf_le
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K H : Subgroup G} (hKH : K ≤ H)
    (U : OpenNormalSubgroup G) (hUK : U.toSubgroup ⊓ H ≤ K) :
    IsLocalHomeomorph (cosetProjection hKH) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  let V : Set (G ⧸ K) :=
    QuotientGroup.mk '' (g • (U.toSubgroup : Set G))
  have hVopen : IsOpen V :=
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap _
      (U.isOpen.leftCoset g)
  have hgV : QuotientGroup.mk g ∈ V := by
    refine ⟨g, ?_, rfl⟩
    simpa using mem_leftCoset g U.one_mem
  refine ⟨V, hVopen.mem_nhds hgV, ?_⟩
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (cosetProjection hKH).continuous.continuousOn.domRestrict
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    rcases ha with ⟨x, hx, rfl⟩
    rcases hb with ⟨y, hy, rfl⟩
    apply Subtype.ext
    apply QuotientGroup.eq.mpr
    apply hUK
    constructor
    · have hxU : g⁻¹ * x ∈ U := (mem_leftCoset_iff g).mp hx
      have hyU : g⁻¹ * y ∈ U := (mem_leftCoset_iff g).mp hy
      have hmul := U.mul_mem (U.inv_mem hxU) hyU
      have heq : (g⁻¹ * x)⁻¹ * (g⁻¹ * y) = x⁻¹ * y := by group
      rw [heq] at hmul
      exact hmul
    · apply QuotientGroup.eq.mp
      change cosetProjection hKH (QuotientGroup.mk x) =
        cosetProjection hKH (QuotientGroup.mk y) at hab
      exact hab
  · exact (cosetProjection_isOpenMap hKH).domRestrict hVopen

/-- If `K` has finite relative index in the closed subgroup `H` of a
profinite group, some ambient open normal subgroup meets `H` inside `K`. -/
theorem exists_openNormal_inf_le_of_isFiniteRelIndex
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (K H : Subgroup G)
    [IsClosed (K : Set G)] [K.IsFiniteRelIndex H] :
    ∃ U : OpenNormalSubgroup G, U.toSubgroup ⊓ H ≤ K := by
  have hclosed : IsClosed
      ((K.subgroupOf H : Subgroup H) : Set H) := by
    exact (show IsClosed (H.subtype ⁻¹' (K : Set G)) from
      (show IsClosed (K : Set G) from inferInstance).preimage
        continuous_subtype_val)
  have hopen : IsOpen ((K.subgroupOf H : Subgroup H) : Set H) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex (K.subgroupOf H) hclosed
  obtain ⟨O, hOopen, hOeq⟩ := isOpen_induced_iff.mp hopen
  have h1O : (1 : G) ∈ O := by
    have h1K : (1 : H) ∈ K.subgroupOf H := (K.subgroupOf H).one_mem
    have h1pre : (1 : H) ∈ H.subtype ⁻¹' O := hOeq.symm ▸ h1K
    exact h1pre
  obtain ⟨U, hUO⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      hOopen h1O
  refine ⟨U, ?_⟩
  intro g hg
  have hgO : g ∈ O := hUO hg.1
  have hgKsub : (⟨g, hg.2⟩ : H) ∈ K.subgroupOf H := by
    change (⟨g, hg.2⟩ : H) ∈ (K.subgroupOf H : Set H)
    rw [← hOeq]
    exact hgO
  exact hgKsub

/-- An open normal subgroup of an open subgroup contains the image of some
ambient open normal subgroup.  The ambient subgroup is therefore contained
in the open subgroup as well. -/
theorem exists_openNormal_le_map_openNormal
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : OpenSubgroup G) (V : OpenNormalSubgroup H) :
    ∃ U : OpenNormalSubgroup G,
      U.toSubgroup ≤ V.toSubgroup.map H.toSubgroup.subtype := by
  let K : Subgroup G := V.toSubgroup.map H.toSubgroup.subtype
  have hKopen : IsOpen (K : Set G) := by
    change IsOpen (H.toSubgroup.subtype '' (V : Set H))
    exact H.isOpen.isOpenMap_subtype_val _ V.isOpen
  obtain ⟨U, hU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      hKopen K.one_mem
  exact ⟨U, hU⟩

/-- For closed nested subgroups of a profinite group, finite relative index
gives a continuous set-theoretic section of the nested coset projection. -/
theorem exists_continuous_section_of_isFiniteRelIndex
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (K H : Subgroup G) (hKH : K ≤ H)
    [IsClosed (K : Set G)] [IsClosed (H : Set G)]
    [K.IsFiniteRelIndex H] :
    ∃ s : C(G ⧸ H, G ⧸ K),
      Function.RightInverse s (cosetProjection hKH) := by
  obtain ⟨U, hU⟩ := exists_openNormal_inf_le_of_isFiniteRelIndex K H
  let _ : TotallyDisconnectedSpace (G ⧸ H) :=
    QuotientGroup.totallyDisconnectedSpace_of_isClosed H
  exact
    (cosetProjection_isLocalHomeomorph_of_inf_le hKH U hU)
      |>.exists_continuous_rightInverse_of_profinite
        (cosetProjection_surjective hKH)

end QuotientGroup

end
