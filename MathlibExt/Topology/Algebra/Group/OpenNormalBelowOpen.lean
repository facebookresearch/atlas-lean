/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.Regular
public import Mathlib.CategoryTheory.Filtered.Final
public import MathlibExt.Topology.Algebra.Group.OpenNormalComap
public import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Ambient open normal subgroups inside a fixed open subgroup

For an open subgroup `H≤G`, the objects `BelowOpen H` are ambient open normal subgroups `U≤G`
satisfying `U≤H`. Their order is inclusion, and intersection is their infimum.

If `G` is a compact totally disconnected topological group, these objects are nonempty and their
opposite poset is filtered. Restricting all ambient open normals to those contained in `H` is
cofinal under reverse inclusion. The preimage index into open normal subgroups of `H` is cofinal
as well.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpenSubgroup

universe u

instance {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : OpenSubgroup G) : IsTopologicalGroup H :=
  inferInstanceAs (IsTopologicalGroup H.toSubgroup)

instance {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (H : OpenSubgroup G) : CompactSpace H :=
  isCompact_iff_compactSpace.mp H.isClosed.isCompact

end OpenSubgroup

namespace OpenNormalSubgroup

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **Ambient open normal subgroup bounded by an open subgroup.** Let `G` be a group with a
topology and `H` an open subgroup. `BelowOpen H` contains an open normal subgroup `U≤G`
and the condition `U≤H`; no compactness or continuity of group operations is needed for
this carrier. -/
structure BelowOpen (H : OpenSubgroup G) where
  /-- **Ambient subgroup of a bounded open-normal object.** Let `G` be a group with a topology
  and `H` an open subgroup. the field `obj` is an open normal subgroup `U≤G`. -/
  obj : OpenNormalSubgroup G
  /-- **Containment field of a bounded ambient open normal subgroup.** Let `G` be a group with
  a topology and `H` an open subgroup. the condition is `U≤H` for the ambient open normal
  subgroup `U` stored in the object. -/
  le_open : obj.toSubgroup ≤ H.toSubgroup

namespace BelowOpen

variable {H : OpenSubgroup G}

/-- **Injective inclusion of bounded open normals into all ambient ones.** Let `G` be a group
with a topology and `H` an open subgroup. `objEmbedding : BelowOpen H ↪ OpenNormal(G)`
forgets the containment condition and retains the ambient subgroup `U`. -/
def objEmbedding : BelowOpen H ↪ OpenNormalSubgroup G where
  toFun := BelowOpen.obj
  inj' := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩ h
    cases h
    rfl

instance : PartialOrder (BelowOpen H) :=
  PartialOrder.lift BelowOpen.obj objEmbedding.injective

@[simp]
theorem le_iff (U V : BelowOpen H) : U ≤ V ↔ U.obj ≤ V.obj :=
  Iff.rfl

instance : Min (BelowOpen H) where
  min U V :=
    ⟨U.obj ⊓ V.obj, fun _g hg => U.le_open ((inf_le_left : U.obj ⊓ V.obj ≤ U.obj) hg)⟩

@[simp]
theorem obj_inf (U V : BelowOpen H) : (U ⊓ V).obj = U.obj ⊓ V.obj :=
  rfl

instance : SemilatticeInf (BelowOpen H) where
  inf := fun U V => U ⊓ V
  inf_le_left U V := by
    exact (show U.obj ⊓ V.obj ≤ U.obj from inf_le_left)
  inf_le_right U V := by
    exact (show U.obj ⊓ V.obj ≤ V.obj from inf_le_right)
  le_inf U V W hUV hUW := by
    exact (show U.obj ≤ V.obj ⊓ W.obj from le_inf hUV hUW)

section Profinite

variable [IsTopologicalGroup G] [CompactSpace G]
variable [TotallyDisconnectedSpace G]

instance : Nonempty (BelowOpen H) := by
  obtain ⟨U, hU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one H.isOpen H.one_mem
  exact ⟨⟨U, hU⟩⟩

/-- **Filtered reverse-inclusion index inside an open subgroup.** Let `G` be a group with a
topology and `H` an open subgroup. Assume `G` is a compact totally disconnected
topological group. the opposite inclusion poset `(BelowOpen H)ᵒᵖ` is filtered, with
intersections giving simultaneous refinements. -/
instance : IsFiltered (BelowOpen H)ᵒᵖ := inferInstance

end Profinite

/-- **Functor including bounded ambient open normal indices.** Let `G` be a group with a
topology and `H` an open subgroup. `inclusion : BelowOpen H ⥤ OpenNormal(G)` sends `U≤H`
to its ambient subgroup `U` and inclusion arrows to the same inclusions. -/
def inclusion : BelowOpen H ⥤ OpenNormalSubgroup G where
  obj U := U.obj
  map {U V} f := homOfLE (show U.obj ≤ V.obj from leOfHom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **Preimage index functor from ambient normals to the open subgroup.** Let `G` be a group
with a topology and `H` an open subgroup. `comapFunctor H : (BelowOpen H)ᵒᵖ ⥤
OpenNormal(H)ᵒᵖ` sends an ambient `U≤H` to its preimage under the subgroup inclusion `H →
G`. -/
def comapFunctor (H : OpenSubgroup G) :
    (BelowOpen H)ᵒᵖ ⥤ (OpenNormalSubgroup H)ᵒᵖ where
  obj U := Opposite.op
    (OpenNormalSubgroup.comap
      (ContinuousMonoidHom.mk H.toSubgroup.subtype continuous_subtype_val)
      U.unop.obj)
  map {_U _V} f :=
    (homOfLE (OpenNormalSubgroup.comap_mono
      (ContinuousMonoidHom.mk H.toSubgroup.subtype continuous_subtype_val)
      (leOfHom f.unop))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

section Final

variable [IsTopologicalGroup G] [CompactSpace G]
variable [TotallyDisconnectedSpace G]

/-- **Cofinality of ambient open normals lying inside a fixed open subgroup.** Let `G` be a
group with a topology and `H` an open subgroup. Assume `G` is a compact totally
disconnected topological group. the opposite inclusion functor `(BelowOpen H)ᵒᵖ →
OpenNormal(G)ᵒᵖ` is final: every ambient open normal subgroup admits a refining ambient
open normal contained in `H`. -/
instance (H : OpenSubgroup G) :
    ((inclusion (H := H)).op).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro U
    let W : BelowOpen H := Classical.choice inferInstance
    let V : BelowOpen H :=
      ⟨U.unop ⊓ W.obj, fun _g hg => W.le_open
        ((inf_le_right : U.unop ⊓ W.obj ≤ W.obj) hg)⟩
    exact ⟨Opposite.op V,
      ⟨(homOfLE (show V.obj ≤ U.unop from inf_le_left)).op⟩⟩
  · intro _ c _ _
    exact ⟨c, 𝟙 _, by subsingleton⟩

/-- **Cofinality of bounded ambient preimages in the subgroup index.** Let `G` be a group with
a topology and `H` an open subgroup. Assume `G` is a compact totally disconnected
topological group. `comapFunctor H` is final: every open normal subgroup of `H` is refined
by the preimage of an ambient open normal subgroup contained in `H`. -/
instance (H : OpenSubgroup G) : (comapFunctor H).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro V
    let S : Subgroup G := V.unop.toSubgroup.map H.toSubgroup.subtype
    have hSopen : IsOpen (S : Set G) := by
      change IsOpen (H.toSubgroup.subtype '' (V.unop : Set H))
      exact H.isOpen.isOpenMap_subtype_val _ V.unop.isOpen
    obtain ⟨U, hUV⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hSopen S.one_mem
    have hUH : U.toSubgroup ≤ H.toSubgroup := by
      refine hUV.trans ?_
      intro g hg
      rcases hg with ⟨v, _hv, rfl⟩
      exact v.property
    let U' : BelowOpen H := ⟨U, hUH⟩
    have hcomap : OpenNormalSubgroup.comap
        (ContinuousMonoidHom.mk H.toSubgroup.subtype continuous_subtype_val)
        U ≤ V.unop := by
      intro h hh
      change h ∈ V.unop
      rcases hUV hh with ⟨v, hv, heq⟩
      have heq' : (v : H) = h := by
        apply Subtype.ext
        exact heq
      exact heq' ▸ hv
    exact ⟨Opposite.op U', ⟨(homOfLE hcomap).op⟩⟩
  · intro _ c _ _
    exact ⟨c, 𝟙 _, by subsingleton⟩

end Final

end BelowOpen

end OpenNormalSubgroup
