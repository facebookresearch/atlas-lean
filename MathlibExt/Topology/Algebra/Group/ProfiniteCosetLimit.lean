/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Algebra.Group.ProfiniteCosetSection
import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Coset space of a subgroup intersection as an inverse limit

An antitone subgroup family `S_i` indexed by a preorder gives the inverse system of left-coset
spaces `G/S_i`, with the nested coset projection maps. The quotient by `∩_i S_i` has a natural
cone to this system.

If `G` is a compact topological group, the indices are nonempty and directed, and each `S_i` is
closed, this cone is a limit in topological spaces. No subgroup normality, total
disconnectedness or Hausdorffness of `G` is required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Topology

namespace QuotientGroup

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {ι : Type u} [Preorder ι]

/-- **Inverse system of antitone subgroup coset spaces.** Let `G` be a group with a topology,
`I` a preorder and `S_i≤G` an antitone subgroup family. `antitoneCosetSystem S : Iᵒᵖ ⥤
TopCat` has object `G/S_i`; an arrow from `op k` to `op i` for `i≤k` maps `[g]_(S_k)` to
`[g]_(S_i)`. -/
def antitoneCosetSystem (S : ι → Subgroup G) (hS : Antitone S) :
    ιᵒᵖ ⥤ TopCat.{u} where
  obj i := TopCat.of (G ⧸ S i.unop)
  map {i j} f := TopCat.ofHom <|
    cosetProjection (hS (leOfHom f.unop))
  map_id i := by
    ext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  map_comp f g := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rfl

/-- **Coset cone from the subgroup intersection.** Let `G` be a group with a topology, `I` a
preorder and `S_i≤G` an antitone subgroup family. `iInfCosetCone S` has vertex `G/(∩_i
S_i)` and component maps `[g]_(∩S) ↦ [g]_(S_i)`. -/
def iInfCosetCone (S : ι → Subgroup G) (hS : Antitone S) :
    Cone (antitoneCosetSystem S hS) where
  pt := TopCat.of (G ⧸ (⨅ i, S i))
  π :=
    { app := fun i => TopCat.ofHom <|
        cosetProjection (iInf_le S i.unop)
      naturality := fun i j f => by
        ext q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        rfl }

/-- **Component of the subgroup-intersection coset cone.** Let `G` be a group with a topology,
`I` a preorder and `S_i≤G` an antitone subgroup family. the component at `op i` is the
nested coset projection `G/(∩_j S_j) → G/S_i` induced by `∩_j S_j≤S_i`. -/
@[simp]
theorem iInfCosetCone_π_app
    (S : ι → Subgroup G) (hS : Antitone S) (i : ιᵒᵖ) :
    (iInfCosetCone S hS).π.app i =
      TopCat.ofHom (cosetProjection (iInf_le S i.unop)) :=
  rfl

/-- **Limit property of a compact closed-subgroup intersection cone.** Let `G` be a group with
a topology, `I` a preorder and `S_i≤G` an antitone subgroup family. assume additionally
that `G` is a compact topological group, `I` is nonempty and directed, and each `S_i` is
closed. Then `iInfCosetCone S` is a limit of the coset system in `TopCat`. -/
noncomputable def iInfCosetConeIsLimit
    [IsDirectedOrder ι] [Nonempty ι]
    [IsTopologicalGroup G] [CompactSpace G]
    (S : ι → Subgroup G) (hS : Antitone S)
    (hclosed : ∀ i, IsClosed (S i : Set G)) :
    IsLimit (iInfCosetCone S hS) := by
  let comparison : TopCat.of (G ⧸ (⨅ i, S i)) ⟶
      (TopCat.limitCone.{u, u, u} (antitoneCosetSystem S hS)).pt :=
    (TopCat.limitConeIsLimit.{u, u, u}
      (antitoneCosetSystem S hS)).lift (iInfCosetCone S hS)
  have comparison_apply
      (q : G ⧸ (⨅ i, S i)) (i : ιᵒᵖ) :
      (comparison q).1 i =
        cosetProjection (iInf_le S i.unop) q :=
    rfl
  have hinjective : Function.Injective comparison := by
    intro q r hqr
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective r
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_iInf]
    intro i
    apply QuotientGroup.eq.mp
    have hi := congrArg (fun z => z.1 (Opposite.op i)) hqr
    have hg := comparison_apply
      (QuotientGroup.mk g : G ⧸ (⨅ i, S i)) (Opposite.op i)
    have hh := comparison_apply
      (QuotientGroup.mk h : G ⧸ (⨅ i, S i)) (Opposite.op i)
    rw [hg, hh] at hi
    change (QuotientGroup.mk g : G ⧸ S i) = QuotientGroup.mk h at hi
    exact hi
  have hsurjective : Function.Surjective comparison := by
    let _ (i : ι) : IsClosed (S i : Set G) := hclosed i
    intro z
    let A : ι → Set G := fun i =>
      QuotientGroup.mk ⁻¹' {z.1 (Opposite.op i)}
    have zcompat (i k : ι) (hik : i ≤ k) :
        cosetProjection (hS hik) (z.1 (Opposite.op k)) =
          z.1 (Opposite.op i) := by
      let f : (Opposite.op k : ιᵒᵖ) ⟶ Opposite.op i :=
        (homOfLE hik).op
      have hz := z.2 f
      change cosetProjection (hS hik) (z.1 (Opposite.op k)) =
        z.1 (Opposite.op i) at hz
      exact hz
    have hA_nonempty : ∀ i, (A i).Nonempty := by
      intro i
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (z.1 (Opposite.op i))
      exact ⟨g, hg⟩
    have hA_closed : ∀ i, IsClosed (A i) := by
      intro i
      let _ : IsClosed (S i : Set G) := hclosed i
      let _ : T2Space (G ⧸ S i) := QuotientGroup.instT2Space
      exact IsClosed.preimage continuous_quotient_mk' isClosed_singleton
    have hA_directed : Directed (· ⊇ ·) A := by
      intro i j
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, ?_, ?_⟩
      · intro g hg
        change (QuotientGroup.mk g : G ⧸ S k) =
          z.1 (Opposite.op k) at hg
        change (QuotientGroup.mk g : G ⧸ S i) =
          z.1 (Opposite.op i)
        rw [← zcompat i k hik, ← hg]
        rfl
      · intro g hg
        change (QuotientGroup.mk g : G ⧸ S k) =
          z.1 (Opposite.op k) at hg
        change (QuotientGroup.mk g : G ⧸ S j) =
          z.1 (Opposite.op j)
        rw [← zcompat j k hjk, ← hg]
        rfl
    have hA_compact : ∀ i, IsCompact (A i) :=
      fun i => (hA_closed i).isCompact
    obtain ⟨g, hg⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        A hA_directed hA_nonempty hA_compact hA_closed
    refine ⟨(QuotientGroup.mk g : G ⧸ (⨅ i, S i)), ?_⟩
    apply Subtype.ext
    funext i
    rw [comparison_apply]
    exact Set.mem_singleton_iff.mp (Set.mem_iInter.mp hg i.unop)
  have hhome : IsHomeomorph comparison := by
    let _ (i : ι) : IsClosed (S i : Set G) := hclosed i
    let _ (i : ιᵒᵖ) : T2Space ((antitoneCosetSystem S hS).obj i) :=
      QuotientGroup.instT2Space
    let _ : T2Space (∀ i : ιᵒᵖ, (antitoneCosetSystem S hS).obj i) :=
      Pi.t2Space
    let _ : T2Space
        {x : ∀ i : ιᵒᵖ, (antitoneCosetSystem S hS).obj i |
          ∀ {i j} (f : i ⟶ j),
            (antitoneCosetSystem S hS).map f (x i) = x j} :=
      inferInstance
    let _ : T2Space
        (TopCat.limitCone.{u, u, u} (antitoneCosetSystem S hS)).pt := by
      change T2Space
        {x : ∀ i : ιᵒᵖ, (antitoneCosetSystem S hS).obj i |
          ∀ {i j} (f : i ⟶ j),
            (antitoneCosetSystem S hS).map f (x i) = x j}
      infer_instance
    rw [isHomeomorph_iff_continuous_bijective]
    exact ⟨comparison.hom.continuous, hinjective, hsurjective⟩
  let homeo := IsHomeomorph.homeomorph
    comparison hhome
  let e : iInfCosetCone S hS ≅
      TopCat.limitCone.{u, u, u} (antitoneCosetSystem S hS) :=
    Cone.ext (TopCat.isoOfHomeo homeo) (fun i => by
      change (iInfCosetCone S hS).π.app i =
        comparison ≫
          (TopCat.limitCone.{u, u, u}
            (antitoneCosetSystem S hS)).π.app i
      exact ((TopCat.limitConeIsLimit.{u, u, u}
        (antitoneCosetSystem S hS)).fac (iInfCosetCone S hS) i).symm)
  exact IsLimit.ofIsoLimit
    (TopCat.limitConeIsLimit.{u, u, u}
      (antitoneCosetSystem S hS)) e.symm

end QuotientGroup

end
