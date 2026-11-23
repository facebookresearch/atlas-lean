/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.OrderedTwoSetCover
public import MathlibExt.Topology.Category.TopPair.Triple

/-!
# The ordered two-set cover for relative cup products

This file records only the topology-layer excision data.  The interiors in
`IsRelativeCupExcisive` are taken in the union subspace `A ∪ B`.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory TopologicalSpace

noncomputable section

universe u w

namespace AlgebraicTopology

/-- The union subspace on which relative-cup excision is tested. -/
def relativeCupUnionSpace {X : TopCat.{u}} (A B : Set X) : TopCat.{u} :=
  TopCat.of (A ∪ B : Set X)

/-- The inverse image of the left subset in the union subspace. -/
def relativeCupLeft {X : TopCat.{u}} (A B : Set X) :
    Set (relativeCupUnionSpace A B) :=
  subspaceIncl (A ∪ B : Set X) ⁻¹' A

/-- The inverse image of the right subset in the union subspace. -/
def relativeCupRight {X : TopCat.{u}} (A B : Set X) :
    Set (relativeCupUnionSpace A B) :=
  subspaceIncl (A ∪ B : Set X) ⁻¹' B

/-- The left subset pulled back to the union subspace is canonically
homeomorphic to the original left subspace. -/
noncomputable def relativeCupLeftIso {X : TopCat.{u}} (A B : Set X) :
    TopCat.of (relativeCupLeft A B) ≅ TopCat.of A :=
  TopCat.isoOfHomeo
    { toEquiv :=
        { toFun := fun x =>
            ⟨⇑(subspaceIncl (A ∪ B : Set X))
              (⇑(subspaceIncl (relativeCupLeft A B)) x), x.property⟩
          invFun := fun x =>
            ⟨⟨x.val, Set.mem_union_left B x.property⟩, x.property⟩
          left_inv := fun x => by
            cases x with
            | mk x hx => cases x with
              | mk _ _ => rfl
          right_inv := fun x => by
            cases x with
            | mk _ _ => rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

/-- The right subset pulled back to the union subspace is canonically
homeomorphic to the original right subspace. -/
noncomputable def relativeCupRightIso {X : TopCat.{u}} (A B : Set X) :
    TopCat.of (relativeCupRight A B) ≅ TopCat.of B :=
  TopCat.isoOfHomeo
    { toEquiv :=
        { toFun := fun x =>
            ⟨⇑(subspaceIncl (A ∪ B : Set X))
              (⇑(subspaceIncl (relativeCupRight A B)) x), x.property⟩
          invFun := fun x =>
            ⟨⟨x.val, Set.mem_union_right A x.property⟩, x.property⟩
          left_inv := fun x => by
            cases x with
            | mk x hx => cases x with
              | mk _ _ => rfl
          right_inv := fun x => by
            cases x with
            | mk _ _ => rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

@[simp]
theorem relativeCupLeftIso_hom_apply {X : TopCat.{u}} (A B : Set X)
    (x : TopCat.of (relativeCupLeft A B)) :
    (relativeCupLeftIso A B).hom x = ⟨x.1.1, x.2⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem relativeCupLeftIso_inv_apply {X : TopCat.{u}} (A B : Set X)
    (x : TopCat.of A) :
    (relativeCupLeftIso A B).inv x =
      ⟨⟨x.1, Set.mem_union_left B x.2⟩, x.2⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

@[simp]
theorem relativeCupRightIso_hom_apply {X : TopCat.{u}} (A B : Set X)
    (x : TopCat.of (relativeCupRight A B)) :
    (relativeCupRightIso A B).hom x = ⟨x.1.1, x.2⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem relativeCupRightIso_inv_apply {X : TopCat.{u}} (A B : Set X)
    (x : TopCat.of B) :
    (relativeCupRightIso A B).inv x =
      ⟨⟨x.1, Set.mem_union_right A x.2⟩, x.2⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The left-subspace isomorphism followed by the inclusion into the union
subspace is the canonical nested-subspace inclusion. -/
@[reassoc]
theorem relativeCupLeftIso_hom_incl {X : TopCat.{u}} (A B : Set X) :
    (relativeCupLeftIso A B).hom ≫
        subspaceInclOfSubset (fun _ hx => Set.mem_union_left B hx) =
      subspaceIncl (relativeCupLeft A B) := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- The right-subspace isomorphism followed by the inclusion into the union
subspace is the canonical nested-subspace inclusion. -/
@[reassoc]
theorem relativeCupRightIso_hom_incl {X : TopCat.{u}} (A B : Set X) :
    (relativeCupRightIso A B).hom ≫
        subspaceInclOfSubset (fun _ hx => Set.mem_union_right A hx) =
      subspaceIncl (relativeCupRight A B) := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- The excision condition for ordinary relative cup products.  Both interiors
are taken in the union subspace, not in the ambient space. -/
def IsRelativeCupExcisive {X : TopCat.{u}} (A B : Set X) : Prop :=
  (Set.univ : Set (relativeCupUnionSpace A B)) ⊆
    interior (relativeCupLeft A B) ∪ interior (relativeCupRight A B)

/-- Two open subsets form a relative-cup excisive pair. -/
theorem isRelativeCupExcisive_of_isOpen {X : TopCat.{u}} {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    IsRelativeCupExcisive A B := by
  have hleft : IsOpen (relativeCupLeft A B) := hA.preimage (by fun_prop)
  have hright : IsOpen (relativeCupRight A B) := hB.preimage (by fun_prop)
  rw [IsRelativeCupExcisive, hleft.interior_eq, hright.interior_eq]
  intro x _
  exact x.2

/-- The ordered two-set cover supplied by a relative-cup excision hypothesis. -/
def relativeCupOrderedTwoSetCover {X : TopCat.{u}} {A B : Set X}
    (h : IsRelativeCupExcisive A B) : OrderedTwoSetCover.{u} where
  X := relativeCupUnionSpace A B
  left := relativeCupLeft A B
  right := relativeCupRight A B
  interior_cover := h

/-- A map between the union subspaces induced by a map preserving both sides. -/
def relativeCupUnionMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {C D : Set Y}
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) :
    relativeCupUnionSpace A B ⟶ relativeCupUnionSpace C D :=
  subspaceMap f (hA.union_union hB)

/-- A side-preserving map between relative-cup ordered covers. -/
def relativeCupOrderedTwoSetCoverMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : Set X} {C D : Set Y}
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (hX : IsRelativeCupExcisive A B) (hY : IsRelativeCupExcisive C D) :
    relativeCupOrderedTwoSetCover hX ⟶ relativeCupOrderedTwoSetCover hY where
  f := relativeCupUnionMap f hA hB
  left_maps := by
    intro x hx
    exact hA hx
  right_maps := by
    intro x hx
    exact hB hx

theorem isRelativeCupExcisive_empty_left {X : TopCat.{u}} (B : Set X) :
    IsRelativeCupExcisive (∅ : Set X) B := by
  have hright : relativeCupRight (∅ : Set X) B = Set.univ := by
    ext x
    constructor
    · intro
      trivial
    · intro
      change x.1 ∈ B
      simpa using x.2
  rw [IsRelativeCupExcisive, hright, interior_univ, Set.union_univ]

theorem isRelativeCupExcisive_empty_right {X : TopCat.{u}} (A : Set X) :
    IsRelativeCupExcisive A (∅ : Set X) := by
  have hleft : relativeCupLeft A (∅ : Set X) = Set.univ := by
    ext x
    constructor
    · intro
      trivial
    · intro
      change x.1 ∈ A
      simpa using x.2
  rw [IsRelativeCupExcisive, hleft, interior_univ, Set.univ_union]

theorem isRelativeCupExcisive_self {X : TopCat.{u}} (A : Set X) :
    IsRelativeCupExcisive A A := by
  have hleft : relativeCupLeft A A = Set.univ := by
    ext x
    constructor
    · intro
      trivial
    · intro
      change x.1 ∈ A
      simpa using x.2
  rw [IsRelativeCupExcisive, hleft, interior_univ, Set.univ_union]

theorem IsRelativeCupExcisive.comm {X : TopCat.{u}} {A B : Set X}
    (h : IsRelativeCupExcisive A B) :
    IsRelativeCupExcisive B A := by
  unfold IsRelativeCupExcisive relativeCupLeft relativeCupRight
    relativeCupUnionSpace at h ⊢
  rw [Set.union_comm B A]
  simpa only [Set.union_comm (interior _) (interior _)] using h

public theorem isRelativeCupExcisive_of_orderedTwoSetCover
    (U : OrderedTwoSetCover.{u}) : IsRelativeCupExcisive U.left U.right := by
  have hmem : ∀ {S : Set U.X} (x : TopCat.of S) (T : Set U.X),
      x ∈ interior (subspaceIncl S ⁻¹' T) ↔ T ∈ nhdsWithin x.1 S := by
    intro S x T
    rw [mem_interior_iff_mem_nhds, nhds_subtype_eq_comap, Filter.mem_comap]
    simp only [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    constructor
    · rintro ⟨W, hW, hW_sub⟩
      refine ⟨W, hW, fun y hy => ?_⟩
      have hyW : (⟨y, hy.2⟩ : TopCat.of S) ∈
          (Subtype.val ⁻¹' W : Set (TopCat.of S)) := hy.1
      have hmemT := hW_sub hyW
      simpa [subspaceIncl] using hmemT
    · rintro ⟨V, hV, hV_sub⟩
      refine ⟨V, hV, fun y hy => ?_⟩
      have hyV : y.1 ∈ V ∩ S := ⟨hy, y.2⟩
      exact hV_sub hyV
  rw [IsRelativeCupExcisive]
  intro x _
  have hx_cover := U.interior_cover (Set.mem_univ x.1)
  rcases hx_cover with hL | hR
  · have h_nhds : U.left ∈ nhds x.1 := mem_interior_iff_mem_nhds.mp hL
    have h_within : U.left ∈ nhdsWithin x.1 (U.left ∪ U.right) :=
      mem_nhdsWithin_of_mem_nhds h_nhds
    have h_in : x ∈ interior (subspaceIncl (U.left ∪ U.right) ⁻¹' U.left) :=
      (hmem x U.left).mpr h_within
    have h_eq : relativeCupLeft U.left U.right =
        subspaceIncl (U.left ∪ U.right) ⁻¹' U.left := rfl
    exact Or.inl (h_eq.symm ▸ h_in)
  · have h_nhds : U.right ∈ nhds x.1 := mem_interior_iff_mem_nhds.mp hR
    have h_within : U.right ∈ nhdsWithin x.1 (U.left ∪ U.right) :=
      mem_nhdsWithin_of_mem_nhds h_nhds
    have h_in : x ∈ interior (subspaceIncl (U.left ∪ U.right) ⁻¹' U.right) :=
      (hmem x U.right).mpr h_within
    have h_eq : relativeCupRight U.left U.right =
        subspaceIncl (U.left ∪ U.right) ⁻¹' U.right := rfl
    exact Or.inr (h_eq.symm ▸ h_in)

private theorem relativeCup_nested_nhdsWithin_trans {X : Type u} [TopologicalSpace X]
    {A B C : Set X} {x : X}
    (hB_mem_nhdsWithin_C : B ∈ nhdsWithin x C) (hA_mem_nhdsWithin_B : A ∈ nhdsWithin x B) :
    A ∈ nhdsWithin x C := by
  rw [mem_nhdsWithin] at hB_mem_nhdsWithin_C hA_mem_nhdsWithin_B
  obtain ⟨U, hU_isOpen, hxU_mem, hU_inter_subset_B⟩ := hB_mem_nhdsWithin_C
  obtain ⟨V, hV_isOpen, hxV_mem, hV_inter_subset_A⟩ := hA_mem_nhdsWithin_B
  rw [mem_nhdsWithin]
  refine ⟨U ∩ V, hU_isOpen.inter hV_isOpen, ⟨hxU_mem, hxV_mem⟩, ?_⟩
  intro y hy_mem
  have hyU_mem : y ∈ U := hy_mem.1.1
  have hyV_mem : y ∈ V := hy_mem.1.2
  have hyC_mem : y ∈ C := hy_mem.2
  have hyB_mem : y ∈ B := hU_inter_subset_B ⟨hyU_mem, hyC_mem⟩
  exact hV_inter_subset_A ⟨hyV_mem, hyB_mem⟩

theorem triple_interior_cover_of_left_nested {X : TopCat.{u}} (A B C : Set X)
    (hAB : IsRelativeCupExcisive A B)
    (hABC : IsRelativeCupExcisive (A ∪ B) C) :
    (Set.univ : Set (TopCat.of ((A ∪ B) ∪ C : Set X))) ⊆
      interior (subspaceIncl ((A ∪ B) ∪ C : Set X) ⁻¹' A) ∪
        interior (subspaceIncl ((A ∪ B) ∪ C : Set X) ⁻¹' B) ∪
      interior (subspaceIncl ((A ∪ B) ∪ C : Set X) ⁻¹' C) := by
  have hmem :
      ∀ {S : Set X} (x : TopCat.of S) (T : Set X),
        x ∈ interior (subspaceIncl S ⁻¹' T) ↔ T ∈ nhdsWithin x.1 S := by
    intro S x T
    rw [mem_interior_iff_mem_nhds, nhds_subtype_eq_comap, Filter.mem_comap]
    simp only [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    constructor
    · rintro ⟨U, hU, hU_sub⟩
      refine ⟨U, hU, fun y hy => ?_⟩
      have hyU : (⟨y, hy.2⟩ : TopCat.of S) ∈
          (Subtype.val ⁻¹' U : Set (TopCat.of S)) := hy.1
      have hmemT := hU_sub hyU
      simpa [subspaceIncl] using hmemT
    · rintro ⟨V, hV, hV_sub⟩
      refine ⟨V, hV, fun y hy => ?_⟩
      have hyV : y.1 ∈ V ∩ S := ⟨hy, y.2⟩
      exact hV_sub hyV
  intro x _
  have hABCx := hABC (Set.mem_univ x)
  rcases hABCx with hAB_in | hC_in
  · have hAB_nhds : (A ∪ B) ∈ nhdsWithin x.1 ((A ∪ B) ∪ C) :=
      (hmem (S := ((A ∪ B) ∪ C : Set X)) x (A ∪ B)).mp hAB_in
    have hxAB : x.1 ∈ A ∪ B := by
      obtain ⟨V, hV, hV_sub⟩ :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hAB_nhds
      exact hV_sub ⟨mem_of_mem_nhds hV, x.2⟩
    let y : relativeCupUnionSpace A B := ⟨x.1, hxAB⟩
    have hy := hAB (Set.mem_univ y)
    rcases hy with hA_in | hB_in
    · have hA_nhds : A ∈ nhdsWithin x.1 (A ∪ B) := by
        have := (hmem (S := A ∪ B) y A).mp hA_in
        simpa using this
      have hA_S : A ∈ nhdsWithin x.1 ((A ∪ B) ∪ C) :=
        relativeCup_nested_nhdsWithin_trans hAB_nhds hA_nhds
      exact Or.inl (Or.inl ((hmem x A).mpr hA_S))
    · have hB_nhds : B ∈ nhdsWithin x.1 (A ∪ B) := by
        have := (hmem (S := A ∪ B) y B).mp hB_in
        simpa using this
      have hB_S : B ∈ nhdsWithin x.1 ((A ∪ B) ∪ C) :=
        relativeCup_nested_nhdsWithin_trans hAB_nhds hB_nhds
      exact Or.inl (Or.inr ((hmem x B).mpr hB_S))
  · exact Or.inr hC_in

/-- An ambient excisive triad packaging the relative-cup excision hypothesis. -/
structure ExcisiveTriad where
  /-- The ambient topological space. -/
  X : TopCat.{u}
  /-- The left side of the triad. -/
  left : Set X
  /-- The right side of the triad. -/
  right : Set X
  excisive : IsRelativeCupExcisive left right

/-- The excisive triad underlying an ordered two-set cover. -/
public def orderedTwoSetCoverExcisiveTriad
    (U : OrderedTwoSetCover.{u}) : ExcisiveTriad.{u} :=
  ⟨U.X, U.left, U.right, isRelativeCupExcisive_of_orderedTwoSetCover U⟩

namespace ExcisiveTriad

/-- Morphisms of excisive triads, given by an ambient map preserving each side. -/
structure Hom (C D : ExcisiveTriad.{u}) where
  /-- The map of ambient spaces. -/
  f : C.X ⟶ D.X
  left_maps : Set.MapsTo f C.left D.left
  right_maps : Set.MapsTo f C.right D.right

@[ext]
theorem Hom.ext {C D : ExcisiveTriad.{u}} {f g : Hom C D} (h : f.f = g.f) : f = g := by
  rcases f with ⟨f, hf1, hf2⟩
  rcases g with ⟨g, hg1, hg2⟩
  simp_all

instance : Category (ExcisiveTriad.{u}) where
  Hom := Hom
  id C :=
    { f := 𝟙 C.X
      left_maps := fun _ hx => hx
      right_maps := fun _ hx => hx }
  comp f g :=
    { f := f.f ≫ g.f
      left_maps := fun _ hx => g.left_maps (f.left_maps hx)
      right_maps := fun _ hx => g.right_maps (f.right_maps hx) }
  id_comp f := Hom.ext (by simp)
  comp_id f := Hom.ext (by simp)
  assoc f g h := Hom.ext (by simp)

/-- Forget an excisive triad to its ambient space. -/
def ambientFunctor : ExcisiveTriad.{u} ⥤ TopCat.{u} where
  obj C := C.X
  map f := f.f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restrict an excisive triad to its ordered cover of the union subspace. -/
def coverFunctor : ExcisiveTriad.{u} ⥤ OrderedTwoSetCover.{u} where
  obj C := relativeCupOrderedTwoSetCover C.excisive
  map f := relativeCupOrderedTwoSetCoverMap f.f f.left_maps f.right_maps _ _
  map_id C := OrderedTwoSetCover.Hom.ext (by apply TopCat.hom_ext; ext x; rfl)
  map_comp f g := OrderedTwoSetCover.Hom.ext (by apply TopCat.hom_ext; ext x; rfl)

@[simp]
lemma ambientFunctor_obj (C : ExcisiveTriad.{u}) : ambientFunctor.obj C = C.X :=
  rfl

@[simp]
lemma ambientFunctor_map {C D : ExcisiveTriad.{u}} (f : C ⟶ D) :
    ambientFunctor.map f = f.f :=
  rfl

@[simp]
lemma coverFunctor_obj (C : ExcisiveTriad.{u}) :
    coverFunctor.obj C = relativeCupOrderedTwoSetCover C.excisive :=
  rfl

@[simp]
lemma coverFunctor_map {C D : ExcisiveTriad.{u}} (f : C ⟶ D) :
    coverFunctor.map f =
      relativeCupOrderedTwoSetCoverMap f.f f.left_maps f.right_maps _ _ :=
  rfl

end ExcisiveTriad

/-- The literal topological triple formed by the pulled-back left side of an
excisive triad, its union subspace, and the ambient space. -/
noncomputable abbrev relativeCupBoundaryTopTriple (T : ExcisiveTriad.{u}) :
    TopTriple.{u} :=
  let A' := relativeCupLeft T.left T.right
  ⟨CategoryTheory.ComposableArrows.mk₂
      (subspaceIncl A') (subspaceIncl (T.left ∪ T.right)),
    ⟨Topology.IsEmbedding.subtypeVal, Topology.IsEmbedding.subtypeVal⟩⟩

/-- Pair 12 of the relative-cup boundary triple is the union pair. -/
@[simp]
theorem relativeCupBoundaryTopTriple_pair12 (T : ExcisiveTriad.{u}) :
    topTriplePair12.obj (relativeCupBoundaryTopTriple T) =
      TopPair.ofSubset (T.left ∪ T.right) := by
  rfl

/-- Pair 01 of the relative-cup boundary triple is the pulled-back left
subset pair in the union subspace. -/
@[simp]
theorem relativeCupBoundaryTopTriple_pair01 (T : ExcisiveTriad.{u}) :
    topTriplePair01.obj (relativeCupBoundaryTopTriple T) =
      TopPair.ofSubset (relativeCupLeft T.left T.right) := by
  rfl

/-! ## Nested closed pairs are excisive -/

/-- Nested closed pairs are excisive: when `B ⊆ A`, the left side pulls back
to the whole union subspace.  In particular, complements of nested opens are
always excisive. -/
theorem isRelativeCupExcisive_of_subset_left {X : TopCat.{w}} {A B : Set X}
    (h : B ⊆ A) : IsRelativeCupExcisive A B := by
  have hleft : relativeCupLeft A B = Set.univ := by
    ext x
    constructor
    · intro
      trivial
    · intro _
      change x.1 ∈ A
      have hx : x.1 ∈ A ∪ B := x.2
      rw [Set.mem_union] at hx
      rcases hx with hxA | hxB
      · exact hxA
      · exact h hxB
  rw [IsRelativeCupExcisive, hleft, interior_univ, Set.univ_union]

/-- Nested closed pairs are excisive: when `A ⊆ B`, the right side pulls back
to the whole union subspace. -/
theorem isRelativeCupExcisive_of_subset_right {X : TopCat.{w}} {A B : Set X}
    (h : A ⊆ B) : IsRelativeCupExcisive A B := by
  have hright : relativeCupRight A B = Set.univ := by
    ext x
    constructor
    · intro
      trivial
    · intro _
      change x.1 ∈ B
      have hx : x.1 ∈ A ∪ B := x.2
      rw [Set.mem_union] at hx
      rcases hx with hxA | hxB
      · exact h hxA
      · exact hxB
  rw [IsRelativeCupExcisive, hright, interior_univ, Set.union_univ]

end AlgebraicTopology
