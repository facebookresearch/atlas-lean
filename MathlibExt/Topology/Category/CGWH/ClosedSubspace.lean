/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Basic

/-!
# Closed subspaces of compactly generated weak Hausdorff spaces

A closed subset of a CGWH space is again a CGWH space.  This file bundles
that closed subspace and provides its canonical inclusion maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory TopologicalSpace

namespace CGWH

/-- A closed subset of a CGWH space, bundled as a CGWH space. -/
abbrev closedSubspace (X : CGWH.{u, v})
    (A : TopologicalSpace.Closeds X) : CGWH.{u, v} := by
  let hCompactlyGenerated : UCompactlyGeneratedSpace.{u} A := by
    apply uCompactlyGeneratedSpace_of_isClosed
    intro s hs
    rw [A.isClosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed]
    apply UCompactlyGeneratedSpace.isClosed
    intro K g
    let P : Set K := g ⁻¹' (A : Set X)
    have hP : IsClosed P := A.isClosed.preimage g.continuous
    let _ : CompactSpace P := isCompact_iff_compactSpace.mp hP.isCompact
    let KP : CompHaus.{u} := CompHaus.of P
    let gA : C(KP, A) :=
      ⟨fun z ↦ ⟨g z.1, z.2⟩,
        (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hs' : IsClosed (gA ⁻¹' s) := hs KP gA
    have hsImage : IsClosed (Subtype.val '' (gA ⁻¹' s)) :=
      hP.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp hs'
    have hImage : Subtype.val '' (gA ⁻¹' s) =
        g ⁻¹' (Subtype.val '' s) := by
      ext k
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨gA z, hz, rfl⟩
      · rintro ⟨a, ha, hga⟩
        let z : P := ⟨k, by
          change g k ∈ A
          rw [← hga]
          exact a.2⟩
        refine ⟨z, ?_, rfl⟩
        change gA z ∈ s
        have hz : gA z = a := by
          apply Subtype.ext
          exact hga.symm
        rw [hz]
        exact ha
    exact hImage ▸ hsImage
  let _ : UCompactlyGeneratedSpace.{u} A := hCompactlyGenerated
  let hWeakHausdorff : UWeakHausdorffSpace.{u} A := by
    rw [uWeakHausdorffSpace_iff_isClosed_equalizer]
    intro K f g
    let i : C(A, X) := ContinuousMap.subtypeVal (A : Set X)
    have h :=
      (uWeakHausdorffSpace_iff_isClosed_equalizer.mp
        (inferInstance : UWeakHausdorffSpace.{u} X)) K (i.comp f) (i.comp g)
    convert h using 1
    ext k
    change (f k = g k) ↔ ((f k : X) = (g k : X))
    exact Subtype.ext_iff
  let _ : UWeakHausdorffSpace.{u} A := hWeakHausdorff
  exact CGWH.of A

/-- The canonical inclusion of a closed subspace into its ambient space. -/
def closedSubspaceι (X : CGWH.{u, v})
    (A : TopologicalSpace.Closeds X) :
    closedSubspace X A ⟶ X :=
  ConcreteCategory.ofHom (ContinuousMap.subtypeVal (A : Set X))

/-- The canonical inclusion induced by an inclusion of closed subsets. -/
def closedSubspaceInclusion (X : CGWH.{u, v})
    {A B : TopologicalSpace.Closeds X} (h : A ≤ B) :
    closedSubspace X A ⟶ closedSubspace X B :=
  ConcreteCategory.ofHom
    ⟨fun x ↦ ⟨x.1, h x.2⟩, continuous_subtype_val.subtype_mk _⟩

@[simp]
theorem closedSubspaceι_apply (X : CGWH.{u, v})
    (A : TopologicalSpace.Closeds X) (x : closedSubspace X A) :
    closedSubspaceι X A x = (x : X) :=
  rfl

@[simp]
theorem closedSubspaceInclusion_apply (X : CGWH.{u, v})
    {A B : TopologicalSpace.Closeds X} (h : A ≤ B)
    (x : closedSubspace X A) :
    closedSubspaceInclusion X h x =
      (⟨(x : X), h x.2⟩ : B) :=
  rfl

theorem closedSubspaceInclusion_comp_ι (X : CGWH.{u, v})
    {A B : TopologicalSpace.Closeds X} (h : A ≤ B) :
    closedSubspaceInclusion X h ≫ closedSubspaceι X B =
      closedSubspaceι X A := by
  ext x
  rfl

@[simp]
theorem closedSubspaceInclusion_refl (X : CGWH.{u, v})
    (A : TopologicalSpace.Closeds X) :
    closedSubspaceInclusion X (le_refl A) = 𝟙 (closedSubspace X A) := by
  ext x
  rfl

theorem closedSubspaceInclusion_trans (X : CGWH.{u, v})
    {A B C : TopologicalSpace.Closeds X}
    (hAB : A ≤ B) (hBC : B ≤ C) :
    closedSubspaceInclusion X hAB ≫ closedSubspaceInclusion X hBC =
      closedSubspaceInclusion X (hAB.trans hBC) := by
  ext x
  rfl

theorem closedSubspaceι_isClosedEmbedding (X : CGWH.{u, v})
    (A : TopologicalSpace.Closeds X) :
    Topology.IsClosedEmbedding (closedSubspaceι X A) :=
  A.isClosed.isClosedEmbedding_subtypeVal

theorem closedSubspaceInclusion_isClosedEmbedding (X : CGWH.{u, v})
    {A B : TopologicalSpace.Closeds X} (h : A ≤ B) :
    Topology.IsClosedEmbedding (closedSubspaceInclusion X h) := by
  apply Topology.IsClosedEmbedding.of_comp
    (closedSubspaceι_isClosedEmbedding X B).isEmbedding
  convert closedSubspaceι_isClosedEmbedding X A using 1
  funext x
  rfl

end CGWH
