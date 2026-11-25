/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author : @toskua
-/
module

public import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Subspace inclusions and maps in `TopCat`

Coefficient-independent subspace morphisms extracted from singular homology.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicTopology

universe w v u

section SubspaceGeneral

variable {X : TopCat.{w}} (S : Set X)

/-- Inclusion of subspace `S ⊆ X` as TopCat morphism. -/
noncomputable def subspaceIncl : TopCat.of S ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance : Mono (subspaceIncl S) := by
  rw [TopCat.mono_iff_injective]
  exact Subtype.val_injective

end SubspaceGeneral

section SubspaceInclOfSubset

variable {X : TopCat.{w}} {S T : Set X}

/-- Inclusion of subspace `S` into subspace `T` when `S ⊆ T`. -/
noncomputable def subspaceInclOfSubset (h : S ⊆ T) : TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom ⟨fun x => ⟨x.1, h x.2⟩, by fun_prop⟩

@[reassoc]
lemma subspaceInclOfSubset_comp (h : S ⊆ T) :
    subspaceInclOfSubset (X := X) h ≫ subspaceIncl T = subspaceIncl S := by
  apply TopCat.hom_ext
  ext x
  rfl

end SubspaceInclOfSubset

section SubspaceMap

variable {X Y : TopCat.{w}} {S : Set X} {T : Set Y}

/-- Coefficient-independent restriction of a `TopCat` morphism to subspaces. -/
noncomputable def subspaceMap (f : X ⟶ Y) (h : Set.MapsTo f S T) :
    TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom
    ⟨fun x => ⟨f x.1, h x.2⟩, by
      have hcont : Continuous (fun x : ↥S => f x.1) :=
        f.hom.continuous.comp continuous_subtype_val
      exact hcont.subtype_mk (fun x => h x.2)⟩

theorem subspaceMap_proof_irrel (f : X ⟶ Y) (h₁ h₂ : Set.MapsTo f S T) :
    subspaceMap f h₁ = subspaceMap f h₂ := by
  apply TopCat.hom_ext
  ext x
  rfl

@[simp]
lemma subspaceMap_id (h : Set.MapsTo (𝟙 X) S S) :
    subspaceMap (𝟙 X) h = 𝟙 (TopCat.of S) := by
  apply TopCat.hom_ext
  ext x
  rfl

lemma subspaceMap_id_of (S : Set X) :
    subspaceMap (𝟙 X) (fun _ hx => hx : Set.MapsTo (𝟙 X) S S) = 𝟙 (TopCat.of S) :=
  subspaceMap_id _

@[simp]
lemma subspaceMap_comp {Z : TopCat.{w}} {U : Set Z} {f : X ⟶ Y} {g : Y ⟶ Z}
    {hf : Set.MapsTo f S T} {hg : Set.MapsTo g T U}
    {hfg : Set.MapsTo (f ≫ g) S U} :
    subspaceMap (f ≫ g) hfg = subspaceMap f hf ≫ subspaceMap g hg := by
  apply TopCat.hom_ext
  ext x
  rfl

lemma subspaceMap_comp_of {Z : TopCat.{w}} {U : Set Z} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g T U) :
    subspaceMap (f ≫ g) (fun _ hx => hg (hf hx)) =
      subspaceMap f hf ≫ subspaceMap g hg :=
  subspaceMap_comp

@[reassoc]
lemma subspaceMap_comp_subspaceIncl (f : X ⟶ Y) (h : Set.MapsTo f S T) :
    subspaceMap f h ≫ subspaceIncl T = subspaceIncl S ≫ f := by
  apply TopCat.hom_ext
  ext x
  rfl

end SubspaceMap

end AlgebraicTopology
