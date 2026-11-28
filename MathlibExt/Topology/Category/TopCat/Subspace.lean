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

For topological spaces in the given universe, subset inclusions and
restrictions of continuous maps define morphisms between the induced
subspaces. These restrictions preserve identities and composition, are
independent of the chosen subset-inclusion proof, and commute with the
inclusions into the ambient spaces.
-/

@[expose] public section

open CategoryTheory

namespace TopCat

universe w v u

section SubspaceGeneral

variable {X : TopCat.{w}} (S : Set X)

/-- For a topological space `X` and subset `S ⊆ X`, the inclusion of the
subspace `S` into `X` is a continuous morphism in `TopCat`. -/
noncomputable def subspaceIncl : TopCat.of S ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance : Mono (subspaceIncl S) := by
  rw [TopCat.mono_iff_injective]
  exact Subtype.val_injective

end SubspaceGeneral

section SubspaceInclOfSubset

variable {X : TopCat.{w}} {S T : Set X}

/-- For subsets `S ⊆ T` of a topological space `X`, inclusion defines a
continuous morphism between their induced subspaces. -/
noncomputable def subspaceInclOfSubset (h : S ⊆ T) : TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom (ContinuousMap.inclusion h)

/-- For subsets `S ⊆ T ⊆ X`, the inclusion `S → T` followed by `T → X`
equals the direct subspace inclusion `S → X`. -/
@[reassoc]
lemma subspaceInclOfSubset_comp (h : S ⊆ T) :
    subspaceInclOfSubset (X := X) h ≫ subspaceIncl T = subspaceIncl S := by
  apply TopCat.hom_ext
  ext x
  rfl

end SubspaceInclOfSubset

section SubspaceMap

variable {X Y : TopCat.{w}} {S : Set X} {T : Set Y}

/-- For a continuous map `f : X → Y` between spaces in the same given
universe and subsets `S ⊆ X`, `T ⊆ Y` with `f(S) ⊆ T`, restricting `f`
gives a continuous morphism from the subspace `S` to the subspace `T`. -/
noncomputable def subspaceMap (f : X ⟶ Y) (h : Set.MapsTo f S T) :
    TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom
    ⟨fun x => ⟨f x.1, h x.2⟩, by
      have hcont : Continuous (fun x : ↥S => f x.1) :=
        f.hom.continuous.comp continuous_subtype_val
      exact hcont.subtype_mk (fun x => h x.2)⟩

/-- For a subset `S` of a space `X` and any proof that the identity of
`X` maps `S` into itself, its restriction is the identity of the subspace `S`. -/
@[simp]
lemma subspaceMap_id (h : Set.MapsTo (𝟙 X) S S) :
    subspaceMap (𝟙 X) h = 𝟙 (TopCat.of S) := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- For continuous maps `f : X → Y`, `g : Y → Z` in the same universe and
subsets `S`, `T`, `U` with `f(S) ⊆ T`, `g(T) ⊆ U`, restricting `f ≫ g`
to `S → U` equals the composite of the restrictions `S → T → U`,
independently of the given proof for the composite. -/
private lemma subspaceMap_comp_proofs {Z : TopCat.{w}} {U : Set Z} {f : X ⟶ Y} {g : Y ⟶ Z}
    {hf : Set.MapsTo f S T} {hg : Set.MapsTo g T U}
    {hfg : Set.MapsTo (f ≫ g) S U} :
    subspaceMap (f ≫ g) hfg = subspaceMap f hf ≫ subspaceMap g hg := by
  apply TopCat.hom_ext
  ext x
  rfl

/-- For continuous maps `f : X → Y`, `g : Y → Z` preserving the subsets
`S → T → U`, the restriction of `f ≫ g` using the composite subset proof
is the composite of the two restricted morphisms. -/
lemma subspaceMap_comp_of {Z : TopCat.{w}} {U : Set Z} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g T U) :
    subspaceMap (f ≫ g) (fun _ hx => hg (hf hx)) =
      subspaceMap f hf ≫ subspaceMap g hg :=
  subspaceMap_comp_proofs

/-- Restrictions preserving `S → T → U` compose to the restriction of the composite. -/
@[simp]
lemma subspaceMap_comp {Z : TopCat.{w}} {U : Set Z} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Set.MapsTo f S T) (hg : Set.MapsTo g T U) :
    subspaceMap f hf ≫ subspaceMap g hg =
      subspaceMap (f ≫ g) (fun _ hx => hg (hf hx)) :=
  (subspaceMap_comp_of f g hf hg).symm

/-- For a continuous map `f : X → Y` carrying `S ⊆ X` into `T ⊆ Y`,
restriction `S → T` followed by inclusion into `Y` equals inclusion of `S`
into `X` followed by `f`. -/
@[reassoc]
lemma subspaceMap_comp_subspaceIncl (f : X ⟶ Y) (h : Set.MapsTo f S T) :
    subspaceMap f h ≫ subspaceIncl T = subspaceIncl S ≫ f := by
  apply TopCat.hom_ext
  ext x
  rfl

end SubspaceMap

end TopCat
