/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-!
# Internal-hom components and Kan–Quillen homotopy-category morphisms

For any simplicial set `K` and Kan complex `L`, the connected components of
`(ihom K).obj L` classify the morphisms from `K` to `L` in the localization
at realization weak equivalences. The forward map applies the localization
functor to the actual map classified by a vertex.

The proof uses the existing internal-hom edge dictionary and the fundamental
lemma of model categories. A model left homotopy is represented on the
existing good standard cylinder `K ⊗ Δ[1]`, so it gives an edge between the
same two internal-hom vertices. Every simplicial set is cofibrant; only the
target is required to be Kan. The forward map and its naturality statements
also apply to targets which are not Kan.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u u' v'

open CategoryTheory HomotopicalAlgebra MonoidalClosed
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

namespace SSet.modelCategoryQuillen

private theorem leftHomotopyRel_of_simplicialHomotopy
    {K L : SSet.{u}} {f g : K ⟶ L} (h : SSet.Homotopy f g) :
    LeftHomotopyRel f g := by
  refine ⟨standardCylinder K, ⟨?_⟩⟩
  exact { h := h.h, h₀ := h.h₀, h₁ := h.h₁ }

variable {H : Type u'} [Category.{v'} H]
    (G : SSet.{u} ⥤ H) [G.IsLocalization (weakEquivalences SSet.{u})]

/-- Apply the localization functor to the actual map classified by an
internal-hom vertex, then descend along the native connected-component
quotient. This construction does not require a Kan target. -/
def ihomPiZeroToHom (K L : SSet.{u}) :
    π₀ ((ihom K).obj L) → (G.obj K ⟶ G.obj L) :=
  π₀.lift (fun v ↦ G.map ((ihomVertexEquiv K L).symm v)) (by
    intro x y e
    have e' : ((ihom K).obj L).Edge
        (ihomVertexEquiv K L ((ihomVertexEquiv K L).symm x))
        (ihomVertexEquiv K L ((ihomVertexEquiv K L).symm y)) := by
      simpa only [Equiv.apply_symm_apply] using e
    exact (leftHomotopyRel_of_simplicialHomotopy
      (SSet.Homotopy.ofIhomEdge e')).factorsThroughLocalization.map_eq G)

/-- On the component of the vertex classified by `f`, the component map is
literally the image of `f` under the localization functor. -/
@[simp] theorem ihomPiZeroToHom_mk {K L : SSet.{u}} (f : K ⟶ L) :
    ihomPiZeroToHom G K L (π₀.mk (ihomVertexEquiv K L f)) = G.map f := by
  simp [ihomPiZeroToHom]

/-- Precomposing the actual classified map agrees with the map on
internal-hom components induced by `MonoidalClosed.pre`. -/
theorem ihomPiZeroToHom_source {K K' L : SSet.{u}}
    (a : K' ⟶ K) (c : π₀ ((ihom K).obj L)) :
    ihomPiZeroToHom G K' L (mapπ₀ ((MonoidalClosed.pre a).app L) c) =
      G.map a ≫ ihomPiZeroToHom G K L c := by
  obtain ⟨v, rfl⟩ := π₀.mk_surjective c
  obtain ⟨f, rfl⟩ := (ihomVertexEquiv K L).surjective v
  rw [mapπ₀_mk, ihomVertexEquiv_pre_app, ihomPiZeroToHom_mk,
    ihomPiZeroToHom_mk, G.map_comp]

/-- Postcomposing the actual classified map agrees with the map on
internal-hom components induced by the internal-hom functor. -/
theorem ihomPiZeroToHom_target {K L L' : SSet.{u}}
    (b : L ⟶ L') (c : π₀ ((ihom K).obj L)) :
    ihomPiZeroToHom G K L' (mapπ₀ ((ihom K).map b) c) =
      ihomPiZeroToHom G K L c ≫ G.map b := by
  obtain ⟨v, rfl⟩ := π₀.mk_surjective c
  obtain ⟨f, rfl⟩ := (ihomVertexEquiv K L).surjective v
  rw [mapπ₀_mk, ihomVertexEquiv_ihom_map, ihomPiZeroToHom_mk,
    ihomPiZeroToHom_mk, G.map_comp]

/-- For a Kan target, equality of the two native internal-hom components is
equivalent to equality of the images of the same maps in the localization. -/
theorem ihomPiZero_mk_eq_iff_map_eq {K L : SSet.{u}} [KanComplex L]
    (f g : K ⟶ L) :
    π₀.mk (ihomVertexEquiv K L f) = π₀.mk (ihomVertexEquiv K L g) ↔
      G.map f = G.map g := by
  constructor
  · intro h
    simpa only [ihomPiZeroToHom_mk] using
      congrArg (ihomPiZeroToHom G K L) h
  · intro h
    have hfg : LeftHomotopyRel f g := (LeftHomotopyRel.iff_map_eq G K L).2 h
    let hom := hfg.leftHomotopy (standardCylinder K)
    exact π₀.sound (SSet.Homotopy.mkOfH hom.h hom.h₀ hom.h₁).edgeIhom

/-- Internal-hom components classify morphisms in any localization at the
selected Kan–Quillen weak equivalences when the target is Kan. The map is
the component map above; surjectivity is the existing fundamental lemma. -/
def ihomPiZeroHomEquivOfIsLocalization (K L : SSet.{u}) [KanComplex L] :
    π₀ ((ihom K).obj L) ≃ (G.obj K ⟶ G.obj L) :=
  Equiv.ofBijective (ihomPiZeroToHom G K L) (by
    constructor
    · intro c d h
      obtain ⟨v, rfl⟩ := π₀.mk_surjective c
      obtain ⟨w, rfl⟩ := π₀.mk_surjective d
      obtain ⟨f, rfl⟩ := (ihomVertexEquiv K L).surjective v
      obtain ⟨g, rfl⟩ := (ihomVertexEquiv K L).surjective w
      apply (ihomPiZero_mk_eq_iff_map_eq G f g).2
      simpa only [ihomPiZeroToHom_mk] using h
    · intro h
      obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization G K L h
      exact ⟨π₀.mk (ihomVertexEquiv K L f), ihomPiZeroToHom_mk G f⟩)

/-- The localization-general bijection preserves the actual classified
vertex and its image under the original localization functor. -/
@[simp] theorem ihomPiZeroHomEquivOfIsLocalization_mk
    {K L : SSet.{u}} [KanComplex L] (f : K ⟶ L) :
    ihomPiZeroHomEquivOfIsLocalization G K L
        (π₀.mk (ihomVertexEquiv K L f)) = G.map f :=
  ihomPiZeroToHom_mk G f

variable (K L : SSet.{u}) [KanComplex L]

/-- The canonical Kan–Quillen localization identifies internal-hom
components with homotopy-category morphisms, for arbitrary `K` and Kan `L`. -/
def ihomPiZeroHomEquiv :
    π₀ ((ihom K).obj L) ≃
      ((toHomotopyCategory SSet.{u}).obj K ⟶
        (toHomotopyCategory SSet.{u}).obj L) :=
  ihomPiZeroHomEquivOfIsLocalization (toHomotopyCategory SSet.{u}) K L

/-- The canonical bijection sends the component of the vertex classified
by `f` to the localization image of the same `f`. -/
@[simp] theorem ihomPiZeroHomEquiv_mk (f : K ⟶ L) :
    ihomPiZeroHomEquiv K L (π₀.mk (ihomVertexEquiv K L f)) =
      (toHomotopyCategory SSet.{u}).map f :=
  ihomPiZeroHomEquivOfIsLocalization_mk _ f

end SSet.modelCategoryQuillen
