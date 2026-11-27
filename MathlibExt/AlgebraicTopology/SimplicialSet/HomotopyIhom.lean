/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.HoComp
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyComp
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-!
# Simplicial homotopies and edges of internal homs

For arbitrary simplicial sets, a cylinder map `X × Δ[1] → Y` with its two strict
endpoint maps determines a simplicial homotopy. Currying identifies such a homotopy
from `f` to `g` with an edge of the internal hom `Fun(X,Y)` between the vertices
classified by `f` and `g`. Uncurrying gives the inverse correspondence on the full
homotopy and edge data.

The constant homotopy corresponds to the identity edge, and postcomposition is
compatible with the correspondence on underlying one-simplices. Cartesian products
of edge-composition witnesses also give the commuting tensor square in the homotopy
category. All simplicial sets in these constructions lie in the same universe.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {X Y Z C : SSet.{u}}

/-!
## Cartesian products of edges and composition witnesses

A simplex of the cartesian product of simplicial sets is a pair of simplices.
Pairing two edge-composition triangles gives a composition triangle of the product
edges, and the two paths around the square determined by a pair of edges agree
in the homotopy category of the product.
-/

namespace Edge

/--
Given composition triangles for edges in two simplicial sets, their paired
two-simplex gives a composition triangle for the corresponding product edges.
-/
def CompStruct.tensor {A B : SSet.{u}}
    {x₀ x₁ x₂ : A _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (hx : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    {y₀ y₁ y₂ : B _⦋0⦌} {e'₀₁ : Edge y₀ y₁} {e'₁₂ : Edge y₁ y₂} {e'₀₂ : Edge y₀ y₂}
    (hy : Edge.CompStruct e'₀₁ e'₁₂ e'₀₂) :
    Edge.CompStruct (e₀₁.tensor e'₀₁) (e₁₂.tensor e'₁₂)
      (e₀₂.tensor e'₀₂) where
  simplex := (hx.simplex, hy.simplex)
  d₂ := Prod.ext hx.d₂ hy.d₂
  d₀ := Prod.ext hx.d₀ hy.d₀
  d₁ := Prod.ext hx.d₁ hy.d₁

/--
For edges `e_x` and `e_y`, the two composites around the square formed by
`e_x ⊗ id` and `id ⊗ e_y` are equal in the homotopy category of the product.
-/
theorem tensor_square {A B : SSet.{u}} {x₀ x₁ : A _⦋0⦌} (ex : Edge x₀ x₁)
    {y₀ y₁ : B _⦋0⦌} (ey : Edge y₀ y₁) :
    HomotopyCategory.homMk (ex.tensor (.id y₀)) ≫
        HomotopyCategory.homMk (Edge.tensor (.id x₁) ey) =
      HomotopyCategory.homMk (Edge.tensor (.id x₀) ey) ≫
        HomotopyCategory.homMk (ex.tensor (.id y₁)) := by
  rw [HomotopyCategory.homMk_comp_homMk
      ((Edge.CompStruct.idComp ex).tensor (Edge.CompStruct.compId ey)),
    HomotopyCategory.homMk_comp_homMk
      ((Edge.CompStruct.compId ex).tensor (Edge.CompStruct.idComp ey))]

/--
The one-simplex underlying the image of an edge under a simplicial map is the
Yoneda simplex represented by the edge's simplex map followed by that simplicial map.
-/
lemma map_edge_yoneda {a b : X _⦋0⦌} (e : Edge a b) (θ : X ⟶ Z) :
    (e.map θ).edge = yonedaEquiv (yonedaEquiv.symm e.edge ≫ θ) := by
  rw [Edge.map_edge]
  conv_lhs => rw [← Equiv.apply_symm_apply yonedaEquiv e.edge]
  exact (yonedaEquiv_comp _ _).symm

end Edge

/-!
## Cylinder homotopies with prescribed endpoints

A map `h : X × Δ[1] → Y` with `ι₀ ≫ h = f` and `ι₁ ≫ h = g` gives a homotopy
from `f` to `g`. The constant homotopy on `f` has cylinder map equal to the first
projection followed by `f`.
-/

namespace Homotopy

variable {f g : X ⟶ Y}

/--
A cylinder map `h : X × Δ[1] → Y` satisfying `ι₀ ≫ h = f` and `ι₁ ≫ h = g`
determines a homotopy from `f` to `g`.
-/
def mkOfH (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y)
    (h₀ : SSet.ι₀ ≫ h = f) (h₁ : SSet.ι₁ ≫ h = g) : Homotopy f g where
  h := h
  h₀ := h₀
  h₁ := h₁
  rel := by ext n ⟨⟨x, hx⟩, t⟩; cases hx

/--
The cylinder map underlying the homotopy assembled from `h` and its endpoint
equations is exactly `h`.
-/
@[simp]
lemma mkOfH_h (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y)
    (h₀ : SSet.ι₀ ≫ h = f) (h₁ : SSet.ι₁ ≫ h = g) :
    (mkOfH h h₀ h₁).h = h :=
  rfl

/--
The homotopy from `f` to itself whose cylinder map is the projection
`X × Δ[1] → X` followed by `f`.
-/
noncomputable def reflH (f : X ⟶ Y) : Homotopy f f :=
  mkOfH (fst X (Δ[1] : SSet.{u}) ≫ f) (by simp) (by simp)

/--
The cylinder map of the constant homotopy on `f` is the first projection followed
by `f`.
-/
@[simp]
lemma reflH_h (f : X ⟶ Y) : (reflH f).h = fst X (Δ[1] : SSet.{u}) ≫ f :=
  rfl

end Homotopy

/-!
## Currying homotopies into internal-hom edges

Currying a cylinder homotopy gives a one-simplex of `Fun(X,Y)` whose endpoints
are the vertices classified by the two endpoint maps. Uncurrying the one-simplex
recovers the same cylinder map and the strict endpoint equations.
-/

/-- The face inclusion `Δ[0] ⟶ Δ[1]` at vertex `0` is the Yoneda name of
that vertex. -/
private lemma deltaOne_δ_one_eq :
    stdSimplex.δ (1 : Fin 2) =
      yonedaEquiv.symm (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rw [show stdSimplex.δ (1 : Fin 2) =
      stdSimplex.δ (1 : Fin 2) ≫ 𝟙 (Δ[1] : SSet.{u}) from (Category.comp_id _).symm]
  rw [stdSimplex.yonedaEquiv_δ_comp]
  ext k
  fin_cases k
  rfl

/-- The face inclusion `Δ[0] ⟶ Δ[1]` at vertex `1` is the Yoneda name of
that vertex. -/
private lemma deltaOne_δ_zero_eq :
    stdSimplex.δ (0 : Fin 2) =
      yonedaEquiv.symm (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  rw [show stdSimplex.δ (0 : Fin 2) =
      stdSimplex.δ (0 : Fin 2) ≫ 𝟙 (Δ[1] : SSet.{u}) from (Category.comp_id _).symm]
  rw [stdSimplex.yonedaEquiv_δ_comp]
  ext k
  fin_cases k
  rfl

private lemma rightUnitor_hom_comp_ι₀ :
    (ρ_ X).hom ≫ (SSet.ι₀ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) =
      X ◁ (Δ0IsoUnit.inv ≫ stdSimplex.δ (1 : Fin 2)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, SSet.ι₀_fst, Category.comp_id,
      CartesianMonoidalCategory.whiskerLeft_fst,
      CartesianMonoidalCategory.rightUnitor_hom]
  · rw [Category.assoc, SSet.ι₀_snd, CartesianMonoidalCategory.whiskerLeft_snd,
      ← Category.assoc, deltaOne_δ_one_eq, yonedaEquiv_symm_zero]
    simp only [SSet.comp_const]

private lemma rightUnitor_hom_comp_ι₁ :
    (ρ_ X).hom ≫ (SSet.ι₁ : X ⟶ X ⊗ (Δ[1] : SSet.{u})) =
      X ◁ (Δ0IsoUnit.inv ≫ stdSimplex.δ (0 : Fin 2)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, SSet.ι₁_fst, Category.comp_id,
      CartesianMonoidalCategory.whiskerLeft_fst,
      CartesianMonoidalCategory.rightUnitor_hom]
  · rw [Category.assoc, SSet.ι₁_snd, CartesianMonoidalCategory.whiskerLeft_snd,
      ← Category.assoc, deltaOne_δ_zero_eq, yonedaEquiv_symm_zero]
    simp only [SSet.comp_const]

variable {f g : X ⟶ C}

private lemma curry_ι₀_vertex (K : X ⊗ (Δ[1] : SSet.{u}) ⟶ C) :
    ((ihom X).obj C).δ (1 : Fin 2)
        (yonedaEquiv (MonoidalClosed.curry K)) =
      ihomVertexEquiv X C (SSet.ι₀ ≫ K) := by
  have key : Δ0IsoUnit.inv ≫ (stdSimplex.δ (1 : Fin 2) ≫
        MonoidalClosed.curry K) =
      MonoidalClosed.curry' (SSet.ι₀ ≫ K) := by
    change Δ0IsoUnit.inv ≫ (stdSimplex.δ (1 : Fin 2) ≫
        MonoidalClosed.curry K) =
      MonoidalClosed.curry ((ρ_ X).hom ≫ (SSet.ι₀ ≫ K))
    rw [← Category.assoc, ← MonoidalClosed.curry_natural_left,
      ← rightUnitor_hom_comp_ι₀, Category.assoc]
  calc ((ihom X).obj C).δ (1 : Fin 2)
        (yonedaEquiv (MonoidalClosed.curry K))
      = yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry K) :=
        (stdSimplex.yonedaEquiv_δ_comp _ _).symm
    _ = unitHomEquiv _ (Δ0IsoUnit.inv ≫
          (stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry K)) :=
        yonedaEquiv_eq_unitHomEquiv _ _
    _ = unitHomEquiv _ (MonoidalClosed.curry' (SSet.ι₀ ≫ K)) := by rw [key]
    _ = ihomVertexEquiv X C (SSet.ι₀ ≫ K) := (ihomVertexEquiv_eq X C _).symm

private lemma curry_ι₁_vertex (K : X ⊗ (Δ[1] : SSet.{u}) ⟶ C) :
    ((ihom X).obj C).δ (0 : Fin 2)
        (yonedaEquiv (MonoidalClosed.curry K)) =
      ihomVertexEquiv X C (SSet.ι₁ ≫ K) := by
  have key : Δ0IsoUnit.inv ≫ (stdSimplex.δ (0 : Fin 2) ≫
        MonoidalClosed.curry K) =
      MonoidalClosed.curry' (SSet.ι₁ ≫ K) := by
    change Δ0IsoUnit.inv ≫ (stdSimplex.δ (0 : Fin 2) ≫
        MonoidalClosed.curry K) =
      MonoidalClosed.curry ((ρ_ X).hom ≫ (SSet.ι₁ ≫ K))
    rw [← Category.assoc, ← MonoidalClosed.curry_natural_left,
      ← rightUnitor_hom_comp_ι₁, Category.assoc]
  calc ((ihom X).obj C).δ (0 : Fin 2)
        (yonedaEquiv (MonoidalClosed.curry K))
      = yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry K) :=
        (stdSimplex.yonedaEquiv_δ_comp _ _).symm
    _ = unitHomEquiv _ (Δ0IsoUnit.inv ≫
          (stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry K)) :=
        yonedaEquiv_eq_unitHomEquiv _ _
    _ = unitHomEquiv _ (MonoidalClosed.curry' (SSet.ι₁ ≫ K)) := by rw [key]
    _ = ihomVertexEquiv X C (SSet.ι₁ ≫ K) := (ihomVertexEquiv_eq X C _).symm

/--
A homotopy from `f` to `g` gives an edge of `Fun(X,C)` between the vertices
classified by `f` and `g`, by currying its cylinder map.
-/
noncomputable def Homotopy.edgeIhom (K : Homotopy f g) :
    ((ihom X).obj C).Edge (ihomVertexEquiv X C f) (ihomVertexEquiv X C g) :=
  Edge.mk (yonedaEquiv (MonoidalClosed.curry K.h))
    (by rw [curry_ι₀_vertex, K.h₀]) (by rw [curry_ι₁_vertex, K.h₁])

/--
The one-simplex underlying the internal-hom edge of a homotopy is the Yoneda
simplex represented by the curried cylinder map.
-/
theorem Homotopy.edgeIhom_edge (K : Homotopy f g) :
    K.edgeIhom.edge = yonedaEquiv (MonoidalClosed.curry K.h) :=
  rfl

/--
An edge of `Fun(X,C)` between the vertices classified by `f` and `g` gives a
homotopy from `f` to `g` by uncurrying its one-simplex.
-/
noncomputable def Homotopy.ofIhomEdge
    (e : ((ihom X).obj C).Edge (ihomVertexEquiv X C f) (ihomVertexEquiv X C g)) :
    Homotopy f g :=
  Homotopy.mkOfH (MonoidalClosed.uncurry (yonedaEquiv.symm e.edge))
    (by
      apply (ihomVertexEquiv X C).injective
      rw [← curry_ι₀_vertex, MonoidalClosed.curry_uncurry,
        Equiv.apply_symm_apply, e.src_eq])
    (by
      apply (ihomVertexEquiv X C).injective
      rw [← curry_ι₁_vertex, MonoidalClosed.curry_uncurry,
        Equiv.apply_symm_apply, e.tgt_eq])

/--
The cylinder map of the homotopy classified by an internal-hom edge is the
uncurrying of the Yoneda map represented by its one-simplex.
-/
lemma Homotopy.ofIhomEdge_h
    (e : ((ihom X).obj C).Edge (ihomVertexEquiv X C f) (ihomVertexEquiv X C g)) :
    (Homotopy.ofIhomEdge e).h = MonoidalClosed.uncurry (yonedaEquiv.symm e.edge) := rfl

/--
Taking the internal-hom edge of the homotopy recovered from an edge returns
that entire edge.
-/
lemma Homotopy.edgeIhom_ofIhomEdge
    (e : ((ihom X).obj C).Edge (ihomVertexEquiv X C f) (ihomVertexEquiv X C g)) :
    (Homotopy.ofIhomEdge e).edgeIhom = e := by
  apply Edge.ext
  rw [Homotopy.edgeIhom_edge, Homotopy.ofIhomEdge_h,
    MonoidalClosed.curry_uncurry, Equiv.apply_symm_apply]

/--
Recovering a homotopy from its internal-hom edge returns that entire homotopy.
-/
lemma Homotopy.ofIhomEdge_edgeIhom (H : Homotopy f g) :
    Homotopy.ofIhomEdge H.edgeIhom = H := by
  apply RelativeMorphism.Homotopy.ext
  change MonoidalClosed.uncurry
    (yonedaEquiv.symm (yonedaEquiv (MonoidalClosed.curry H.h))) = H.h
  rw [Equiv.symm_apply_apply, MonoidalClosed.uncurry_curry]

namespace Homotopy

/--
The internal-hom edge classified by the constant homotopy on `f` is the identity
edge at the vertex classified by `f`.
-/
lemma edgeIhom_reflH (f : X ⟶ C) :
    (reflH f).edgeIhom = Edge.id (ihomVertexEquiv X C f) := by
  apply Edge.ext
  rw [Homotopy.edgeIhom_edge, Edge.id_edge, ← Equiv.eq_symm_apply]
  change MonoidalClosed.curry (fst X (Δ[1] : SSet.{u}) ≫ f) =
    yonedaEquiv.symm (((ihom X).obj C).σ 0 (ihomVertexEquiv X C f))
  rw [← stdSimplex.σ_comp_yonedaEquiv_symm, yonedaEquiv_symm_ihomVertexEquiv]
  change MonoidalClosed.curry (fst X (Δ[1] : SSet.{u}) ≫ f) =
    (stdSimplex.σ (0 : Fin 1) ≫ Δ0IsoUnit.hom) ≫
      MonoidalClosed.curry ((ρ_ X).hom ≫ f)
  have hu : (X ◁ (stdSimplex.σ (0 : Fin 1) ≫ Δ0IsoUnit.hom)) ≫ (ρ_ X).hom =
      fst X (Δ[1] : SSet.{u}) := by
    rw [CartesianMonoidalCategory.rightUnitor_hom,
      CartesianMonoidalCategory.whiskerLeft_fst]
  calc MonoidalClosed.curry (fst X (Δ[1] : SSet.{u}) ≫ f)
      = MonoidalClosed.curry (((X ◁ (stdSimplex.σ (0 : Fin 1) ≫
            Δ0IsoUnit.hom)) ≫ (ρ_ X).hom) ≫ f) := by rw [hu]
    _ = MonoidalClosed.curry ((X ◁ (stdSimplex.σ (0 : Fin 1) ≫
            Δ0IsoUnit.hom)) ≫ ((ρ_ X).hom ≫ f)) := by rw [Category.assoc]
    _ = (stdSimplex.σ (0 : Fin 1) ≫ Δ0IsoUnit.hom) ≫
          MonoidalClosed.curry ((ρ_ X).hom ≫ f) :=
        MonoidalClosed.curry_natural_left _ _

/--
On underlying one-simplices, mapping the internal-hom edge by postcomposition with
`q` equals the internal-hom edge of the homotopy postcomposed with `q`.
-/
lemma edgeIhom_map_ihomMap_edge {f g : X ⟶ Y} (K : Homotopy f g) (q : Y ⟶ C) :
    (K.edgeIhom.map ((ihom X).map q)).edge = (K.postcomp q).edgeIhom.edge := by
  rw [Edge.map_edge_yoneda, Homotopy.edgeIhom_edge, Homotopy.edgeIhom_edge]
  change yonedaEquiv (yonedaEquiv.symm (yonedaEquiv (MonoidalClosed.curry K.h)) ≫
      (ihom X).map q) = yonedaEquiv (MonoidalClosed.curry (K.h ≫ q))
  rw [Equiv.symm_apply_apply, ← MonoidalClosed.curry_natural_right]

end Homotopy

end SSet
