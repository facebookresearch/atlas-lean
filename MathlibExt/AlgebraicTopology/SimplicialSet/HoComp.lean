/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-! # Internal composition on homotopy categories of functor objects

Neutral (pre-Joyal) infrastructure: external products of edges, and
internal composition
`SSet.hoComp X Y C : h Fun(X, Y) × h Fun(Y, C) ⥤ h Fun(X, C)` on
homotopy categories of internal-hom objects, built from
`MonoidalClosed.comp` and the binary-product inverse for the
`2`-truncated homotopy category functor. The fixed-first-argument
slice `SSet.hoCompSlice` at the vertex classified by `f : X ⟶ Y` is
precomposition with `f`
(`SSet.hoCompSlice_mk_ihomVertexEquiv_eq_hoPre`), and isomorphic
first arguments give naturally isomorphic slices
(`SSet.hoCompSliceIso`). This module knows nothing about Joyal
categorical equivalences; the Joyal detection theorem built on it is
`SSet.categoricalEquivalences.of_hoCompIso` in
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.EquivalenceCategorical`.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial

universe u

namespace SSet

namespace Edge

/-! ## External products of edges -/

variable {X Y : SSet.{u}}

/-- The external product of edges of simplicial sets: the `SSet`-level
companion of `SSet.Truncated.Edge.tensor`, with `1`-simplex the pair of the
`1`-simplices. -/
def tensor {x x' : X _⦋0⦌} (e₁ : Edge x x') {y y' : Y _⦋0⦌}
    (e₂ : Edge y y') :
    Edge (X := X ⊗ Y) (x, y) (x', y') where
  edge := (e₁.edge, e₂.edge)
  src_eq := Prod.ext e₁.src_eq e₂.src_eq
  tgt_eq := Prod.ext e₁.tgt_eq e₂.tgt_eq

/-- The `1`-simplex underlying an external product of edges is the pair of
the underlying `1`-simplices. -/
@[simp]
lemma tensor_edge {x x' : X _⦋0⦌} (e₁ : Edge x x') {y y' : Y _⦋0⦌}
    (e₂ : Edge y y') : (e₁.tensor e₂).edge = (e₁.edge, e₂.edge) := rfl

/-- Truncation commutes with the external product of edges. -/
@[simp]
lemma toTruncated_tensor {x x' : X _⦋0⦌} (e₁ : Edge x x') {y y' : Y _⦋0⦌}
    (e₂ : Edge y y') :
    (e₁.tensor e₂).toTruncated = e₁.toTruncated.tensor e₂.toTruncated := rfl

end Edge

variable {X Y C W : SSet.{u}}

/-- Transport of `HomotopyCategory.homMk` along endpoint equalities: edges
with the same underlying `1`-simplex have conjugate `homMk` morphisms. -/
private lemma homMk_eq_of_edge_eq {a₁ a₂ b₁ b₂ : W _⦋0⦌}
    {e₁ : Edge a₁ b₁} {e₂ : Edge a₂ b₂}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (h : e₁.edge = e₂.edge) :
    HomotopyCategory.homMk e₁ =
      eqToHom (congrArg HomotopyCategory.mk ha) ≫ HomotopyCategory.homMk e₂ ≫
        eqToHom (congrArg HomotopyCategory.mk hb).symm := by
  subst ha
  subst hb
  rw [Edge.ext h]
  simp

/-- Internal composition on homotopy categories of functor objects: the
functor `h Fun(X, Y) × h Fun(Y, C) ⥤ h Fun(X, C)` obtained from
`MonoidalClosed.comp X Y C` and the binary-product inverse for the
`2`-truncated homotopy category functor. -/
noncomputable def hoComp (X Y C : SSet.{u}) :
    ((ihom X).obj Y).HomotopyCategory × ((ihom Y).obj C).HomotopyCategory ⥤
      ((ihom X).obj C).HomotopyCategory :=
  Truncated.HomotopyCategory.BinaryProduct.inverse _ _ ⋙
    mapHomotopyCategory (MonoidalClosed.comp X Y C)

/-- Internal composition on objects is application of
`MonoidalClosed.comp` to the pair of vertices. -/
@[simp]
lemma hoComp_obj_mk_mk (a : ((ihom X).obj Y) _⦋0⦌) (b : ((ihom Y).obj C) _⦋0⦌) :
    (hoComp X Y C).obj (HomotopyCategory.mk a, HomotopyCategory.mk b) =
      HomotopyCategory.mk ((MonoidalClosed.comp X Y C).app (op ⦋0⦌) (a, b)) := rfl

/-- Internal composition with an identity in the first argument and an
edge in the second is the edge obtained by tensoring with an identity edge
and mapping along `MonoidalClosed.comp`. -/
lemma hoComp_map_mkHom_id_homMk {a : ((ihom X).obj Y) _⦋0⦌}
    {b₀ b₁ : ((ihom Y).obj C) _⦋0⦌} (e : Edge b₀ b₁) :
    (hoComp X Y C).map (Prod.mkHom (𝟙 (HomotopyCategory.mk a))
        (HomotopyCategory.homMk e)) =
      HomotopyCategory.homMk (((Edge.id a).tensor e).map
        (MonoidalClosed.comp X Y C)) := rfl

/-- The vertex of an internal hom picked out by `MonoidalClosed.comp` at a
pair of vertices classified by `f` and `g` is the vertex classified by
`f ≫ g`. This is the vertex form of `MonoidalClosed.curry'_comp`. -/
theorem comp_app_zero_ihomVertexEquiv (f : X ⟶ Y) (g : Y ⟶ C) :
    (MonoidalClosed.comp X Y C).app (op ⦋0⦌)
        (ihomVertexEquiv X Y f, ihomVertexEquiv Y C g) =
      ihomVertexEquiv X C (f ≫ g) := by
  have h : MonoidalClosed.curry' (f ≫ g) =
      (λ_ (𝟙_ SSet.{u})).inv ≫ (MonoidalClosed.curry' f ⊗ₘ MonoidalClosed.curry' g) ≫
        MonoidalClosed.comp X Y C :=
    MonoidalClosed.curry'_comp f g
  have h2 := congrArg (fun φ : 𝟙_ SSet.{u} ⟶ (ihom X).obj C =>
    φ.app (op ⦋0⦌) PUnit.unit) h
  exact h2.symm

/-- `MonoidalClosed.comp` with first vertex fixed at the vertex classified
by `f` agrees on vertices with precomposition by `f`. -/
theorem comp_app_zero_ihomVertexEquiv_pre (f : X ⟶ Y)
    (b : ((ihom Y).obj C) _⦋0⦌) :
    (MonoidalClosed.comp X Y C).app (op ⦋0⦌) (ihomVertexEquiv X Y f, b) =
      ((pre f).app C).app (op ⦋0⦌) b := by
  obtain ⟨g, rfl⟩ := (ihomVertexEquiv Y C).surjective b
  rw [comp_app_zero_ihomVertexEquiv, ihomVertexEquiv_pre_app]

/-- `MonoidalClosed.comp` on a `1`-simplex that is an identity edge in the
first factor agrees with precomposition: the `1`-simplex form of
`MonoidalClosed.curry'_whiskerRight_comp`. -/
theorem comp_app_one_tensor_id_edge (f : X ⟶ Y)
    {b₀ b₁ : ((ihom Y).obj C) _⦋0⦌} (e : Edge b₀ b₁) :
    (MonoidalClosed.comp X Y C).app (op ⦋1⦌)
        ((Edge.id (ihomVertexEquiv X Y f)).edge, e.edge) =
      ((pre f).app C).app (op ⦋1⦌) e.edge := by
  have hθ : (λ_ ((ihom Y).obj C)).inv ≫ (MonoidalClosed.curry' f ▷ ((ihom Y).obj C)) ≫
        MonoidalClosed.comp X Y C = (pre f).app C := by
    rw [MonoidalClosed.curry'_whiskerRight_comp, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [← hθ]
  rfl

/-- The slice of internal composition at a fixed object of `h Fun(X, Y)`:
the functor `h Fun(Y, C) ⥤ h Fun(X, C)` of composition with that object in
the first argument. -/
noncomputable def hoCompSlice {X Y C : SSet.{u}}
    (a : ((ihom X).obj Y).HomotopyCategory) :
    ((ihom Y).obj C).HomotopyCategory ⥤ ((ihom X).obj C).HomotopyCategory :=
  ((Functor.const _).obj a).prod' (𝟭 _) ⋙ hoComp X Y C

/-- The slice of internal composition at a vertex, on objects. -/
lemma hoCompSlice_obj_mk {X Y C : SSet.{u}} (a : ((ihom X).obj Y) _⦋0⦌)
    (b : ((ihom Y).obj C) _⦋0⦌) :
    (hoCompSlice (HomotopyCategory.mk a)).obj (HomotopyCategory.mk b) =
      HomotopyCategory.mk ((MonoidalClosed.comp X Y C).app (op ⦋0⦌) (a, b)) := rfl

/-- The slice of internal composition at a vertex, on generating
morphisms. -/
lemma hoCompSlice_map_homMk {X Y C : SSet.{u}} (a : ((ihom X).obj Y) _⦋0⦌)
    {b₀ b₁ : ((ihom Y).obj C) _⦋0⦌} (e : Edge b₀ b₁) :
    (hoCompSlice (HomotopyCategory.mk a)).map (HomotopyCategory.homMk e) =
      HomotopyCategory.homMk (((Edge.id a).tensor e).map
        (MonoidalClosed.comp X Y C)) := rfl

/-- The slice of internal composition at the vertex classified by
`f : X ⟶ Y` is precomposition with `f` on homotopy categories of functor
objects. -/
theorem hoCompSlice_mk_ihomVertexEquiv_eq_hoPre (f : X ⟶ Y) (C : SSet.{u}) :
    hoCompSlice (HomotopyCategory.mk (ihomVertexEquiv X Y f)) =
      (hoFunctor.map ((pre f).app C)).toFunctor := by
  apply Truncated.HomotopyCategory.functor_ext
    (fun b => congrArg HomotopyCategory.mk (comp_app_zero_ihomVertexEquiv_pre f b))
  intro b₀ b₁ ε
  let e : Edge b₀ b₁ := Edge.ofTruncated (X := (ihom Y).obj C) ε
  have hε : e.toTruncated = ε := rfl
  have hsimp : (((Edge.id (ihomVertexEquiv X Y f)).tensor e).map
        (MonoidalClosed.comp X Y C)).edge = (e.map ((pre f).app C)).edge :=
    comp_app_one_tensor_id_edge f e
  exact homMk_eq_of_edge_eq (comp_app_zero_ihomVertexEquiv_pre f b₀)
    (comp_app_zero_ihomVertexEquiv_pre f b₁) hsimp

/-- Whiskering an isomorphism in `h Fun(X, Y)` through internal composition:
isomorphic first arguments give naturally isomorphic slice functors, with
naturality by functoriality in the product category. -/
noncomputable def hoCompSliceIso {X Y C : SSet.{u}}
    {a₁ a₂ : ((ihom X).obj Y).HomotopyCategory} (α : a₁ ≅ a₂) :
    hoCompSlice (C := C) a₁ ≅ hoCompSlice a₂ :=
  NatIso.ofComponents (fun b => (hoComp X Y C).mapIso (Iso.prod α (Iso.refl b)))
    (fun φ => by
      simp only [hoCompSlice, Functor.comp_obj, Functor.prod'_obj,
        Functor.const_obj_obj, Functor.id_obj, Functor.comp_map, Functor.prod'_map,
        Functor.const_obj_map, Functor.id_map, Functor.mapIso_hom, Iso.prod_hom]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Prod.ext <;> simp)

end SSet

end
