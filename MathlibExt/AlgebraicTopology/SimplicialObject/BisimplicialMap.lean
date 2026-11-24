/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.Diagonal

/-!
# Maps in two simplicial directions

A bisimplicial object sends a pair of simplex-category morphisms to a map
between bidegrees.  This file names that map and records its composition,
interchange, diagonal, and naturality laws.  The outer direction is applied
first in the definition; naturality shows that applying the inner direction
first gives the same result.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.Bisimplicial

variable {A : Type u} [Category.{v} A]
  (B : SimplicialObject (SimplicialObject A))

/-- The map of a bisimplicial object induced by one simplex-category map in
each direction. -/
noncomputable def map {p q n m : ℕ}
    (α : ⦋n⦌ ⟶ ⦋p⦌) (β : ⦋m⦌ ⟶ ⦋q⦌) :
    (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
      (B.obj (Opposite.op ⦋n⦌)).obj (Opposite.op ⦋m⦌) :=
  (B.map α.op).app (Opposite.op ⦋q⦌) ≫
    (B.obj (Opposite.op ⦋n⦌)).map β.op

/-- Interchange: the inner simplicial map may be applied before the outer
simplicial map. -/
theorem map_eq_inner_outer {p q n m : ℕ}
    (α : ⦋n⦌ ⟶ ⦋p⦌) (β : ⦋m⦌ ⟶ ⦋q⦌) :
    map B α β =
      (B.obj (Opposite.op ⦋p⦌)).map β.op ≫
        (B.map α.op).app (Opposite.op ⦋m⦌) := by
  exact ((B.map α.op).naturality β.op).symm

/-- Composition of maps in both simplicial directions. -/
theorem map_comp {p q n m n' m' : ℕ}
    (α : ⦋n⦌ ⟶ ⦋p⦌) (β : ⦋m⦌ ⟶ ⦋q⦌)
    (α' : ⦋n'⦌ ⟶ ⦋n⦌) (β' : ⦋m'⦌ ⟶ ⦋m⦌) :
    map B α β ≫ map B α' β' =
      map B (α' ≫ α) (β' ≫ β) := by
  unfold map
  let o := (B.map α.op).app (Opposite.op ⦋q⦌)
  let i := (B.obj (Opposite.op ⦋n⦌)).map β.op
  let o' := (B.map α'.op).app (Opposite.op ⦋m⦌)
  let oq' := (B.map α'.op).app (Opposite.op ⦋q⦌)
  let i' := (B.obj (Opposite.op ⦋n'⦌)).map β'.op
  let ib := (B.obj (Opposite.op ⦋n'⦌)).map β.op
  have hnat := (B.map α'.op).naturality β.op
  change i ≫ o' = oq' ≫ ib at hnat
  change (o ≫ i) ≫ o' ≫ i' = _
  calc
    _ = o ≫ (i ≫ o') ≫ i' := by simp only [Category.assoc]
    _ = o ≫ (oq' ≫ ib) ≫ i' := by rw [hnat]
    _ = (o ≫ oq') ≫ ib ≫ i' := by simp only [Category.assoc]
    _ = _ := by
      dsimp only [o, oq', ib, i']
      rw [← NatTrans.comp_app, ← B.map_comp, ← Functor.map_comp]
      rfl

/-- The map induced by two identity simplex maps is the identity. -/
@[simp]
theorem map_id (p q : ℕ) :
    map B (𝟙 ⦋p⦌) (𝟙 ⦋q⦌) =
      𝟙 ((B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌)) := by
  simp [map]

/-- A face in the outer direction and the identity in the inner direction. -/
theorem map_delta_id (p q : ℕ) (i : Fin (p + 2)) :
    map B (SimplexCategory.δ i) (𝟙 ⦋q⦌) =
      (B.δ i).app (Opposite.op ⦋q⦌) := by
  simp [map, SimplicialObject.δ]

/-- The identity in the outer direction and a face in the inner direction. -/
theorem map_id_delta (p q : ℕ) (i : Fin (q + 2)) :
    map B (𝟙 ⦋p⦌) (SimplexCategory.δ i) =
      (B.obj (Opposite.op ⦋p⦌)).δ i := by
  simp [map, SimplicialObject.δ]

/-- Equality transports in the two simplex degrees induce the corresponding
transport between bidegree objects. -/
theorem map_eqToHom {p q n m : ℕ} (hp : n = p) (hq : m = q) :
    map B (eqToHom (by rw [hp])) (eqToHom (by rw [hq])) =
      (eqToHom (by rw [hp, hq]) :
        (B.obj (Opposite.op ⦋p⦌)).obj (Opposite.op ⦋q⦌) ⟶
          (B.obj (Opposite.op ⦋n⦌)).obj (Opposite.op ⦋m⦌)) := by
  subst p
  subst q
  simp

/-- Applying the same simplex map in both directions is the map of the
diagonal simplicial object. -/
theorem map_diagonal {p n : ℕ} (α : ⦋n⦌ ⟶ ⦋p⦌) :
    map B α α = ((SimplicialObject.diagonalFunctor A).obj B).map α.op := by
  rw [map_eq_inner_outer]
  rfl

/-- Naturality of the bidegree map under a morphism of bisimplicial objects. -/
theorem map_naturality
    {B B' : SimplicialObject (SimplicialObject A)} (f : B ⟶ B')
    {p q n m : ℕ} (α : ⦋n⦌ ⟶ ⦋p⦌) (β : ⦋m⦌ ⟶ ⦋q⦌) :
    map B α β ≫
        (f.app (Opposite.op ⦋n⦌)).app (Opposite.op ⦋m⦌) =
      (f.app (Opposite.op ⦋p⦌)).app (Opposite.op ⦋q⦌) ≫
        map B' α β := by
  unfold map
  have hinner := (f.app (Opposite.op ⦋n⦌)).naturality β.op
  have houter := congrArg (fun k => k.app (Opposite.op ⦋q⦌))
    (f.naturality α.op)
  calc
    _ = (B.map α.op).app (Opposite.op ⦋q⦌) ≫
        (f.app (Opposite.op ⦋n⦌)).app (Opposite.op ⦋q⦌) ≫
          (B'.obj (Opposite.op ⦋n⦌)).map β.op := by
      simpa only [Category.assoc] using
        (B.map α.op).app (Opposite.op ⦋q⦌) ≫= hinner
    _ = _ := by
      simpa only [NatTrans.comp_app, Category.assoc] using
        houter =≫ (B'.obj (Opposite.op ⦋n⦌)).map β.op

end AlgebraicTopology.Bisimplicial
