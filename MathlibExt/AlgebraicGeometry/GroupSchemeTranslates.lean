/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Translates of open subsets of a group scheme over a field

* `CategoryTheory.GrpObj.shearIso`: for a morphism `a : T ⟶ G` to a group object of a cartesian
  monoidal category, the automorphism `(t, g) ↦ (t, a(t) * g)` of `T ⊗ G`.
* `AlgebraicGeometry.isOpen_range_mul_of_grpObj`: for a group scheme `G` over a field `k`, an open
  subscheme `U` of `G` and a morphism `a : T ⟶ G`, the image of
  `T ×_k U ⟶ G ×_k G ⟶ G`, `(t, u) ↦ a(t) * u`, is open in `G` (Stacks project, Groupoid Schemes,
  Lemma 39.7.2, Tag 0B7N).

The proof: the shearing map `(t, g) ↦ (t, a(t) * g)` is an automorphism of `T ×_k G` over `T`,
which carries the open `T ×_k U` onto an open set whose image under the second projection
`T ×_k G ⟶ G` is the image in question; that projection is open, being a base change of the
universally open structure morphism `T ⟶ Spec k`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace CategoryTheory

/-- The shearing automorphism `(t, g) ↦ (t, a(t) * g)` of `T ⊗ G`, for a morphism `a : T ⟶ G` to
a group object `G` of a cartesian monoidal category; its inverse is `(t, g) ↦ (t, a(t)⁻¹ * g)`. -/
@[simps]
def GrpObj.shearIso {C : Type*} [Category C] [CartesianMonoidalCategory C] {T G : C} [GrpObj G]
    (a : T ⟶ G) : T ⊗ G ≅ T ⊗ G where
  hom := lift (fst _ _) (lift (fst _ _ ≫ a) (snd _ _) ≫ μ)
  inv := lift (fst _ _) (lift (fst _ _ ≫ a ≫ ι) (snd _ _) ≫ μ)
  hom_inv_id := by
    refine hom_ext _ _ (by simp) ?_
    · rw [Category.assoc, lift_snd, Category.id_comp, comp_lift_assoc, ← Hom.mul_def]
      simp only [lift_fst_assoc, lift_snd]
      rw [← Category.assoc, ← Hom.inv_def, ← Hom.mul_def, inv_mul_cancel_left]
  inv_hom_id := by
    refine hom_ext _ _ (by simp) ?_
    · rw [Category.assoc, lift_snd, Category.id_comp, comp_lift_assoc, ← Hom.mul_def]
      simp only [lift_fst_assoc, lift_snd]
      rw [← Hom.mul_def, ← Category.assoc, ← Hom.inv_def, mul_inv_cancel_left]

end CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)]

/-- **Translates of open subsets of a group scheme.** Let `G` be a group scheme over a field `k`
(`f : G ⟶ Spec k` with a group object structure on `Over.mk f`), let `U` be an open subscheme of
`G` and let `a : T ⟶ G` be a morphism of schemes, making `T` a `k`-scheme. Then the image of the
composition `T ×_k U ⟶ G ×_k G ⟶ G` of `a × (U ⊆ G)` with the multiplication is open in `G`.

This is the Stacks project, Groupoid Schemes, Lemma 39.7.2 (Tag 0B7N): "Let `k` be a field. Let
`G` be a group scheme over `k`. Let `U ⊂ G` open and `T → G` a morphism of schemes. Then the image
of the composition `T ×_k U → G ×_k G → G` is open." -/
theorem isOpen_range_mul_of_grpObj {T : Scheme.{u}} (a : T ⟶ G) (U : G.Opens) :
    IsOpen (Set.range (((Over.homMk a rfl : Over.mk (a ≫ f) ⟶ Over.mk f) ⊗ₘ
      (Over.homMk U.ι rfl : Over.mk (U.ι ≫ f) ⟶ Over.mk f)) ≫ μ).left) := by
  set A : Over.mk (a ≫ f) ⟶ Over.mk f := Over.homMk a rfl
  set ιU : Over.mk (U.ι ≫ f) ⟶ Over.mk f := Over.homMk U.ι rfl
  have key : (A ⊗ₘ ιU) ≫ μ = (Over.mk (a ≫ f) ◁ ιU) ≫ (GrpObj.shearIso A).hom ≫ snd _ _ := by
    rw [← lift_fst_comp_snd_comp, GrpObj.shearIso_hom, lift_snd, comp_lift_assoc,
      whiskerLeft_fst_assoc, whiskerLeft_snd]
  have hr {P Q R W : Scheme.{u}} (x : P ⟶ Q) (y : Q ⟶ R) (z : R ⟶ W) :
      Set.range (x ≫ y ≫ z) = z '' (y '' Set.range x) := by
    ext w
    simp
  have h1 : Set.range ⇑(𝟙 (Over.mk (a ≫ f)).left) = Set.univ :=
    Set.range_eq_univ.2 fun x ↦ ⟨x, by simp⟩
  rw [key, Over.comp_left, Over.comp_left, hr, Over.whiskerLeft_left, Scheme.Pullback.range_map,
    h1, Set.preimage_univ, Set.univ_inter]
  simp only [ιU, Over.homMk_left]
  rw [Over.snd_left]
  have h2 : IsOpenMap (pullback.snd (Over.mk (a ≫ f)).hom (Over.mk f).hom) :=
    Scheme.Hom.isOpenMap _
  exact h2 _ ((GrpObj.shearIso A).hom.left.isOpenEmbedding.isOpenMap _
    (U.ι.isOpenEmbedding.isOpen_range.preimage (Scheme.Hom.continuous _)))

end AlgebraicGeometry
