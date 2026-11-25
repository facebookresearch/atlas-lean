/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat

/-!
# Zero-simplices of simplicial internal hom

The `0`-simplices of `(ihom A).obj X` are the simplicial maps `A ⟶ X`.
We build `ihom₀Equiv` from `yonedaEquiv`, currying and `rightUnitor`, and record
the precomposition `pre` and postcomposition `map` formulas needed for the
pullback target and fiber-membership packets.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial SSet
open scoped Simplicial

namespace SSet

variable {A B X Y : SSet.{u}}

/-- Zero-simplex equivalence for simplicial internal hom.

Forward: `s ↦ rightUnitor.inv ≫ uncurry (yonedaEquiv.symm s)`.
Backward: `f ↦ yonedaEquiv (curry (rightUnitor.hom ≫ f))`. -/
noncomputable def ihom₀Equiv (A X : SSet.{u}) :
    ((ihom A).obj X) _⦋0⦌ ≃ (A ⟶ X) where
  toFun s := (stdSimplex.rightUnitor A).inv ≫ uncurry (yonedaEquiv.symm s)
  invFun f := yonedaEquiv (curry ((stdSimplex.rightUnitor A).hom ≫ f))
  left_inv s := by
    calc yonedaEquiv (curry ((stdSimplex.rightUnitor A).hom ≫
          (stdSimplex.rightUnitor A).inv ≫ uncurry (yonedaEquiv.symm s)))
        = yonedaEquiv (curry (uncurry (yonedaEquiv.symm s))) := by
          rw [Iso.hom_inv_id_assoc]
      _ = yonedaEquiv (yonedaEquiv.symm s) := by rw [curry_uncurry]
      _ = s := by rw [Equiv.apply_symm_apply]
  right_inv f := by
    calc (stdSimplex.rightUnitor A).inv ≫
            uncurry (yonedaEquiv.symm
              (yonedaEquiv (curry ((stdSimplex.rightUnitor A).hom ≫ f))))
        = (stdSimplex.rightUnitor A).inv ≫
            uncurry (curry ((stdSimplex.rightUnitor A).hom ≫ f)) := by
              rw [Equiv.symm_apply_apply]
      _ = (stdSimplex.rightUnitor A).inv ≫
            ((stdSimplex.rightUnitor A).hom ≫ f) := by rw [uncurry_curry]
      _ = f := by rw [Iso.inv_hom_id_assoc]

@[simp] theorem ihom₀Equiv_apply (s : ((ihom A).obj X) _⦋0⦌) :
    ihom₀Equiv A X s =
      (stdSimplex.rightUnitor A).inv ≫ uncurry (yonedaEquiv.symm s) := rfl

@[simp] theorem ihom₀Equiv_symm_apply (f : A ⟶ X) :
    (ihom₀Equiv A X).symm f =
      yonedaEquiv (curry ((stdSimplex.rightUnitor A).hom ≫ f)) := rfl

@[simp] theorem ihom₀Equiv_apply_symm_apply (f : A ⟶ X) :
    ihom₀Equiv A X ((ihom₀Equiv A X).symm f) = f :=
  Equiv.apply_symm_apply _ _

@[simp] theorem ihom₀Equiv_symm_apply_apply (s : ((ihom A).obj X) _⦋0⦌) :
    (ihom₀Equiv A X).symm (ihom₀Equiv A X s) = s :=
  Equiv.symm_apply_apply _ _

theorem ihom₀Equiv_symm_pre {B A X : SSet.{u}} (f : B ⟶ A) (g : A ⟶ X) :
    (ihom₀Equiv B X).symm (f ≫ g) =
      ((pre f).app X).app _ ((ihom₀Equiv A X).symm g) := by
  calc (ihom₀Equiv B X).symm (f ≫ g) =
        yonedaEquiv (curry ((stdSimplex.rightUnitor B).hom ≫ f ≫ g)) := rfl
    _ = yonedaEquiv (curry
          (f ▷ (Δ[0] : SSet.{u}) ≫ (stdSimplex.rightUnitor A).hom ≫ g)) := by
            rw [stdSimplex.rightUnitor_hom_naturality_assoc]
    _ = yonedaEquiv (curry
          ((stdSimplex.rightUnitor A).hom ≫ g) ≫ (pre f).app X) := by
              rw [← curry_pre_app]
    _ = ((pre f).app X).app _ (yonedaEquiv (curry
          ((stdSimplex.rightUnitor A).hom ≫ g))) := by rw [yonedaEquiv_comp]
    _ = _ := rfl

theorem ihom₀Equiv_symm_map {A X Y : SSet.{u}} (f : A ⟶ X) (g : X ⟶ Y) :
    (ihom₀Equiv A Y).symm (f ≫ g) =
      ((ihom A).map g).app _ ((ihom₀Equiv A X).symm f) := by
  calc (ihom₀Equiv A Y).symm (f ≫ g) =
        yonedaEquiv (curry ((stdSimplex.rightUnitor A).hom ≫ f ≫ g)) := rfl
    _ = yonedaEquiv (curry
          (((stdSimplex.rightUnitor A).hom ≫ f) ≫ g)) := by rw [Category.assoc]
    _ = yonedaEquiv (curry
          ((stdSimplex.rightUnitor A).hom ≫ f) ≫ (ihom A).map g) := by
              rw [curry_natural_right]
    _ = ((ihom A).map g).app _ (yonedaEquiv (curry
          ((stdSimplex.rightUnitor A).hom ≫ f))) := by rw [yonedaEquiv_comp]
    _ = _ := rfl

end SSet
