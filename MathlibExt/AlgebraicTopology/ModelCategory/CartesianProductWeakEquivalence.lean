/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductBrown
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Actual Cartesian products of cofibrant weak maps

The existing tensor Brown theorem applies to the genuine Cartesian
tensor. Its canonical product-functor Iso transfers each fixed-factor
map, and the two original fixed-factor maps compose to the whole chosen
product map. No fibrancy or unit-axiom assumption is needed.
-/

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalCategory

namespace HomotopicalAlgebra.MonoidalPushoutProductAxiom

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [CartesianMonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [HasBinaryProducts C]

/-- The product of the same two weak maps between cofibrant endpoints is
weak for the selected model and its actual Cartesian pushout-product axiom. -/
theorem prodMap_weakEquivalence (hPP : MonoidalPushoutProductAxiom C)
    {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B')
    [IsCofibrant A] [IsCofibrant A'] [IsCofibrant B] [IsCofibrant B']
    [WeakEquivalence f] [WeakEquivalence g] : WeakEquivalence (prod.map f g) := by
  have left_weak (K : C) {X Y : C} (p : X ⟶ Y)
      [IsCofibrant K] [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence p] :
      weakEquivalences C (prod.map (𝟙 K) p) := by
    let e := CartesianMonoidalCategory.tensorLeftIsoProd K
    let _ : WeakEquivalence (K ◁ p) := hPP.whiskerLeft_weakEquivalence_of_cofibrant K p
    let a : Arrow.mk (K ◁ p) ≅ Arrow.mk (prod.map (𝟙 K) p) :=
      Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality p).symm
    exact ((weakEquivalences C).arrow_mk_iso_iff a).mp (mem_weakEquivalences _)
  have hr : weakEquivalences C (prod.map f (𝟙 B)) := by
    have hw := left_weak B f
    have he : prod.map f (𝟙 B) =
        (prod.braiding A B).hom ≫ prod.map (𝟙 B) f ≫ (prod.braiding B A').hom := by
      apply prod.hom_ext <;> simp
    rw [he]
    exact (weakEquivalences C).comp_mem _ _ (mem_weakEquivalences _)
      ((weakEquivalences C).comp_mem _ _ hw (mem_weakEquivalences _))
  have he : prod.map f g = prod.map f (𝟙 B) ≫ prod.map (𝟙 A') g := by simp
  apply (weakEquivalence_iff _).mpr
  rw [he]
  exact (weakEquivalences C).comp_mem _ _ hr (left_weak A' g)

end HomotopicalAlgebra.MonoidalPushoutProductAxiom
