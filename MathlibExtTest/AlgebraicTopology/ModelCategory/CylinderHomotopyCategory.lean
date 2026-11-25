/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import MathlibExt.AlgebraicTopology.ModelCategory.CylinderHomotopyCategory

/-!
# Cylinder Homotopy Category
-/

open CategoryTheory

universe v u v' u'

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C))
variable {A X Y Z W : C}

-- Both compositions descend for generated homotopies, without a single
-- elementary witness or a fibrancy assumption.
example (a : A ⟶ X) (p : Y ⟶ Z) {f g : X ⟶ Y} (h : P.homotopyRel f g) :
    P.homotopyQuotientFunctor.map (a ≫ f ≫ p) =
      P.homotopyQuotientFunctor.map (a ≫ g ≫ p) := by
  apply (P.homotopyQuotientFunctor_map_eq_iff _ _).2
  simpa only [Category.assoc] using HomRel.comp_right p (HomRel.comp_left a h)

-- Reversal is a generated homotopy; no reversal of the chosen cylinder
-- or an elementary homotopy with reversed endpoints is assumed.
example {f g : X ⟶ Y} (H : (P.app X).LeftHomotopy f g) :
    P.homotopyRel g f :=
  (P.homotopyQuotientFunctor_map_eq_iff _ _).1
    (P.homotopyQuotientFunctor_map_eq H).symm

example {f g h : X ⟶ Y} (H₀ : (P.app X).LeftHomotopy g f)
    (H₁ : (P.app X).LeftHomotopy g h) : P.homotopyRel f h :=
  (P.homotopyQuotientFunctor_map_eq_iff _ _).1
    ((P.homotopyQuotientFunctor_map_eq H₀).symm.trans
      (P.homotopyQuotientFunctor_map_eq H₁))

-- These are the native functor laws in the quotient category.
example (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.homotopyQuotientFunctor.map (f ≫ g) =
      P.homotopyQuotientFunctor.map f ≫ P.homotopyQuotientFunctor.map g :=
  P.homotopyQuotientFunctor.map_comp f g

example (X : C) : P.homotopyQuotientFunctor.map (𝟙 X) =
    𝟙 (P.homotopyQuotientFunctor.obj X) :=
  P.homotopyQuotientFunctor.map_id X

-- Every class has an actual map representative, in the original hom universe.
example (α : P.HomotopyClass X Y) :
    ∃ f : X ⟶ Y, P.homotopyQuotientFunctor.map f = α :=
  P.homotopyQuotientFunctor.map_surjective α

example (e : X ≅ Y) : P.homotopyEquivalences e.hom := by
  rw [P.homotopyEquivalences_iff]
  infer_instance

-- A functor that identifies the specified elementary homotopies descends
-- through this quotient, for target categories of independent universes.
example {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (h : ∀ {X Y : C} (f g : X ⟶ Y),
      (P.app X).LeftHomotopy f g → F.map f = F.map g) :
    ∃ G : P.HomotopyQuotient ⥤ D, P.homotopyQuotientFunctor ⋙ G = F := by
  let H : ∀ (X Y : C) (f g : X ⟶ Y),
      P.elementaryHomotopyRel f g → F.map f = F.map g :=
    fun _ _ f g e ↦ e.elim (h f g)
  exact ⟨CategoryTheory.Quotient.lift P.elementaryHomotopyRel F H,
    CategoryTheory.Quotient.lift_spec P.elementaryHomotopyRel F H⟩

end HomotopicalAlgebra.Precylinder
