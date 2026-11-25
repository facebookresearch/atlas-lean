/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CylinderHomotopyCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrations
public import Mathlib.CategoryTheory.Yoneda

/-!
# Weak equivalences defined by chosen-cylinder homotopy classes

The presheaf of homotopy classes into a fixed object is the native Yoneda
presheaf on the chosen-cylinder quotient, restricted along the quotient
functor. Its action is actual precomposition on homotopy classes.

The testing class consists of maps inducing a bijection on these classes
into every naive fibrant object for the specified anodyne class. This is
Cisinski's Definition 2.4.18 (July 30, 2026 version). The primitive uses a
functorial precylinder and an explicit morphism class in any category
with a terminal object; the exact presheaf/anodyne system is its source
application.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C))

/-- The presheaf of homotopy classes into `T`, in the original Hom universe. -/
abbrev homotopyClassFunctor (T : C) : Cᵒᵖ ⥤ Type v :=
  P.homotopyQuotientFunctor.op ⋙ yoneda.obj (P.homotopyQuotientFunctor.obj T)

/-- Precomposition by the class of the actual specified map. -/
abbrev homotopyClassPrecomp {X Y : C} (f : X ⟶ Y) (T : C) :
    P.HomotopyClass Y T → P.HomotopyClass X T :=
  (P.homotopyClassFunctor T).map f.op

/-- On a representative, class precomposition is ordinary precomposition. -/
lemma homotopyClassPrecomp_map {X Y T : C} (f : X ⟶ Y) (g : Y ⟶ T) :
    P.homotopyClassPrecomp f T (P.homotopyQuotientFunctor.map g) =
      P.homotopyQuotientFunctor.map (f ≫ g) := by
  change P.homotopyQuotientFunctor.map f ≫ P.homotopyQuotientFunctor.map g = _
  exact (P.homotopyQuotientFunctor.map_comp f g).symm

variable (An : MorphismProperty C) [HasTerminal C]

/-- Homotopy-class testing against every naive fibrant object for `An`. -/
def testingEquivalences : MorphismProperty C :=
  fun _ _ f ↦ ∀ T : C, An.naiveFibrantObjects T →
    Function.Bijective (P.homotopyClassPrecomp f T)

lemma testingEquivalences_iff {X Y : C} (f : X ⟶ Y) :
    P.testingEquivalences An f ↔
      ∀ T : C, An.naiveFibrantObjects T →
        Function.Bijective (P.homotopyClassPrecomp f T) :=
  Iff.rfl

end HomotopicalAlgebra.Precylinder
