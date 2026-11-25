/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTesting

/-!
# Public use of the homotopy-class testing predicate

The class presheaf uses the original Hom universe and native functor laws.
Testing equivalences give actual representatives of extensions up to
generated homotopy, and injectivity on homotopy classes.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra

universe v u

namespace HomotopyTestingTest

variable {C : Type u} [Category.{v} C] (P : Precylinder (𝟭 C))
variable {X Y Z T : C}

example (X T : C) : (P.homotopyClassFunctor T).obj (op X) =
    P.HomotopyClass X T := rfl

example (α : P.HomotopyClass X T) : P.homotopyClassPrecomp (𝟙 X) T α = α := by
  change P.homotopyQuotientFunctor.map (𝟙 X) ≫ α = α
  rw [P.homotopyQuotientFunctor.map_id, Category.id_comp]

example (f : X ⟶ Y) (g : Y ⟶ Z) (α : P.HomotopyClass Z T) :
    P.homotopyClassPrecomp (f ≫ g) T α =
      P.homotopyClassPrecomp f T (P.homotopyClassPrecomp g T α) := by
  change P.homotopyQuotientFunctor.map (f ≫ g) ≫ α =
    P.homotopyQuotientFunctor.map f ≫ (P.homotopyQuotientFunctor.map g ≫ α)
  rw [P.homotopyQuotientFunctor.map_comp, Category.assoc]

variable (An : MorphismProperty C) [HasTerminal C]

/-- Class surjectivity supplies an actual map with the prescribed generated
homotopy restriction. -/
lemma exists_extension_up_to_homotopy (f : X ⟶ Y) (hf : P.testingEquivalences An f)
    (hT : An.naiveFibrantObjects T) (g : X ⟶ T) :
    ∃ h : Y ⟶ T, P.homotopyRel (f ≫ h) g := by
  obtain ⟨β, hβ⟩ := (hf T hT).surjective (P.homotopyQuotientFunctor.map g)
  obtain ⟨h, hh⟩ := P.homotopyQuotientFunctor.map_surjective β
  refine ⟨h, (P.homotopyQuotientFunctor_map_eq_iff _ _).1 ?_⟩
  rw [← P.homotopyClassPrecomp_map f h, hh]
  exact hβ

/-- Class injectivity cancels precomposition into the specified testing target. -/
lemma classes_eq (f : X ⟶ Y) (hf : P.testingEquivalences An f)
    (hT : An.naiveFibrantObjects T) (α β : P.HomotopyClass Y T)
    (h : P.homotopyClassPrecomp f T α = P.homotopyClassPrecomp f T β) : α = β :=
  (hf T hT).injective h

end HomotopyTestingTest
