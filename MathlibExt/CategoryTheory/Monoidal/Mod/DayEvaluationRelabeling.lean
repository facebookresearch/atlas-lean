/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluation
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Relabeling free Day modules along index morphisms

The generic evaluation family of Day modules is functorial in its index.  By
taking inverse mates of those evaluation maps, this file packages the
free-at-object functors as a functor on the opposite index category.  Its two
characteristic theorems are the corresponding unit and counit mate equations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vI uI vV uV

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
variable [MonoidalCategory (DayFunctor I V)]
variable (A : DayFunctor I V) [MonObj A]
variable [∀ i j : I, HasCoproductsOfShape (i ⟶ j) V]

/-- Free Day modules at varying objects form a functor contravariant in the
index. Its maps are inverse mates of the generic evaluation relabeling maps. -/
noncomputable def dayFreeAtFunctor :
    Iᵒᵖ ⥤ (V ⥤ CategoryTheory.Mod (DayFunctor I V) A) :=
  let K : CategoryTheory.Mod (DayFunctor I V) A ⥤ I ⥤ V :=
    CategoryTheory.Mod.forget A ⋙ (DayFunctor.equiv I V).symm.inverse
  { obj := fun X ↦ dayFreeAt A X.unop
    map := fun {X Y} g ↦
      (conjugateEquiv
        (dayFreeAtEvaluationAdjunction A Y.unop)
        (dayFreeAtEvaluationAdjunction A X.unop)).symm
          (K.flip.map g.unop)
    map_id := fun X ↦ by
      rw [unop_id, Functor.map_id]
      change
        (conjugateEquiv
          (dayFreeAtEvaluationAdjunction A X.unop)
          (dayFreeAtEvaluationAdjunction A X.unop)).symm
            (𝟙 (dayEvaluation A X.unop)) = 𝟙 (dayFreeAt A X.unop)
      exact conjugateEquiv_symm_id
        (dayFreeAtEvaluationAdjunction A X.unop)
    map_comp := fun {X Y Z} f g ↦ by
      rw [unop_comp, Functor.map_comp]
      exact (conjugateEquiv_symm_comp
        (dayFreeAtEvaluationAdjunction A Z.unop)
        (dayFreeAtEvaluationAdjunction A Y.unop)
        (dayFreeAtEvaluationAdjunction A X.unop)
        (K.flip.map g.unop) (K.flip.map f.unop)).symm }

/-- The map of `dayFreeAtFunctor` is the inverse mate of evaluation
relabeling, expressed by the unit equation on underlying Day functors. -/
theorem dayFreeAtFunctor_map_unit {i j : I} (g : i ⟶ j) (X : V) :
    (dayFreeAtEvaluationAdjunction A i).unit.app X ≫
        ((dayFreeAt A i).obj X).X.functor.map g =
      (dayFreeAtEvaluationAdjunction A j).unit.app X ≫
        (dayEvaluation A j).map (((dayFreeAtFunctor A).map g.op).app X) := by
  let K : CategoryTheory.Mod (DayFunctor I V) A ⥤ I ⥤ V :=
    CategoryTheory.Mod.forget A ⋙ (DayFunctor.equiv I V).symm.inverse
  change
    (dayFreeAtEvaluationAdjunction A i).unit.app X ≫
        (K.flip.map g).app ((dayFreeAt A i).obj X) =
      (dayFreeAtEvaluationAdjunction A j).unit.app X ≫
        (dayEvaluation A j).map
          (((conjugateEquiv
            (dayFreeAtEvaluationAdjunction A i)
            (dayFreeAtEvaluationAdjunction A j)).symm
              (K.flip.map g)).app X)
  exact unit_conjugateEquiv_symm
    (dayFreeAtEvaluationAdjunction A i)
    (dayFreeAtEvaluationAdjunction A j) (K.flip.map g) X

/-- The map of `dayFreeAtFunctor` is the inverse mate of evaluation
relabeling, expressed by the counit equation on Day modules. -/
theorem dayFreeAtFunctor_map_counit {i j : I} (g : i ⟶ j)
    (M : CategoryTheory.Mod (DayFunctor I V) A) :
    (dayFreeAt A j).map (M.X.functor.map g) ≫
        (dayFreeAtEvaluationAdjunction A j).counit.app M =
      ((dayFreeAtFunctor A).map g.op).app ((dayEvaluation A i).obj M) ≫
        (dayFreeAtEvaluationAdjunction A i).counit.app M := by
  let K : CategoryTheory.Mod (DayFunctor I V) A ⥤ I ⥤ V :=
    CategoryTheory.Mod.forget A ⋙ (DayFunctor.equiv I V).symm.inverse
  change
    (dayFreeAt A j).map ((K.flip.map g).app M) ≫
        (dayFreeAtEvaluationAdjunction A j).counit.app M =
      ((conjugateEquiv
        (dayFreeAtEvaluationAdjunction A i)
        (dayFreeAtEvaluationAdjunction A j)).symm
          (K.flip.map g)).app ((dayEvaluation A i).obj M) ≫
        (dayFreeAtEvaluationAdjunction A i).counit.app M
  exact conjugateEquiv_counit_symm
    (dayFreeAtEvaluationAdjunction A i)
    (dayFreeAtEvaluationAdjunction A j) (K.flip.map g) M

end CategoryTheory.Mod
