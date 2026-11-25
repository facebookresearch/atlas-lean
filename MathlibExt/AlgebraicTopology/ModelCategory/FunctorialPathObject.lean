/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.ModelCategory.PathObject
import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Path objects from the supplied native functorial factorization

The diagonal arrow, middle functor, unit and joint endpoint map retain the
actual given factorization data. Its functoriality supplies every original
endpoint square; the resulting path object is very good without an added
path or lifting outcome assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.FunctorialPathObject

variable {C : Type u} [Category.{v} C]

section Categorical

variable [HasBinaryProducts C]

/-- The actual binary-square functor, retaining both copies of every map. -/
def square : C ⥤ C where
  obj X := X ⨯ X
  map f := prod.map f f
  map_id _X := prod.map_id_id
  map_comp _f _g := by apply prod.hom_ext <;> simp

/-- The original natural diagonal. -/
def diagonal : 𝟭 C ⟶ square where
  app X := prod.lift (𝟙 X) (𝟙 X)
  naturality _X _Y _f := by apply prod.hom_ext <;> simp [square]

/-- Diagonal arrows and their complete original commutative squares. -/
def diagonalArrow : C ⥤ Arrow C where
  obj X := Arrow.mk (diagonal.app X)
  map f := Arrow.homMk f (square.map f) (diagonal.naturality f)
  map_id _X := by apply Arrow.hom_ext <;> simp
  map_comp _f _g := by apply Arrow.hom_ext <;> simp

end Categorical

variable [ModelCategory C]
  (data : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The path functor is the actual supplied middle functor on the diagonal. -/
def pathFunctor : C ⥤ C := diagonalArrow ⋙ data.Z

/-- The actual first factor, with its complete source naturality. -/
def unit : 𝟭 C ⟶ pathFunctor data := Functor.whiskerLeft diagonalArrow data.i

/-- The actual second factor, with both original endpoints. -/
def endpoints : pathFunctor data ⟶ square := Functor.whiskerLeft diagonalArrow data.p

/-- The original first endpoint. -/
def first : pathFunctor data ⟶ 𝟭 C where
  app X := (endpoints data).app X ≫ prod.fst
  naturality X Y f := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ (prod.fst : Y ⨯ Y ⟶ Y))
        ((endpoints data).naturality f)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun g => (endpoints data).app X ≫ g) (prod.map_fst f f)).trans
            (Category.assoc _ _ _).symm)))

/-- The original second endpoint. -/
def second : pathFunctor data ⟶ 𝟭 C where
  app X := (endpoints data).app X ≫ prod.snd
  naturality X Y f := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ (prod.snd : Y ⨯ Y ⟶ Y))
        ((endpoints data).naturality f)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun g => (endpoints data).app X ≫ g) (prod.map_snd f f)).trans
            (Category.assoc _ _ _).symm)))

/-- Both supplied factors compose to the same original diagonal. -/
theorem fac (X : C) : (unit data).app X ≫ (endpoints data).app X = diagonal.app X :=
  data.fac_app

@[reassoc (attr := simp)]
theorem unit_first (X : C) : (unit data).app X ≫ (first data).app X = 𝟙 X := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (prod.fst : X ⨯ X ⟶ X)) (fac data X)).trans
      (prod.lift_fst _ _))

@[reassoc (attr := simp)]
theorem unit_second (X : C) : (unit data).app X ≫ (second data).app X = 𝟙 X := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (prod.snd : X ⨯ X ⟶ X)) (fac data X)).trans
      (prod.lift_snd _ _))

/-- The actual native factorization constructs the very good path object. -/
abbrev pathObject (X : C) : PathObject X :=
  PathObject.ofFactorizationData (data.factorizationData (diag X))

@[simp]
theorem pathObject_P (X : C) : (pathObject data X).P = (pathFunctor data).obj X := rfl

@[simp]
theorem pathObject_unit (X : C) : (pathObject data X).ι = (unit data).app X := rfl

@[simp]
theorem pathObject_first (X : C) : (pathObject data X).p₀ = (first data).app X := rfl

@[simp]
theorem pathObject_second (X : C) : (pathObject data X).p₁ = (second data).app X := rfl

/-- Very-goodness follows from the native trivial-cofibration/fibration factors. -/
instance pathObject_isVeryGood (X : C) : (pathObject data X).IsVeryGood := inferInstance

end HomotopicalAlgebra.FunctorialPathObject
