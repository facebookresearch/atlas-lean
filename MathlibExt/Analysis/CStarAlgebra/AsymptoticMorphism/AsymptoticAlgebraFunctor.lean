/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.AsymptoticAlgebraMap
public import MathlibExt.Analysis.CStarAlgebra.Category.Basic
public import Mathlib.CategoryTheory.NatTrans

/-!
# The same-universe asymptotic-algebra functor

`asymptoticAlgebraObject` is the deliberately lightweight reducible carrier
view needed by finite iteration.  It stores the existing quotient C-star
dictionary and no proof-heavy map. The functor is a lightweight transparent
wrapper so its object carriers compute to the literal quotient; its maps
delegate to the opaque, independent-universe primary map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped BoundedContinuousFunction

noncomputable section

universe u

namespace NonUnitalCStarAlgCat

/-- The actual asymptotic quotient as an object of the existing category.
This abbreviation is intentionally reducible: its carrier and stored
dictionary are the computational interface used by finite iteration. -/
abbrev asymptoticAlgebraObject
    (A : NonUnitalCStarAlgCat.{u}) : NonUnitalCStarAlgCat.{u} where
  carrier := AsymptoticAlgebra A
  str := AsymptoticAlgebra.cStarAlgebra A

theorem asymptoticAlgebraObject_carrier
    (A : NonUnitalCStarAlgCat.{u}) :
    (asymptoticAlgebraObject A).carrier = AsymptoticAlgebra A := by
  rfl

/-- The actual asymptotic quotient as an endofunctor of the existing category.
The direct `AsymptoticAlgebra.map` remains the universe-polymorphic primary API. -/
def asymptoticAlgebraFunctor :
    NonUnitalCStarAlgCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj := asymptoticAlgebraObject
  map φ := AsymptoticAlgebra.map φ
  map_id A := AsymptoticAlgebra.map_id A
  map_comp φ ψ := AsymptoticAlgebra.map_comp φ ψ

/-- The functor object is the lightweight literal quotient object. -/
theorem asymptoticAlgebraFunctor_obj
    (A : NonUnitalCStarAlgCat.{u}) :
    asymptoticAlgebraFunctor.obj A = asymptoticAlgebraObject A := by
  rfl

/-- The functor map is the direct coefficient map. -/
theorem asymptoticAlgebraFunctor_map
    {A B : NonUnitalCStarAlgCat.{u}} (φ : A ⟶ B) :
    asymptoticAlgebraFunctor.map φ = AsymptoticAlgebra.map φ := by
  rfl

/-- The functor map has the literal postcomposition formula on quotient
representatives. -/
theorem asymptoticAlgebraFunctor_map_quotientMap
    {A B : NonUnitalCStarAlgCat.{u}} (φ : A ⟶ B)
    (f : AsymptoticTime →ᵇ A) :
    asymptoticAlgebraFunctor.map φ
        (AsymptoticAlgebra.quotientMap A f) =
      AsymptoticAlgebra.quotientMap B
        (BoundedContinuousFunction.compNonUnitalStarAlgHom φ f) := by
  exact AsymptoticAlgebra.map_quotientMap φ f

/-- The constant-class inclusions form a natural transformation from the
identity functor to the asymptotic-algebra functor. -/
@[no_expose]
def asymptoticAlgebraConstant :
    NatTrans (𝟭 NonUnitalCStarAlgCat.{u}) asymptoticAlgebraFunctor where
  app A := AsymptoticAlgebra.constantHom A
  naturality {_A _B} φ :=
    (AsymptoticAlgebra.map_comp_constantHom φ).symm

/-- The natural-transformation component is the actual constant-class map. -/
theorem asymptoticAlgebraConstant_app
    (A : NonUnitalCStarAlgCat.{u}) :
    asymptoticAlgebraConstant.app A = AsymptoticAlgebra.constantHom A := by
  rfl

theorem asymptoticAlgebraConstant_app_apply
    (A : NonUnitalCStarAlgCat.{u}) (a : A) :
    asymptoticAlgebraConstant.app A a =
      AsymptoticAlgebra.constantHom A a := by
  rfl

/-- Every component of the constant-class transformation is injective,
including on the zero algebra. -/
theorem asymptoticAlgebraConstant_app_injective
    (A : NonUnitalCStarAlgCat.{u}) :
    Function.Injective (asymptoticAlgebraConstant.app A) := by
  rw [asymptoticAlgebraConstant_app]
  exact AsymptoticAlgebra.constantHom_injective A

#print axioms asymptoticAlgebraObject
#print axioms asymptoticAlgebraFunctor
#print axioms asymptoticAlgebraFunctor_map
#print axioms asymptoticAlgebraConstant
#print axioms asymptoticAlgebraConstant_app
#print axioms asymptoticAlgebraConstant_app_injective

end NonUnitalCStarAlgCat
