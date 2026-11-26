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
# Asymptotic algebra as an endofunctor

Let 𝒞 be the category of nonunital complex C-star algebras whose carriers lie in Type u, with
nonunital complex star homomorphisms as morphisms. For X∈𝒞 set X∞=C_b([1,∞),X)/C₀([1,∞),X).
The endofunctor α maps X to X∞ and f:X→Y to α(f)([F])=[f∘F]. Constant classes c_X(x)=[t↦x]
give a natural transformation from the identity functor to α, with injective components.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped BoundedContinuousFunction

noncomputable section

universe u

namespace NonUnitalCStarAlgCat

/-- **Asymptotic quotient as a C-star algebra object.**

Let 𝒞 be the category of nonunital complex C-star algebras whose carriers lie in Type u, with
nonunital complex star homomorphisms as morphisms. For X∈𝒞 set X∞=C_b([1,∞),X)/C₀([1,∞),X).
The object asymptoticAlgebraObject X is X∞, with pointwise quotient operations and quotient
norm ‖[F]‖=inf_{h∈C₀}‖F+h‖∞.
-/
abbrev asymptoticAlgebraObject
    (A : NonUnitalCStarAlgCat.{u}) : NonUnitalCStarAlgCat.{u} where
  carrier := AsymptoticAlgebra A
  str := AsymptoticAlgebra.cStarAlgebra A

theorem asymptoticAlgebraObject_carrier
    (A : NonUnitalCStarAlgCat.{u}) :
    (asymptoticAlgebraObject A).carrier = AsymptoticAlgebra A := by
  rfl

/-- **Asymptotic quotient endofunctor.**

Let 𝒞 be the category of nonunital complex C-star algebras whose carriers lie in Type u, with
nonunital complex star homomorphisms as morphisms. For X∈𝒞 set X∞=C_b([1,∞),X)/C₀([1,∞),X).
The functor asymptoticAlgebraFunctor has object map X↦X∞ and morphism map f↦([F]↦[f∘F]); it
preserves identities and composition.
-/
def asymptoticAlgebraFunctor :
    NonUnitalCStarAlgCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj := asymptoticAlgebraObject
  map φ := AsymptoticAlgebra.map φ
  map_id A := AsymptoticAlgebra.map_id A
  map_comp φ ψ := AsymptoticAlgebra.map_comp φ ψ

/-- **Object value of the asymptotic algebra functor.**

Let 𝒞 be the category of nonunital complex C-star algebras whose carriers lie in Type u, with
nonunital complex star homomorphisms as morphisms. For X∈𝒞 set X∞=C_b([1,∞),X)/C₀([1,∞),X).
For X∈𝒞, asymptoticAlgebraFunctor.obj X=asymptoticAlgebraObject X, the quotient
C_b([1,∞),X)/C₀([1,∞),X).
-/
theorem asymptoticAlgebraFunctor_obj
    (A : NonUnitalCStarAlgCat.{u}) :
    asymptoticAlgebraFunctor.obj A = asymptoticAlgebraObject A := by
  rfl

/-- **Morphism value of the asymptotic algebra functor.**

Let 𝒞 be the category of nonunital complex C-star algebras whose carriers lie in Type u, with
nonunital complex star homomorphisms as morphisms. For X∈𝒞 set X∞=C_b([1,∞),X)/C₀([1,∞),X).
For f:X→Y in 𝒞, asymptoticAlgebraFunctor.map f=AsymptoticAlgebra.map f, the map X∞→Y∞ induced
by [F]↦[f∘F].
-/
theorem asymptoticAlgebraFunctor_map
    {A B : NonUnitalCStarAlgCat.{u}} (φ : A ⟶ B) :
    asymptoticAlgebraFunctor.map φ = AsymptoticAlgebra.map φ := by
  rfl

/-- **Functor map on quotient representatives.**

Let 𝒞 be the category of nonunital complex C-star algebras whose carriers lie in Type u, with
nonunital complex star homomorphisms as morphisms. For X∈𝒞 set X∞=C_b([1,∞),X)/C₀([1,∞),X).
For f:X→Y and F∈C_b([1,∞),X), asymptoticAlgebraFunctor.map f (q_X(F))=q_Y(f∘F), where q_X,q_Y
are the quotient maps.
-/
theorem asymptoticAlgebraFunctor_map_quotientMap
    {A B : NonUnitalCStarAlgCat.{u}} (φ : A ⟶ B)
    (f : AsymptoticTime →ᵇ A) :
    asymptoticAlgebraFunctor.map φ
        (AsymptoticAlgebra.quotientMap A f) =
      AsymptoticAlgebra.quotientMap B
        (BoundedContinuousFunction.compNonUnitalStarAlgHom φ f) := by
  exact AsymptoticAlgebra.map_quotientMap φ f

/-- **Natural transformation of constant coefficient classes.**

Let 𝒞 be the category of nonunital complex C-star algebras whose carriers lie in Type u, with
nonunital complex star homomorphisms as morphisms. For X∈𝒞 set X∞=C_b([1,∞),X)/C₀([1,∞),X).
The natural transformation asymptoticAlgebraConstant from the identity functor to
asymptoticAlgebraFunctor has components c_X:X→X∞, c_X(x)=[t↦x], with α(f)∘c_X=c_Y∘f.
-/
@[no_expose]
def asymptoticAlgebraConstant :
    NatTrans (𝟭 NonUnitalCStarAlgCat.{u}) asymptoticAlgebraFunctor where
  app A := AsymptoticAlgebra.constantHom A
  naturality {_A _B} φ :=
    (AsymptoticAlgebra.map_comp_constantHom φ).symm

/-- **Component of the constant-class natural transformation.**

Let 𝒞 be the category of nonunital complex C-star algebras whose carriers lie in Type u, with
nonunital complex star homomorphisms as morphisms. For X∈𝒞 set X∞=C_b([1,∞),X)/C₀([1,∞),X).
For X∈𝒞, asymptoticAlgebraConstant.app X=AsymptoticAlgebra.constantHom X, the star
homomorphism x↦[t↦x] into X∞.
-/
theorem asymptoticAlgebraConstant_app
    (A : NonUnitalCStarAlgCat.{u}) :
    asymptoticAlgebraConstant.app A = AsymptoticAlgebra.constantHom A := by
  rfl

theorem asymptoticAlgebraConstant_app_apply
    (A : NonUnitalCStarAlgCat.{u}) (a : A) :
    asymptoticAlgebraConstant.app A a =
      AsymptoticAlgebra.constantHom A a := by
  rfl

/-- **Injectivity of each constant-class component.**

Let 𝒞 be the category of nonunital complex C-star algebras whose carriers lie in Type u, with
nonunital complex star homomorphisms as morphisms. For X∈𝒞 set X∞=C_b([1,∞),X)/C₀([1,∞),X).
For X∈𝒞, asymptoticAlgebraConstant.app X:X→X∞ is injective; this also holds for the zero
C-star algebra.
-/
theorem asymptoticAlgebraConstant_app_injective
    (A : NonUnitalCStarAlgCat.{u}) :
    Function.Injective (asymptoticAlgebraConstant.app A) := by
  rw [asymptoticAlgebraConstant_app]
  exact AsymptoticAlgebra.constantHom_injective A


end NonUnitalCStarAlgCat
