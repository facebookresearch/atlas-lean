/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingComplex
import MathlibExt.AlgebraicTopology.SimplicialSet.LeftIhomPrism
import Mathlib.CategoryTheory.Types.Basic

/-!
# The original underlying marked mapping simplices

Forgetting a marked parameter-product map retains its entire original
simplicial map. These maps form the usual left-parameter mapping complex,
canonically isomorphic to the already existing simplicial internal Hom.
The forgetful map is degreewise injective for either parameter marking.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The unmarked mapping complex on the same original left-parameter prisms. -/
def parameterMapping (X Y : SSet.{u}) : SSet.{u} :=
  (SSet.stdSimplex ⋙ tensorRight X).op ⋙ CategoryTheory.yoneda.obj Y

/-- Each original left-parameter mapping simplex is its whole simplicial prism. -/
def parameterMappingSimplexEquiv (X Y : SSet.{u}) (n : ℕ) :
    (parameterMapping X Y) _⦋n⦌ ≃ ((Δ[n] : SSet.{u}) ⊗ X ⟶ Y) := Equiv.refl _

/-- The usual internal Hom is this same mapping complex through the native prism dictionary. -/
def parameterMappingIsoIhom (X Y : SSet.{u}) : parameterMapping X Y ≅ (ihom X).obj Y :=
  NatIso.ofComponents (fun n => (leftIhomSimplexEquiv X Y n.unop.len).toIso) (by
    intro n m a
    apply ConcreteCategory.hom_ext
    intro f
    change leftIhomSimplexOfPrism ((SSet.stdSimplex.map a.unop ▷ X) ≫ f) =
      ((ihom X).obj Y).map a (leftIhomSimplexOfPrism f)
    exact (leftIhomSimplexOfPrism_map a.unop f).symm)

/-- The original complete prism is the image of a marked mapping simplex after forgetting. -/
def mappingComplexUnderlying (k : ParameterMarking) (X Y : Marked.{u}) :
    mappingComplex k X Y ⟶ parameterMapping X.toSSet Y.toSSet := by
  cases k <;> exact
    { app := fun _ => ↾fun f => f.hom
      naturality := fun _ _ _ => by
        apply ConcreteCategory.hom_ext
        intro f
        rfl }

/-- The minimal-parameter forgetful map retains the complete original prism. -/
@[simp]
theorem mappingComplexUnderlying_min_app (X Y : Marked.{u}) (n : ℕ)
    (f : (mappingComplex .minimal X Y) _⦋n⦌) :
    (mappingComplexUnderlying .minimal X Y).app (op ⦋n⦌) f = f.hom := rfl

/-- The maximal-parameter forgetful map retains the complete original prism. -/
@[simp]
theorem mappingComplexUnderlying_max_app (X Y : Marked.{u}) (n : ℕ)
    (f : (mappingComplex .maximal X Y) _⦋n⦌) :
    (mappingComplexUnderlying .maximal X Y).app (op ⦋n⦌) f = f.hom := rfl

/-- Different marked mapping simplices have different underlying original prisms. -/
theorem mappingComplexUnderlying_app_injective (k : ParameterMarking) (X Y : Marked.{u})
    (n : SimplexCategoryᵒᵖ) : Function.Injective ((mappingComplexUnderlying k X Y).app n) := by
  cases k <;> intro f g h <;> exact Hom.ext h

end SSet.Marked
