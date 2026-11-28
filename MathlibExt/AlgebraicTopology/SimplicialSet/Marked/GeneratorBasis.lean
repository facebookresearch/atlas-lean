/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.StrongGenerator
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# The actual marked simplex and edge basis

Objects are the original minimally marked standard simplices and the
maximally marked interval. All arrows are their actual marked maps,
including maps between different basis objects. The category over a
marked total space retains the whole original basis map and marking.
This is an object-presentation basis, not a claim about a model
generating family.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.GeneratorBasis

/-- The original basis labels with their full actual marked Hom maps. -/
abbrev Generator := InducedCategory Marked.{u} strongGeneratorObj.{u}

/-- The actual marked basis functor retains every original marked map between its labels. -/
def generatorFunctor : Generator.{u} ⥤ Marked.{u} := inducedFunctor strongGeneratorObj.{u}

/-- Basis objects over the supplied original marked total space retain their complete map. -/
abbrev Index (X : Marked.{u}) := CostructuredArrow generatorFunctor.{u} X

/-- The original full marked basis diagram over a supplied total space. -/
def diagram (X : Marked.{u}) : Index X ⥤ Marked.{u} :=
  CostructuredArrow.proj generatorFunctor X ⋙ generatorFunctor

/-- The original complete basis maps form their actual marked cocone with point the supplied total space. -/
def cocone (X : Marked.{u}) : Cocone (diagram X) where
  pt := X
  ι :=
    { app i := i.hom
      naturality i j f := by
        have h : generatorFunctor.map f.left ≫ j.hom = i.hom := CostructuredArrow.w f
        exact h.trans (Category.comp_id i.hom).symm }

/-- An original simplex gives precisely its minimally marked whole Yoneda basis map. -/
def simplex (X : Marked.{u}) (n : SimplexCategory) (x : X.toSSet.obj (op n)) : Index X :=
  CostructuredArrow.mk (C := Generator.{u}) (S := generatorFunctor) (Y := (some n.len : Generator))
    (ofMin (SSet.yonedaEquiv.symm x))

/-- An originally marked edge gives its actual maximally marked interval basis map. -/
def markedEdge (X : Marked.{u}) (e : X.toSSet _⦋1⦌) (he : e ∈ X.marking) : Index X :=
  CostructuredArrow.mk (C := Generator.{u}) (S := generatorFunctor) (Y := (none : Generator))
    (intervalMapOfMarkedEdge e he)

/-- Every original simplex operator is the corresponding whole marked basis restriction over the same total space. -/
def simplexRestriction (X : Marked.{u}) {n m : SimplexCategory} (f : n ⟶ m)
    (x : X.toSSet.obj (op m)) : simplex X n (X.toSSet.map f.op x) ⟶ simplex X m x :=
  CostructuredArrow.homMk ⟨minimal.map (SSet.stdSimplex.map f)⟩ (Hom.ext
    (SSet.yonedaEquiv_symm_naturality_left f x))

/-- The original identity underlying edge identifies the minimal and marked presentations of the same marked edge. -/
def edgeMarking (X : Marked.{u}) (e : X.toSSet _⦋1⦌) (he : e ∈ X.marking) :
    simplex X ⦋1⦌ e ⟶ markedEdge X e he :=
  CostructuredArrow.homMk ⟨toMax (𝟙 (Δ[1] : SSet.{u}))⟩ (Hom.ext rfl)

/-- The original simplex basis map retains its complete native Yoneda representative. -/
theorem simplex_hom (X : Marked.{u}) (n : SimplexCategory) (x : X.toSSet.obj (op n)) :
    (simplex X n x).hom.hom = SSet.yonedaEquiv.symm x := rfl

/-- Marked-edge basis maps keep precisely the same original edge and whole representative. -/
theorem markedEdge_hom (X : Marked.{u}) (e : X.toSSet _⦋1⦌) (he : e ∈ X.marking) :
    (markedEdge X e he).hom.hom = SSet.yonedaEquiv.symm e := rfl

end SSet.Marked.GeneratorBasis
