/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Whiskering

/-!
# Actual scalar Hom complexes of covariant simplex diagrams

Coefficient Yoneda gives a genuine functor from the opposite-coefficient
simplicial-object category to simplicial sets. Its ordinary maps are the
whole original precomposition maps. For the standard simplex diagram,
the actual simplicial Yoneda isomorphism recovers the entire supplied
simplicial set, with no model or comparison outcome assumption.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FrameHom

/-- The genuine ordinary Hom-complex functor given by coefficient Yoneda at the supplied original simplicial set. -/
def functor (H : SSet.{u}) : SimplicialObject (SSet.{u}ᵒᵖ) ⥤ SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ (SSet.{u}ᵒᵖ) (Type u)).obj (yoneda.obj H)

/-- The actual whole Hom complex of a supplied original covariant simplex diagram. -/
def complex (Q : SimplexCategory ⥤ SSet.{u}) (H : SSet.{u}) : SSet.{u} := (functor H).obj Q.op

/-- Every actual source-diagram map acts by the same whole original scalar precomposition. -/
theorem map_app (H : SSet.{u}) {X Y : SimplicialObject (SSet.{u}ᵒᵖ)}
    (f : X ⟶ Y) (q : SimplexCategoryᵒᵖ) (g : unop (X.obj q) ⟶ H) :
    ((functor H).map f).app q g = (f.app q).unop ≫ g := rfl

/-- Every original scalar operator of the complex is actual precomposition by the same covariant diagram operator. -/
theorem complex_operator (Q : SimplexCategory ⥤ SSet.{u}) (H : SSet.{u})
    {n m : SimplexCategory} (θ : n ⟶ m) (f : Q.obj m ⟶ H) :
    (complex Q H).map θ.op f = Q.map θ ≫ f := rfl

/-- The genuine whole standard-simplex Hom-complex isomorphism with the supplied original simplicial set. -/
def standardIso (H : SSet.{u}) : complex SSet.stdSimplex H ≅ H :=
  NatIso.ofComponents (fun q => (SSet.yonedaEquiv (X := H) (n := q.unop)).toIso) (fun θ => by
    ext f
    exact (SSet.yonedaEquiv_naturality θ.unop f).symm)

/-- The actual standard-complex isomorphism reads every original Hom map by its same original simplicial
  Yoneda evaluation. -/
theorem standardIso_hom_app (H : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (f : SSet.stdSimplex.obj q.unop ⟶ H) : (standardIso H).hom.app q f = SSet.yonedaEquiv f := rfl

/-- The actual inverse retains every supplied individual original scalar simplex as its whole standard-simplex map. -/
theorem standardIso_inv_app (H : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x : H.obj q) :
    (standardIso H).inv.app q x = SSet.yonedaEquiv.symm x := rfl

end CategoryTheory.CoherentRealization.FrameHom
