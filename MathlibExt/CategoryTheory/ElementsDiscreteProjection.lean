/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Actual discrete coefficient projections from full original elements categories

An original natural transformation to a constant coefficient set gives
the full original elements projection. Its arrow equations retain the
original element map and original naturality. The comparison square
uses actual original coefficient isomorphisms and all original Homs.
Index object, index Hom and coefficient universes are independent.
-/

noncomputable section
universe uJ vJ u
open CategoryTheory
namespace CategoryTheory
variable {J : Type uJ} [Category.{vJ} J] {F G : J ⥤ Type u} {Z W : Type u}

/-- The full original elements projection from an actual natural map to a constant
coefficient set. -/
def Functor.Elements.discreteProjection (τ : F ⟶ (Functor.const J).obj Z) : F.Elements
  ⥤ Discrete Z where
  obj E := Discrete.mk (τ.app E.obj E.val)
  map {E E'} f := Discrete.eqToHom
    ((τ.naturality_apply f.hom E.val).symm.trans (congrArg (τ.app E'.obj) f.map_val))
  map_id _E := Subsingleton.elim _ _
  map_comp _f _g := Subsingleton.elim _ _

/-- An actual original natural isomorphism gives the full original elements equivalence with
its genuine inverse. -/
def NatIso.elementsEquivalence (e : F ≅ G) : F.Elements ≌ G.Elements :=
  Cat.equivOfIso (Functor.elementsFunctor.mapIso e)

/-- The actual original elements equivalence retains the literal original element map functor. -/
theorem NatIso.elementsEquivalence_functor (e : F ≅ G) :
    (NatIso.elementsEquivalence e).functor = e.hom.mapElements := rfl

/-- The full original elements/discrete square retains the entire actual original
coefficient comparison. -/
def Functor.Elements.discreteProjectionComparison (e : F ≅ G)
    (τ : F ⟶ (Functor.const J).obj Z) (υ : G ⟶ (Functor.const J).obj W) (p : Z ≅ W)
    (h : e.hom ≫ υ = τ ≫ (Functor.const J).map p.hom) :
    e.hom.mapElements ⋙ Functor.Elements.discreteProjection υ ≅
      Functor.Elements.discreteProjection τ ⋙ Discrete.functor (fun z => Discrete.mk (p.hom z)) :=
  NatIso.ofComponents
    (fun E => by
      apply Discrete.eqToIso
      change υ.app E.obj (e.hom.app E.obj E.val) = p.hom (τ.app E.obj E.val)
      exact ConcreteCategory.congr_hom (NatTrans.congr_app h E.obj) E.val)
    (fun _f => Subsingleton.elim _ _)

end CategoryTheory
