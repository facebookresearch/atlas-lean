/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Adjunction.Parametrized

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uD vD uV vV
open CategoryTheory

namespace CategoryTheory.ParametrizedAdjunction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {V : Type uV} [Category.{vV} V]

/-- Actual whole functor equalities transport all fixed adjunctions and source maps together. -/
def transportWhole {F F' : C ⥤ D ⥤ V} {G G' : Cᵒᵖ ⥤ V ⥤ D}
    (eF : F = F') (eG : G = G') (adj : F ⊣₂ G) : F' ⊣₂ G' := by
  subst F'
  subst G'
  exact adj

end CategoryTheory.ParametrizedAdjunction

universe u1 u2 u3 v1 v2 v3

namespace CategoryTheory.ParametrizedAdjunction

variable {C1 : Type u1} [Category.{v1} C1] {C2 : Type u2} [Category.{v2} C2]
  {C3 : Type u3} [Category.{v3} C3]
  {F : C1 ⥤ C2 ⥤ C3} {G G' : C1ᵒᵖ ⥤ C3 ⥤ C2}

/-- A supplied actual whole right bifunctor isomorphism transports
every adjunction and every source naturality square together. -/
def ofRightNatIso (adj : F ⊣₂ G) (e : G ≅ G') : F ⊣₂ G' :=
  mk' (fun X => (adj.adj X).ofNatIsoRight (e.app (Opposite.op X))) (by
    intro X Y f A B g
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_ofNatIsoRight_apply]
    have hL := congrArg (fun h => h ≫ (e.app (Opposite.op X)).hom.app B)
      (adj.homEquiv_naturality_one f g)
    have hn := congrArg (fun t => t.app B) (e.hom.naturality f.op)
    exact hL.trans ((Category.assoc _ _ _).trans
      ((congrArg (fun t => adj.homEquiv g ≫ t) hn).trans (Category.assoc _ _ _).symm)))

/-- Actual transport retains every whole original Hom conversion,
followed by its actual supplied right comparison component. -/
theorem ofRightNatIso_homEquiv (adj : F ⊣₂ G) (e : G ≅ G')
    {X : C1} {A : C2} {B : C3} (f : (F.obj X).obj A ⟶ B) :
    ((ofRightNatIso adj e).adj X).homEquiv A B f =
      (adj.adj X).homEquiv A B f ≫ (e.app (Opposite.op X)).hom.app B :=
  Adjunction.homEquiv_ofNatIsoRight_apply (adj.adj X) (e.app (Opposite.op X)) f

end CategoryTheory.ParametrizedAdjunction
