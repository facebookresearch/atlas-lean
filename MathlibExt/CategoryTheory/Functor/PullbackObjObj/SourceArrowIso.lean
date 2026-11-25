/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uD vD uV vV
open CategoryTheory

namespace CategoryTheory.Functor.PullbackObjObj

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {V : Type uV} [Category.{vV} V] {G : Cᵒᵖ ⥤ V ⥤ D}

/-- An actual isomorphic first corner projection identifies its whole original source Arrow. -/
def sourceArrowIso {X Y : C} {Z U : V} {p : X ⟶ Y} {q : Z ⟶ U}
    (pb : G.PullbackObjObj p q) (h : IsIso pb.fst) :
    Arrow.mk pb.π ≅ Arrow.mk ((G.map p.op).app Z) := by
  letI : IsIso pb.fst := h
  exact Arrow.isoMk' _ _ (Iso.refl _) (asIso pb.fst) (by simp)

end CategoryTheory.Functor.PullbackObjObj
