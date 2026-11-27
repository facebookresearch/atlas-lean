/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.InducedOrdinary
public import MathlibExt.CategoryTheory.Enriched.PointFunctionTransport

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uD vD

open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.InducedCategory

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {A : Type uA} {D : Type uD} [Category.{vD} D] [EnrichedOrdinaryCategory V D]
  (f : A → Dᵒᵖ)

/-- The whole induced opposite point function retains its original endpoint isomorphism. -/
theorem enrichedOrdinaryCategory_opposite_point_function_eqToIso
    (a b : InducedCategory Dᵒᵖ f)
    (h : (enrichedOrdinaryCategory V f).toEnrichedCategory.Hom a b =
      ((f b).unop ⟶[V] (f a).unop)) :
    (fun g : a ⟶ b => (enrichedOrdinaryCategory V f).homEquiv g ≫ (eqToIso h).hom) =
      (fun g : a ⟶ b => eHomEquiv V (C := D) g.hom.unop) := by
  exact EnrichedPointFunctionTransport.point_function_eqToIso h _ _
    (heq_of_eq (enrichedOrdinaryCategory_opposite_point_function V f a b))

/-- Each original source point uses the same full projected and reversed original arrow. -/
@[reassoc]
theorem enrichedOrdinaryCategory_opposite_point_eqToIso
    (a b : InducedCategory Dᵒᵖ f)
    (h : (enrichedOrdinaryCategory V f).toEnrichedCategory.Hom a b =
      ((f b).unop ⟶[V] (f a).unop)) (g : a ⟶ b) :
    (enrichedOrdinaryCategory V f).homEquiv g ≫ (eqToIso h).hom =
      eHomEquiv V (C := D) g.hom.unop := by
  exact congrFun (enrichedOrdinaryCategory_opposite_point_function_eqToIso V f a b h) g

/-- The entire inverse point function recovers the same original induced opposite arrow. -/
theorem enrichedOrdinaryCategory_opposite_inverse_function_eqToIso
    (a b : InducedCategory Dᵒᵖ f)
    (h : (enrichedOrdinaryCategory V f).toEnrichedCategory.Hom a b =
      ((f b).unop ⟶[V] (f a).unop)) :
    (fun p : 𝟙_ V ⟶ ((f b).unop ⟶[V] (f a).unop) =>
      (enrichedOrdinaryCategory V f).homEquiv.symm (p ≫ (eqToIso h).inv)) =
        (fun p => InducedCategory.homMk (D := Dᵒᵖ) (F := f) (X := a) (Y := b)
          (((eHomEquiv V (C := D) (X := (f b).unop) (Y := (f a).unop)).symm p).op)) := by
  have hr : h = rfl := Subsingleton.elim _ _
  cases hr
  funext p
  rw [eqToIso_refl, Iso.refl_inv]
  exact (congrArg (enrichedOrdinaryCategory V f).homEquiv.symm (Category.comp_id p)).trans
    (congrFun (enrichedOrdinaryCategory_opposite_inverse_function V f a b) p)

end CategoryTheory.InducedCategory
