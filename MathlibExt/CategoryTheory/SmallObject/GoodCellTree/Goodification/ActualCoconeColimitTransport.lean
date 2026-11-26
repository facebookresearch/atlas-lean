/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Actual lower-colimit transport by full functor and original leg comparisons

A proved equality of complete actual diagrams and the original point/leg
comparisons construct the full new colimit universal property from the
actual old colimit. The cocone isomorphism is constructed from these maps;
no desired new colimit or cocone isomorphism is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.ActualCoconeColimitTransport

open Limits

variable {I : Type w} [Category.{w} I] {C : Type u} [Category.{v} C]
  {F G : I ⥤ C} (hF : F = G) (sF : Cocone F) (sG : Cocone G)
  (hPoint : sF.pt = sG.pt) (hLegs : ∀ p : I, sF.ι.app p ≍ sG.ι.app p)

/-- The complete actual old cocone is precomposed by the full proved original diagram equality. -/
abbrev transportedCocone : Cocone F := (Cocone.precompose (eqToHom hF)).obj sG

include hLegs in
/-- Each actual transported leg keeps the complete original leg and selected-point comparison. -/
theorem transported_leg (p : I) :
    (transportedCocone hF sG).ι.app p ≫ eqToHom hPoint.symm = sF.ι.app p := by
  change ((eqToHom hF : F ⟶ G).app p ≫ sG.ι.app p) ≫ eqToHom hPoint.symm = sF.ι.app p
  rw [eqToHom_app]
  exact eq_of_heq
    ((comp_eqToHom_heq (eqToHom (Functor.congr_obj hF p) ≫ sG.ι.app p) hPoint.symm).trans
      ((eqToHom_comp_heq (sG.ι.app p) (Functor.congr_obj hF p)).trans (hLegs p).symm))

/-- The complete actual cocone isomorphism is constructed from original full diagram/leg data. -/
def coconeIso : transportedCocone hF sG ≅ sF :=
  Cocone.ext (eqToIso hPoint.symm) (transported_leg hF sF sG hPoint hLegs)

/-- The old actual colimit UP constructs the new complete actual colimit UP. -/
def isColimit (hG : IsColimit sG) : IsColimit sF :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (eqToIso hF) sG).symm hG)
    (coconeIso hF sF sG hPoint hLegs)

end CategoryTheory.SmallObject.ActualCoconeColimitTransport
