/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.CentralGradedYoneda

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uC uD uV vV
open CategoryTheory MonoidalCategory Opposite
namespace MathlibExtTest.CentralGradedYoneda
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C] {D : Type uD} [EnrichedCategory V D]
  (F G : EnrichedFunctor V C D)

example : True := by
  fail_if_success letI : Category C := inferInstance
  trivial

example (Γ : Center V) :
    (centralGradedYoneda F G).obj (op Γ) = GradedNatTrans Γ F G :=
  centralGradedYoneda_obj F G Γ

example {Γ Δ : (Center V)ᵒᵖ} (f : Γ ⟶ Δ) (t : GradedNatTrans Γ.unop F G) :
    (centralGradedYoneda F G).map f t = GradedNatTrans.regrade f.unop t :=
  centralGradedYoneda_map F G f t

example {Γ Δ : (Center V)ᵒᵖ} (f : Γ ⟶ Δ) (t : GradedNatTrans Γ.unop F G) (a : C) :
    ((centralGradedYoneda F G).map f t).app a = f.unop.f ≫ t.app a :=
  centralGradedYoneda_map_app F G f t a

example (Γ : (Center V)ᵒᵖ) (t : GradedNatTrans Γ.unop F G) :
    (centralGradedYoneda F G).map (𝟙 Γ) t = t := by
  exact congrArg (fun f => f t) ((centralGradedYoneda F G).map_id Γ)

example {Γ Δ Θ : (Center V)ᵒᵖ} (f : Γ ⟶ Δ) (g : Δ ⟶ Θ)
    (t : GradedNatTrans Γ.unop F G) :
    (centralGradedYoneda F G).map (f ≫ g) t =
      (centralGradedYoneda F G).map g ((centralGradedYoneda F G).map f t) := by
  exact congrArg (fun h => h t) ((centralGradedYoneda F G).map_comp f g)

variable [BraidedCategory V]
example : (Center.ofBraided V).op ⋙ centralGradedYoneda F G ≅ enrichedNatTransYoneda F G :=
  centralGradedYonedaOfBraidedIso F G

example (M : V) (t : GradedNatTrans ((Center.ofBraided V).obj M) F G) :
    (centralGradedYonedaOfBraidedIso F G).hom.app (op M) t = t :=
  centralGradedYonedaOfBraidedIso_hom_app F G M t

example (M : V) (t : GradedNatTrans ((Center.ofBraided V).obj M) F G) :
    (centralGradedYonedaOfBraidedIso F G).inv.app (op M) t = t :=
  centralGradedYonedaOfBraidedIso_inv_app F G M t

example : (centralGradedYonedaOfBraidedIso F G).hom ≫
    (centralGradedYonedaOfBraidedIso F G).inv = 𝟙 _ :=
  (centralGradedYonedaOfBraidedIso F G).hom_inv_id

example : (centralGradedYonedaOfBraidedIso F G).inv ≫
    (centralGradedYonedaOfBraidedIso F G).hom = 𝟙 _ :=
  (centralGradedYonedaOfBraidedIso F G).inv_hom_id
end MathlibExtTest.CentralGradedYoneda
