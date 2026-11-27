/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.CentralGradedInputActions

/-!
# Both actual input actions on the full central Hom presheaf

Original diagram maps act on every actual central grade. The actions are
natural transformations with full identity, composition and interchange
laws, and define the two ordinary diagram-variable presheaf functors.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uI uV vV
open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalClosed
namespace MathlibExtTest.CentralGradedInputActions
open CategoryTheory.EnrichedFunctorCat
attribute [local instance] MonoidalClosed.enrichedCategorySelf
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

example : True := by
  fail_if_success letI : Category I := inferInstance
  trivial

example {F' F G : EnrichedFunctorCat V I} (p : F' ⟶ F) :
    centralGradedYoneda F.toEnrichedFunctor G.toEnrichedFunctor ⟶
      centralGradedYoneda F'.toEnrichedFunctor G.toEnrichedFunctor :=
  centralGradedYonedaPrecomp p

example {F' F G : EnrichedFunctorCat V I} (p : F' ⟶ F)
    (Γ : Center V) (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    (centralGradedYonedaPrecomp p).app (op Γ) t = gradedPrecomp Γ p t :=
  centralGradedYonedaPrecomp_app p Γ t

example (F G : EnrichedFunctorCat V I) : centralGradedYonedaPrecomp (G := G) (𝟙 F) =
    𝟙 (centralGradedYoneda F.toEnrichedFunctor G.toEnrichedFunctor) :=
  centralGradedYonedaPrecomp_id F G

example {F₀ F₁ F₂ G : EnrichedFunctorCat V I} (p : F₀ ⟶ F₁) (q : F₁ ⟶ F₂) :
    centralGradedYonedaPrecomp (G := G) (p ≫ q) =
      centralGradedYonedaPrecomp (G := G) q ≫ centralGradedYonedaPrecomp (G := G) p :=
  centralGradedYonedaPrecomp_comp p q

example {F G G' : EnrichedFunctorCat V I} (q : G ⟶ G') :
    centralGradedYoneda F.toEnrichedFunctor G.toEnrichedFunctor ⟶
      centralGradedYoneda F.toEnrichedFunctor G'.toEnrichedFunctor :=
  centralGradedYonedaPostcomp q

example {F G G' : EnrichedFunctorCat V I} (q : G ⟶ G')
    (Γ : Center V) (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    (centralGradedYonedaPostcomp q).app (op Γ) t = gradedPostcomp Γ t q :=
  centralGradedYonedaPostcomp_app q Γ t

example (F G : EnrichedFunctorCat V I) : centralGradedYonedaPostcomp (F := F) (𝟙 G) =
    𝟙 (centralGradedYoneda F.toEnrichedFunctor G.toEnrichedFunctor) :=
  centralGradedYonedaPostcomp_id F G

example {F G₀ G₁ G₂ : EnrichedFunctorCat V I} (q : G₀ ⟶ G₁) (r : G₁ ⟶ G₂) :
    centralGradedYonedaPostcomp (F := F) (q ≫ r) =
      centralGradedYonedaPostcomp (F := F) q ≫ centralGradedYonedaPostcomp (F := F) r :=
  centralGradedYonedaPostcomp_comp q r

example {F' F G G' : EnrichedFunctorCat V I} (p : F' ⟶ F) (q : G ⟶ G') :
    centralGradedYonedaPrecomp (G := G) p ≫ centralGradedYonedaPostcomp (F := F') q =
      centralGradedYonedaPostcomp (F := F) q ≫ centralGradedYonedaPrecomp (G := G') p :=
  centralGradedYonedaPrecomp_postcomp p q

example (G : EnrichedFunctorCat V I) :
    (EnrichedFunctorCat V I)ᵒᵖ ⥤ ((Center V)ᵒᵖ ⥤ Type (max uI vV)) :=
  centralGradedYonedaSource G

example (F : EnrichedFunctorCat V I) :
    EnrichedFunctorCat V I ⥤ ((Center V)ᵒᵖ ⥤ Type (max uI vV)) :=
  centralGradedYonedaTarget F

example {F' F G : EnrichedFunctorCat V I} (p : F' ⟶ F) :
    (centralGradedYonedaSource G).map p.op = centralGradedYonedaPrecomp p := rfl

example {F G G' : EnrichedFunctorCat V I} (q : G ⟶ G') :
    (centralGradedYonedaTarget F).map q = centralGradedYonedaPostcomp q := rfl

example {F' F G : EnrichedFunctorCat V I} (p : F' ⟶ F)
    {Γ Δ : (Center V)ᵒᵖ} (f : Γ ⟶ Δ)
    (t : GradedNatTrans Γ.unop F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedPrecomp Δ.unop p (GradedNatTrans.regrade f.unop t) =
      GradedNatTrans.regrade f.unop (gradedPrecomp Γ.unop p t) :=
  congrArg (fun k => k t) ((centralGradedYonedaPrecomp p).naturality f)

example {F G G' : EnrichedFunctorCat V I} (q : G ⟶ G')
    {Γ Δ : (Center V)ᵒᵖ} (f : Γ ⟶ Δ)
    (t : GradedNatTrans Γ.unop F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedPostcomp Δ.unop (GradedNatTrans.regrade f.unop t) q =
      GradedNatTrans.regrade f.unop (gradedPostcomp Γ.unop t q) :=
  congrArg (fun k => k t) ((centralGradedYonedaPostcomp q).naturality f)
end MathlibExtTest.CentralGradedInputActions
