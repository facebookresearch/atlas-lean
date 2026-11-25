/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.CentralGradedYoneda
public import MathlibExt.CategoryTheory.Enriched.GradedInputComposition

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
namespace CategoryTheory.EnrichedFunctorCat
attribute [local instance] MonoidalClosed.enrichedCategorySelf
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

set_option maxHeartbeats 200000 in
-- Retain the entire original source action and full raw coefficient naturality.
/-- A genuine source diagram map acts naturally on the entire central Hom presheaf. -/
def centralGradedYonedaPrecomp {F' F G : EnrichedFunctorCat V I} (p : F' ⟶ F) :
    centralGradedYoneda F.toEnrichedFunctor G.toEnrichedFunctor ⟶
      centralGradedYoneda F'.toEnrichedFunctor G.toEnrichedFunctor where
  app Γ := ↾fun t => gradedPrecomp Γ.unop p t
  naturality := by
    intro Γ Δ f
    apply ConcreteCategory.hom_ext
    intro t
    exact gradedPrecomp_regrade f.unop p t

/-- Every given actual grade sees the complete original source action. -/
theorem centralGradedYonedaPrecomp_app {F' F G : EnrichedFunctorCat V I} (p : F' ⟶ F)
    (Γ : Center V) (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    (centralGradedYonedaPrecomp p).app (op Γ) t = gradedPrecomp Γ p t := rfl

set_option maxHeartbeats 200000 in
-- Retain both entire presheaf transformations in the actual source identity law.
/-- The actual source identity is the identity transformation of the full central presheaf. -/
theorem centralGradedYonedaPrecomp_id (F G : EnrichedFunctorCat V I) :
    centralGradedYonedaPrecomp (G := G) (𝟙 F) =
      𝟙 (centralGradedYoneda F.toEnrichedFunctor G.toEnrichedFunctor) := by
  apply NatTrans.ext
  funext Γ
  apply ConcreteCategory.hom_ext
  intro t
  exact gradedPrecomp_id Γ.unop t

set_option maxHeartbeats 200000 in
-- Retain the complete original contravariant source composition as a NatTrans equality.
/-- Source composition acts contravariantly on every actual central grade. -/
theorem centralGradedYonedaPrecomp_comp {F₀ F₁ F₂ G : EnrichedFunctorCat V I}
    (p : F₀ ⟶ F₁) (q : F₁ ⟶ F₂) :
    centralGradedYonedaPrecomp (G := G) (p ≫ q) =
      centralGradedYonedaPrecomp (G := G) q ≫ centralGradedYonedaPrecomp (G := G) p := by
  apply NatTrans.ext
  funext Γ
  apply ConcreteCategory.hom_ext
  intro t
  exact gradedPrecomp_comp Γ.unop p q t

set_option maxHeartbeats 200000 in
-- Retain the entire original target action and full raw coefficient naturality.
/-- A genuine target diagram map acts naturally on the entire central Hom presheaf. -/
def centralGradedYonedaPostcomp {F G G' : EnrichedFunctorCat V I} (q : G ⟶ G') :
    centralGradedYoneda F.toEnrichedFunctor G.toEnrichedFunctor ⟶
      centralGradedYoneda F.toEnrichedFunctor G'.toEnrichedFunctor where
  app Γ := ↾fun t => gradedPostcomp Γ.unop t q
  naturality := by
    intro Γ Δ f
    apply ConcreteCategory.hom_ext
    intro t
    exact gradedPostcomp_regrade f.unop t q

/-- Every given actual grade sees the complete original target action. -/
theorem centralGradedYonedaPostcomp_app {F G G' : EnrichedFunctorCat V I} (q : G ⟶ G')
    (Γ : Center V) (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    (centralGradedYonedaPostcomp q).app (op Γ) t = gradedPostcomp Γ t q := rfl

set_option maxHeartbeats 200000 in
-- Retain both entire presheaf transformations in the actual target identity law.
/-- The actual target identity is the identity transformation of the full central presheaf. -/
theorem centralGradedYonedaPostcomp_id (F G : EnrichedFunctorCat V I) :
    centralGradedYonedaPostcomp (F := F) (𝟙 G) =
      𝟙 (centralGradedYoneda F.toEnrichedFunctor G.toEnrichedFunctor) := by
  apply NatTrans.ext
  funext Γ
  apply ConcreteCategory.hom_ext
  intro t
  exact gradedPostcomp_id Γ.unop t

set_option maxHeartbeats 200000 in
-- Retain the complete original covariant target composition as a NatTrans equality.
/-- Target composition acts covariantly on every actual central grade. -/
theorem centralGradedYonedaPostcomp_comp {F G₀ G₁ G₂ : EnrichedFunctorCat V I}
    (q : G₀ ⟶ G₁) (r : G₁ ⟶ G₂) :
    centralGradedYonedaPostcomp (F := F) (q ≫ r) =
      centralGradedYonedaPostcomp (F := F) q ≫ centralGradedYonedaPostcomp (F := F) r := by
  apply NatTrans.ext
  funext Γ
  apply ConcreteCategory.hom_ext
  intro t
  exact gradedPostcomp_comp Γ.unop t q r

set_option maxHeartbeats 200000 in
-- Keep both actual diagram maps and the entire full-center presheaf square.
/-- The original source and target actions commute as complete presheaf transformations. -/
theorem centralGradedYonedaPrecomp_postcomp {F' F G G' : EnrichedFunctorCat V I}
    (p : F' ⟶ F) (q : G ⟶ G') :
    centralGradedYonedaPrecomp (G := G) p ≫ centralGradedYonedaPostcomp (F := F') q =
      centralGradedYonedaPostcomp (F := F) q ≫ centralGradedYonedaPrecomp (G := G') p := by
  apply NatTrans.ext
  funext Γ
  apply ConcreteCategory.hom_ext
  intro t
  exact (gradedPrecomp_postcomp Γ.unop p t q).symm

set_option maxHeartbeats 200000 in
-- Use the actual complete source maps and their proved identity/composition equations.
/-- The full central Hom presheaf is functorial in the actual contravariant diagram variable. -/
def centralGradedYonedaSource (G : EnrichedFunctorCat V I) :
    (EnrichedFunctorCat V I)ᵒᵖ ⥤ ((Center V)ᵒᵖ ⥤ Type (max uI vV)) where
  obj F := centralGradedYoneda F.unop.toEnrichedFunctor G.toEnrichedFunctor
  map p := centralGradedYonedaPrecomp p.unop
  map_id F := centralGradedYonedaPrecomp_id F.unop G
  map_comp p q := centralGradedYonedaPrecomp_comp q.unop p.unop

set_option maxHeartbeats 200000 in
-- Use the actual complete target maps and their proved identity/composition equations.
/-- The full central Hom presheaf is functorial in the actual covariant diagram variable. -/
def centralGradedYonedaTarget (F : EnrichedFunctorCat V I) :
    EnrichedFunctorCat V I ⥤ ((Center V)ᵒᵖ ⥤ Type (max uI vV)) where
  obj G := centralGradedYoneda F.toEnrichedFunctor G.toEnrichedFunctor
  map q := centralGradedYonedaPostcomp q
  map_id G := centralGradedYonedaPostcomp_id F G
  map_comp q r := centralGradedYonedaPostcomp_comp q r

end CategoryTheory.EnrichedFunctorCat
