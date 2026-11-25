/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.GradedComposition
public import Mathlib.CategoryTheory.Types.Basic

/-!
# The graded Hom presheaf on the actual center

Every central grade and every morphism in the center is retained. The
canonical ambient profile is the pinned enrichedNatTransYoneda presheaf.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uC uD uV vV
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C] {D : Type uD} [EnrichedCategory V D]
  (F G : EnrichedFunctor V C D)

set_option maxHeartbeats 200000 in
-- Keep actual central morphisms in both functoriality laws on the full raw records.
/-- The full raw graded Hom presheaf retains every actual grade in the center. -/
def centralGradedYoneda : (Center V)ᵒᵖ ⥤ Type (max uC vV) where
  obj Γ := GradedNatTrans Γ.unop F G
  map f := ↾fun t => GradedNatTrans.regrade f.unop t
  map_id Γ := by
    apply ConcreteCategory.hom_ext
    intro t
    apply GradedNatTrans.ext
    funext a
    change (𝟙 Γ.unop.1) ≫ t.app a = t.app a
    exact Category.id_comp _
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro t
    apply GradedNatTrans.ext
    funext a
    change (g.unop.f ≫ f.unop.f) ≫ t.app a = g.unop.f ≫ f.unop.f ≫ t.app a
    exact Category.assoc _ _ _

/-- Every presheaf value is the complete raw natural-transformation type in the given grade. -/
theorem centralGradedYoneda_obj (Γ : Center V) :
    (centralGradedYoneda F G).obj (op Γ) = GradedNatTrans Γ F G := rfl

/-- Every actual central coefficient arrow acts by the original regrade function. -/
theorem centralGradedYoneda_map {Γ Δ : (Center V)ᵒᵖ} (f : Γ ⟶ Δ)
    (t : GradedNatTrans Γ.unop F G) :
    (centralGradedYoneda F G).map f t = GradedNatTrans.regrade f.unop t := rfl

/-- Every raw component is precomposed by the actual underlying central morphism. -/
theorem centralGradedYoneda_map_app {Γ Δ : (Center V)ᵒᵖ} (f : Γ ⟶ Δ)
    (t : GradedNatTrans Γ.unop F G) (a : C) :
    ((centralGradedYoneda F G).map f t).app a = f.unop.f ≫ t.app a := rfl

variable [BraidedCategory V]

set_option maxHeartbeats 200000 in
-- Compare both actual functors and every entire map before identifying the canonical profile.
/-- The actual ambient-center specialization is the pinned graded Hom presheaf. -/
def centralGradedYonedaOfBraidedIso :
    (Center.ofBraided V).op ⋙ centralGradedYoneda F G ≅ enrichedNatTransYoneda F G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K K' f
    apply ConcreteCategory.hom_ext
    intro t
    apply GradedNatTrans.ext
    funext a
    rfl)

/-- The canonical forward specialization retains the entire given raw transformation. -/
theorem centralGradedYonedaOfBraidedIso_hom_app (M : V)
    (t : GradedNatTrans ((Center.ofBraided V).obj M) F G) :
    (centralGradedYonedaOfBraidedIso F G).hom.app (op M) t = t := rfl

/-- The canonical inverse specialization retains the entire given raw transformation. -/
theorem centralGradedYonedaOfBraidedIso_inv_app (M : V)
    (t : GradedNatTrans ((Center.ofBraided V).obj M) F G) :
    (centralGradedYonedaOfBraidedIso F G).inv.app (op M) t = t := rfl

end CategoryTheory
