/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.GradedComposition

/-!
# Restriction of actual transformations in every central grade

Restriction keeps each original component and precomposes the two complete
source Hom maps. Its naturality uses the supplied center half-braiding.
No ordinary source category, ambient braiding, closedness or limits are used.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uB uC uV vV
open CategoryTheory MonoidalCategory

namespace CategoryTheory.GradedNatTrans

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for full graded restriction naturality.
private theorem restrict_naturality (j : EnrichedFunctor V A B) {Γ : Center V}
    {F G : EnrichedFunctor V B C} (t : GradedNatTrans Γ F G) (a b : A) :
    (Γ.2.β (a ⟶[V] b)).hom ≫
        (((j.comp V F).map a b) ⊗ₘ t.app (j.obj b)) ≫
        eComp V (F.obj (j.obj a)) (F.obj (j.obj b)) (G.obj (j.obj b)) =
      (t.app (j.obj a) ⊗ₘ ((j.comp V G).map a b)) ≫
        eComp V (F.obj (j.obj a)) (G.obj (j.obj a)) (G.obj (j.obj b)) := by
  let P : V := a ⟶[V] b
  let Q : V := j.obj a ⟶[V] j.obj b
  let u : P ⟶ Q := j.map a b
  let f := F.map (j.obj a) (j.obj b)
  let g := G.map (j.obj a) (j.obj b)
  have hLeft : (u ▷ Γ.1) ≫ (f ⊗ₘ t.app (j.obj b)) =
      (u ≫ f) ⊗ₘ t.app (j.obj b) := by
    simpa only [tensorHom_id, Category.id_comp] using
      tensorHom_comp_tensorHom u (𝟙 Γ.1) f (t.app (j.obj b))
  have hRight : (Γ.1 ◁ u) ≫ (t.app (j.obj a) ⊗ₘ g) =
      t.app (j.obj a) ⊗ₘ (u ≫ g) := by
    simpa only [id_tensorHom, Category.id_comp] using
      tensorHom_comp_tensorHom (𝟙 Γ.1) u (t.app (j.obj a)) g
  change (Γ.2.β P).hom ≫ ((u ≫ f) ⊗ₘ t.app (j.obj b)) ≫
      eComp V (F.obj (j.obj a)) (F.obj (j.obj b)) (G.obj (j.obj b)) =
    (t.app (j.obj a) ⊗ₘ (u ≫ g)) ≫
      eComp V (F.obj (j.obj a)) (G.obj (j.obj a)) (G.obj (j.obj b))
  calc
    _ = (Γ.2.β P).hom ≫ (u ▷ Γ.1) ≫ (f ⊗ₘ t.app (j.obj b)) ≫
        eComp V (F.obj (j.obj a)) (F.obj (j.obj b)) (G.obj (j.obj b)) := by
      simpa only [Category.assoc] using congrArg
        (fun h => (Γ.2.β P).hom ≫ h ≫
          eComp V (F.obj (j.obj a)) (F.obj (j.obj b)) (G.obj (j.obj b))) hLeft.symm
    _ = (Γ.1 ◁ u) ≫ (Γ.2.β Q).hom ≫ (f ⊗ₘ t.app (j.obj b)) ≫
        eComp V (F.obj (j.obj a)) (F.obj (j.obj b)) (G.obj (j.obj b)) := by
      simpa only [Category.assoc] using congrArg
        (fun h : Γ.1 ⊗ P ⟶ Q ⊗ Γ.1 => h ≫ (f ⊗ₘ t.app (j.obj b)) ≫
          eComp V (F.obj (j.obj a)) (F.obj (j.obj b)) (G.obj (j.obj b)))
        (Γ.2.naturality u).symm
    _ = (Γ.1 ◁ u) ≫ (t.app (j.obj a) ⊗ₘ g) ≫
        eComp V (F.obj (j.obj a)) (G.obj (j.obj a)) (G.obj (j.obj b)) :=
      congrArg (fun h => (Γ.1 ◁ u) ≫ h) (t.naturality (j.obj a) (j.obj b))
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun h => h ≫
        eComp V (F.obj (j.obj a)) (G.obj (j.obj a)) (G.obj (j.obj b))) hRight)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual all-grade restriction constructor.
/-- Restrict the original full transformation along the actual enriched source functor. -/
@[no_expose]
def restrict (j : EnrichedFunctor V A B) {Γ : Center V}
    {F G : EnrichedFunctor V B C} (t : GradedNatTrans Γ F G) :
    GradedNatTrans Γ (j.comp V F) (j.comp V G) where
  app a := t.app (j.obj a)
  naturality a b := restrict_naturality j t a b

private theorem restrict_app_private (j : EnrichedFunctor V A B) {Γ : Center V}
    {F G : EnrichedFunctor V B C} (t : GradedNatTrans Γ F G) (a : A) :
    (restrict j t).app a = t.app (j.obj a) := rfl

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for every complete original restricted component.
/-- All-grade restriction retains every entire original component. -/
theorem restrict_app (j : EnrichedFunctor V A B) {Γ : Center V}
    {F G : EnrichedFunctor V B C} (t : GradedNatTrans Γ F G) (a : A) :
    (restrict j t).app a = t.app (j.obj a) := restrict_app_private j t a

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for restriction of actual tensor composition.
/-- Restriction preserves actual tensor composition in its full source-first central grade. -/
theorem restrict_tensorComp (j : EnrichedFunctor V A B) {Γ Δ : Center V}
    {F G H : EnrichedFunctor V B C} (t : GradedNatTrans Γ F G) (u : GradedNatTrans Δ G H) :
    restrict j (tensorComp t u) = tensorComp (restrict j t) (restrict j u) := by
  apply GradedNatTrans.ext
  funext a
  rw [restrict_app, tensorComp_app, tensorComp_app, restrict_app, restrict_app]
  rfl

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for restriction after every actual central regrading.
/-- Restriction commutes with every genuine central coefficient morphism. -/
theorem restrict_regrade (j : EnrichedFunctor V A B) {Γ Δ : Center V} (h : Γ ⟶ Δ)
    {F G : EnrichedFunctor V B C} (t : GradedNatTrans Δ F G) :
    restrict j (regrade h t) = regrade h (restrict j t) := by
  apply GradedNatTrans.ext
  funext a
  rw [restrict_app, regrade_app, regrade_app, restrict_app]
  rfl

end CategoryTheory.GradedNatTrans
