/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.FreeYoneda

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- The unit-coefficient free evaluation retains the entire original operator Hom object. -/
@[no_expose]
def evaluateHom (a b : A) (t : Free.object b (𝟙_ V) ⟶ Free.object a (𝟙_ V)) :
    𝟙_ V ⟶ (a ⟶[V] b) :=
  Free.evaluate b (𝟙_ V) (Free.object a (𝟙_ V)) t ≫ (λ_ (a ⟶[V] b)).hom

/-- Genuine free-module maps correspond to every original unit-Hom parameter. -/
@[no_expose]
def homEquiv (a b : A) :
    (Free.object b (𝟙_ V) ⟶ Free.object a (𝟙_ V)) ≃ (𝟙_ V ⟶ (a ⟶[V] b)) :=
  (Free.homEquiv b (𝟙_ V) (Free.object a (𝟙_ V))).trans
    (Iso.homCongr (Iso.refl (𝟙_ V)) (λ_ (a ⟶[V] b)))

/-- The whole original forward map is identity evaluation and the actual left unitor. -/
theorem homEquiv_apply (a b : A)
    (t : Free.object b (𝟙_ V) ⟶ Free.object a (𝟙_ V)) :
    homEquiv a b t = evaluateHom a b t := by
  change (𝟙 (𝟙_ V)) ≫ Free.evaluate b (𝟙_ V) (Free.object a (𝟙_ V)) t ≫
    (λ_ (a ⟶[V] b)).hom = evaluateHom a b t
  exact Category.id_comp _

/-- The whole original inverse map extends the actual unit-Hom parameter through all Homs. -/
theorem homEquiv_symm_apply (a b : A) (p : 𝟙_ V ⟶ (a ⟶[V] b)) :
    (homEquiv a b).symm p =
      Free.extend b (𝟙_ V) (Free.object a (𝟙_ V)) (p ≫ (λ_ (a ⟶[V] b)).inv) := by
  change Free.extend b (𝟙_ V) (Free.object a (𝟙_ V))
    ((𝟙 (𝟙_ V)) ≫ p ≫ (λ_ (a ⟶[V] b)).inv) = _
  rw [Category.id_comp]

omit [BraidedCategory V] [MonoidalClosed V] in
/-- Both actual unit-coefficient values produce the original ordered tensor pair. -/
@[reassoc]
theorem unitTensor_pair {X Y : V}
    (p : 𝟙_ V ⟶ (𝟙_ V) ⊗ X) (q : 𝟙_ V ⟶ (𝟙_ V) ⊗ Y) :
    q ≫ p ▷ Y ≫ (λ_ X).hom ▷ Y =
      (λ_ (𝟙_ V)).inv ≫ ((p ≫ (λ_ X).hom) ⊗ₘ (q ≫ (λ_ Y).hom)) := by
  rw [← comp_whiskerRight]
  have hq : q = (q ≫ (λ_ Y).hom) ≫ (λ_ Y).inv := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    q ≫ (p ≫ (λ_ X).hom) ▷ Y =
        ((q ≫ (λ_ Y).hom) ≫ (λ_ Y).inv) ≫ (p ≫ (λ_ X).hom) ▷ Y :=
      congrArg (fun z => z ≫ (p ≫ (λ_ X).hom) ▷ Y) hq
    _ = (λ_ (𝟙_ V)).inv ≫ (𝟙_ V) ◁ (q ≫ (λ_ Y).hom) ≫
        (p ≫ (λ_ X).hom) ▷ Y := by
      rw [Category.assoc, leftUnitor_inv_naturality_assoc]
    _ = _ := by rw [← tensorHom_def']

/-- The independent free-map identity evaluates to the full original operator identity. -/
theorem evaluateHom_id (a : A) :
    evaluateHom a a (𝟙 (Free.object a (𝟙_ V))) = eId V a := by
  unfold evaluateHom Free.evaluate
  rw [EnrichedFunctorCat.component_id, Category.comp_id, Category.assoc, leftUnitor_naturality,
    ← unitors_inv_equal, Iso.inv_hom_id_assoc]

/-- Actual free-map composition gives original source-first composition on both entire Homs. -/
theorem evaluateHom_comp (a b c : A)
    (t : Free.object b (𝟙_ V) ⟶ Free.object a (𝟙_ V))
    (u : Free.object c (𝟙_ V) ⟶ Free.object b (𝟙_ V)) :
    evaluateHom a c (u ≫ t) =
      (λ_ (𝟙_ V)).inv ≫ (evaluateHom a b t ⊗ₘ evaluateHom b c u) ≫ eComp V a b c := by
  let X : V := a ⟶[V] b
  let Y : V := b ⟶[V] c
  let Z : V := a ⟶[V] c
  let p : 𝟙_ V ⟶ (𝟙_ V) ⊗ X := Free.evaluate b (𝟙_ V) (Free.object a (𝟙_ V)) t
  let q : 𝟙_ V ⟶ (𝟙_ V) ⊗ Y := Free.evaluate c (𝟙_ V) (Free.object b (𝟙_ V)) u
  have ht : EnrichedFunctorCat.component t c = p ▷ Y ≫ Free.action a (𝟙_ V) b c := by
    simpa only [Free.extensionComponent, tensorHom_id, MonoidalClosed.uncurry_curry] using
      Free.reconstruct_component b (𝟙_ V) (Free.object a (𝟙_ V)) t c
  have hAction : Free.action a (𝟙_ V) b c ≫ (λ_ Z).hom =
      (λ_ X).hom ▷ Y ≫ eComp V a b c := by
    dsimp only [Free.action]
    simp only [Category.assoc]
    rw [leftUnitor_naturality, leftUnitor_tensor_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  change Free.evaluate c (𝟙_ V) (Free.object a (𝟙_ V)) (u ≫ t) ≫ (λ_ Z).hom =
    (λ_ (𝟙_ V)).inv ≫ ((p ≫ (λ_ X).hom) ⊗ₘ (q ≫ (λ_ Y).hom)) ≫ eComp V a b c
  have hPost : Free.evaluate c (𝟙_ V) (Free.object a (𝟙_ V)) (u ≫ t) =
      q ≫ EnrichedFunctorCat.component t c := by
    exact Free.evaluate_postcomp c (𝟙_ V) u t
  rw [hPost, ht]
  simp only [Category.assoc]
  rw [hAction]
  exact unitTensor_pair_assoc p q (eComp V a b c)

private theorem evaluateHom_eq_proof (a b : A)
    (t : Free.object b (𝟙_ V) ⟶ Free.object a (𝟙_ V)) :
    evaluateHom a b t = Free.evaluate b (𝟙_ V) (Free.object a (𝟙_ V)) t ≫
      (λ_ (a ⟶[V] b)).hom := rfl

/-- The entire actual original evaluation initializer keeps its whole free map and unitor. -/
theorem evaluateHom_eq (a b : A) (t : Free.object b (𝟙_ V) ⟶ Free.object a (𝟙_ V)) :
    evaluateHom a b t = Free.evaluate b (𝟙_ V) (Free.object a (𝟙_ V)) t ≫
      (λ_ (a ⟶[V] b)).hom := evaluateHom_eq_proof a b t

end CategoryTheory.EnrichedFunctorCat.FreeYoneda
