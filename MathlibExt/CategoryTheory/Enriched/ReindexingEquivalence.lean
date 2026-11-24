/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.Enriched.Reindexing

/-!
# Reindexing along an actual equivalence retains both whole inverse functors

The original coefficient category, its Hom universe, and both object
universes are independent. The inverse uses only the proved object
equalities of the supplied equivalence. Every full original Hom map
and both whole enriched-functor identities are retained.
-/

@[expose] public section

noncomputable section
universe uV vV uC uO
open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedCategory

variable (V : Type uV) [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C] {O : Type uO}

/-- The inverse of the SAME full original projection along a supplied object equivalence. -/
def reindexInverse (e : O ≃ C) :
    let _ : EnrichedCategory V O := reindex V e
    EnrichedFunctor V C O := by
  let _ : EnrichedCategory V O := reindex V e
  exact {
    obj := e.symm
    map x y := eqToHom (congrArg₂ (fun a b : C => a ⟶[V] b)
      (e.apply_symm_apply x).symm (e.apply_symm_apply y).symm)
    map_id x := by
      have transport {a b : C} (h : a = b) :
          eId V a ≫ eqToHom (congrArg₂ (fun s t : C => s ⟶[V] t) h h) = eId V b := by
        cases h
        exact Category.comp_id _
      exact transport (e.apply_symm_apply x).symm
    map_comp x y z := by
      have transport {a b c a' b' c' : C} (ha : a = a') (hb : b = b') (hc : c = c') :
          eComp V a b c ≫ eqToHom (congrArg₂ (fun s t : C => s ⟶[V] t) ha hc) =
            (eqToHom (congrArg₂ (fun s t : C => s ⟶[V] t) ha hb) ⊗ₘ
              eqToHom (congrArg₂ (fun s t : C => s ⟶[V] t) hb hc)) ≫
                eComp V a' b' c' := by
        cases ha
        cases hb
        cases hc
        simp only [eqToHom_refl, Category.comp_id, id_tensorHom_id, Category.id_comp]
      exact transport (e.apply_symm_apply x).symm
        (e.apply_symm_apply y).symm (e.apply_symm_apply z).symm }

/-- The actual inverse object map is the SAME supplied inverse function. -/
theorem reindexInverse_obj (e : O ≃ C) (x : C) :
    let _ : EnrichedCategory V O := reindex V e
    (reindexInverse V e).obj x = e.symm x := rfl

/-- Every full inverse Hom map uses precisely the true two object equations. -/
theorem reindexInverse_map (e : O ≃ C) (x y : C) :
    let _ : EnrichedCategory V O := reindex V e
    (reindexInverse V e).map x y = eqToHom (congrArg₂ (fun a b : C => a ⟶[V] b)
      (e.apply_symm_apply x).symm (e.apply_symm_apply y).symm) := rfl

/-- The SAME entire original projection followed by its inverse is the whole reindexed identity. -/
theorem reindexProjection_inverse (e : O ≃ C) :
    let _ : EnrichedCategory V O := reindex V e
    (reindexProjection V e).comp V (reindexInverse V e) = EnrichedFunctor.id V O := by
  let _ : EnrichedCategory V O := reindex V e
  apply EnrichedFunctor.ext V
    (F := (reindexProjection V e).comp V (reindexInverse V e))
    (G := EnrichedFunctor.id V O) (fun x => e.symm_apply_apply x)
  intro x y
  let h₁ := congrArg₂ (fun a b : C => a ⟶[V] b)
    (e.apply_symm_apply (e x)).symm (e.apply_symm_apply (e y)).symm
  let h₂ := congrArg₂ (fun a b : C => a ⟶[V] b)
    (congrArg e (e.symm_apply_apply x)) (congrArg e (e.symm_apply_apply y))
  change (𝟙 (e x ⟶[V] e y) ≫ eqToHom h₁) ≫ eqToHom h₂ = 𝟙 (e x ⟶[V] e y)
  rw [Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- The SAME entire inverse followed by the original projection is the whole original identity. -/
theorem reindexInverse_projection (e : O ≃ C) :
    let _ : EnrichedCategory V O := reindex V e
    (reindexInverse V e).comp V (reindexProjection V e) = EnrichedFunctor.id V C := by
  let _ : EnrichedCategory V O := reindex V e
  apply EnrichedFunctor.ext V
    (F := (reindexInverse V e).comp V (reindexProjection V e))
    (G := EnrichedFunctor.id V C) (fun x => e.apply_symm_apply x)
  intro x y
  let h₁ := congrArg₂ (fun a b : C => a ⟶[V] b)
    (e.apply_symm_apply x).symm (e.apply_symm_apply y).symm
  let h₂ := congrArg₂ (fun a b : C => a ⟶[V] b)
    (e.apply_symm_apply x) (e.apply_symm_apply y)
  change (eqToHom h₁ ≫ 𝟙 (e (e.symm x) ⟶[V] e (e.symm y))) ≫ eqToHom h₂ = 𝟙 (x ⟶[V] y)
  rw [Category.comp_id, eqToHom_trans, eqToHom_refl]

end CategoryTheory.EnrichedCategory
