/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Actual extra degeneracies on a whole augmented diagram at a fixed point

Pull back the original whole augmentation along a prescribed coefficient
map. Every extra degeneracy retains its original first leg and the same
prescribed base leg. All required equations are proved on both original
pullback projections. No contraction or compatibility outcome is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (A : SimplicialObject.Augmented C)
  {P : C} (p : P ⟶ A.right)

/-- The original whole augmented diagram pulled back along the same prescribed coefficient map. -/
def baseChange : SimplicialObject.Augmented C where
  left := pullback A.hom ((SimplicialObject.const C).map p)
  right := P
  hom := pullback.snd A.hom ((SimplicialObject.const C).map p)

/-- The whole original pullback leg of the fixed-base augmented diagram. -/
def baseChangeToOriginal : (baseChange A p).left ⟶ A.left :=
  pullback.fst A.hom ((SimplicialObject.const C).map p)

variable {A} (ed : A.ExtraDegeneracy)

omit [HasPullbacks C] in
/-- Every actual extra degeneracy retains the whole original augmentation. -/
theorem s_comp_augmentation (n : ℕ) :
    ed.s n ≫ A.hom.app (op (SimplexCategory.mk (n + 1))) =
      A.hom.app (op (SimplexCategory.mk n)) := by
  have h := A.hom.naturality (SimplexCategory.δ (0 : Fin (n + 2))).op
  change A.left.δ (0 : Fin (n + 2)) ≫ A.hom.app (op (SimplexCategory.mk n)) =
    A.hom.app (op (SimplexCategory.mk (n + 1))) ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  rw [← h, ← Category.assoc, ed.s_comp_δ₀, Category.id_comp]

/-- Evaluation retains the same original coefficient pullback in every fixed-base degree. -/
def baseChangeRowIso (n : ℕ) :
    (baseChange A p).left.obj (op (SimplexCategory.mk n)) ≅
      pullback (A.hom.app (op (SimplexCategory.mk n))) p :=
  ((IsPullback.of_hasPullback A.hom ((SimplicialObject.const C).map p)).map
    ((evaluation SimplexCategoryᵒᵖ C).obj (op (SimplexCategory.mk n)))).isoPullback

/-- The original inverse row comparison keeps its full evaluated first leg. -/
theorem baseChangeRowIso_inv_fst (n : ℕ) :
    (baseChangeRowIso (A := A) p n).inv ≫
      (baseChangeToOriginal A p).app (op (SimplexCategory.mk n)) = pullback.fst _ _ :=
  ((IsPullback.of_hasPullback A.hom ((SimplicialObject.const C).map p)).map
    ((evaluation SimplexCategoryᵒᵖ C).obj (op (SimplexCategory.mk n)))).isoPullback_inv_fst

/-- The original inverse row comparison keeps its full evaluated same-base leg. -/
theorem baseChangeRowIso_inv_snd (n : ℕ) :
    (baseChangeRowIso (A := A) p n).inv ≫
      (baseChange A p).hom.app (op (SimplexCategory.mk n)) = pullback.snd _ _ :=
  ((IsPullback.of_hasPullback A.hom ((SimplicialObject.const C).map p)).map
    ((evaluation SimplexCategoryᵒᵖ C).obj (op (SimplexCategory.mk n)))).isoPullback_inv_snd

/-- The original forward row comparison keeps its full first pullback leg. -/
theorem baseChangeRowIso_hom_fst (n : ℕ) :
    (baseChangeRowIso (A := A) p n).hom ≫ pullback.fst _ _ =
      (baseChangeToOriginal A p).app (op (SimplexCategory.mk n)) :=
  ((IsPullback.of_hasPullback A.hom ((SimplicialObject.const C).map p)).map
    ((evaluation SimplexCategoryᵒᵖ C).obj (op (SimplexCategory.mk n)))).isoPullback_hom_fst

/-- The original forward row comparison keeps its full same-base pullback leg. -/
theorem baseChangeRowIso_hom_snd (n : ℕ) :
    (baseChangeRowIso (A := A) p n).hom ≫ pullback.snd _ _ =
      (baseChange A p).hom.app (op (SimplexCategory.mk n)) :=
  ((IsPullback.of_hasPullback A.hom ((SimplicialObject.const C).map p)).map
    ((evaluation SimplexCategoryᵒᵖ C).obj (op (SimplexCategory.mk n)))).isoPullback_hom_snd

set_option backward.isDefEq.respectTransparency false in
/-- The actual original extra degeneracy on the same fixed-base row. -/
def baseChangeExtraMap (n : ℕ) :
    (baseChange A p).left.obj (op (SimplexCategory.mk n)) ⟶
      (baseChange A p).left.obj (op (SimplexCategory.mk (n + 1))) :=
  (baseChangeRowIso (A := A) p n).hom ≫
    pullback.map (A.hom.app (op (SimplexCategory.mk n))) p
      (A.hom.app (op (SimplexCategory.mk (n + 1)))) p
      (ed.s n) (𝟙 P) (𝟙 A.right)
      (by
        exact (Category.comp_id (A.hom.app (op (SimplexCategory.mk n)))).trans
          (s_comp_augmentation ed n).symm)
      (by simp) ≫ (baseChangeRowIso (A := A) p (n + 1)).inv

set_option backward.isDefEq.respectTransparency false in
/-- Every induced fixed-base extra map retains its whole original extra-degeneracy leg. -/
theorem baseChangeExtraMap_fst (n : ℕ) :
    baseChangeExtraMap (ed := ed) (p := p) n ≫
      (baseChangeToOriginal A p).app (op (SimplexCategory.mk (n + 1))) =
      (baseChangeToOriginal A p).app (op (SimplexCategory.mk n)) ≫ ed.s n := by
  unfold baseChangeExtraMap
  rw [Category.assoc, Category.assoc, baseChangeRowIso_inv_fst, pullback.map, pullback.lift_fst,
    ← Category.assoc, baseChangeRowIso_hom_fst]

set_option backward.isDefEq.respectTransparency false in
/-- Every induced fixed-base extra map retains its same original base projection. -/
theorem baseChangeExtraMap_snd (n : ℕ) :
    baseChangeExtraMap (ed := ed) (p := p) n ≫
      (baseChange A p).hom.app (op (SimplexCategory.mk (n + 1))) =
      (baseChange A p).hom.app (op (SimplexCategory.mk n)) := by
  unfold baseChangeExtraMap
  rw [Category.assoc, Category.assoc, baseChangeRowIso_inv_snd, pullback.map, pullback.lift_snd,
    Category.comp_id, baseChangeRowIso_hom_snd]

/-- The actual original fixed-base augmentation section keeps its prescribed coefficient map. -/
def baseChangeSection : P ⟶ (baseChange A p).left.obj (op (SimplexCategory.mk 0)) :=
  pullback.lift (p ≫ ed.s') (𝟙 P)
    (by rw [Category.assoc, ed.s'_comp_ε, Category.comp_id, Category.id_comp]) ≫
      (baseChangeRowIso (A := A) p 0).inv

/-- Both original evaluated pullback legs detect every whole fixed-base row map. -/
theorem baseChange_hom_ext (n : ℕ) {Z : C}
    (f g : Z ⟶ (baseChange A p).left.obj (op (SimplexCategory.mk n)))
    (hf : f ≫ (baseChangeToOriginal A p).app (op (SimplexCategory.mk n)) =
      g ≫ (baseChangeToOriginal A p).app (op (SimplexCategory.mk n)))
    (hg : f ≫ (baseChange A p).hom.app (op (SimplexCategory.mk n)) =
      g ≫ (baseChange A p).hom.app (op (SimplexCategory.mk n))) : f = g :=
  ((IsPullback.of_hasPullback A.hom ((SimplicialObject.const C).map p)).map
    ((evaluation SimplexCategoryᵒᵖ C).obj (op (SimplexCategory.mk n)))).hom_ext hf hg

set_option backward.isDefEq.respectTransparency false in
/-- The induced original augmentation section retains its same original extra section. -/
theorem baseChangeSection_fst :
    baseChangeSection (ed := ed) (p := p) ≫
      (baseChangeToOriginal A p).app (op (SimplexCategory.mk 0)) = p ≫ ed.s' := by
  unfold baseChangeSection
  rw [Category.assoc, baseChangeRowIso_inv_fst, pullback.lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- The induced original augmentation section retains the same prescribed base as identity. -/
theorem baseChangeSection_snd :
    baseChangeSection (ed := ed) (p := p) ≫
      (baseChange A p).hom.app (op (SimplexCategory.mk 0)) = 𝟙 P := by
  unfold baseChangeSection
  rw [Category.assoc, baseChangeRowIso_inv_snd, pullback.lift_snd]

/-- Every original face retains the fixed-base first pullback projection. -/
theorem baseChange_delta_fst (n : ℕ) (i : Fin (n + 2)) :
    (baseChange A p).left.δ i ≫ (baseChangeToOriginal A p).app (op (SimplexCategory.mk n)) =
      (baseChangeToOriginal A p).app (op (SimplexCategory.mk (n + 1))) ≫ A.left.δ i :=
  (baseChangeToOriginal A p).naturality (SimplexCategory.δ i).op

/-- Every original face retains the same fixed-base coefficient projection. -/
theorem baseChange_delta_snd (n : ℕ) (i : Fin (n + 2)) :
    (baseChange A p).left.δ i ≫ (baseChange A p).hom.app (op (SimplexCategory.mk n)) =
      (baseChange A p).hom.app (op (SimplexCategory.mk (n + 1))) := by
  have h := (baseChange A p).hom.naturality (SimplexCategory.δ i).op
  exact h.trans (Category.comp_id _)

/-- Every original degeneracy retains the fixed-base first pullback projection. -/
theorem baseChange_sigma_fst (n : ℕ) (i : Fin (n + 1)) :
    (baseChange A p).left.σ i ≫ (baseChangeToOriginal A p).app (op (SimplexCategory.mk (n + 1))) =
      (baseChangeToOriginal A p).app (op (SimplexCategory.mk n)) ≫ A.left.σ i :=
  (baseChangeToOriginal A p).naturality (SimplexCategory.σ i).op

/-- Every original degeneracy retains the same fixed-base coefficient projection. -/
theorem baseChange_sigma_snd (n : ℕ) (i : Fin (n + 1)) :
    (baseChange A p).left.σ i ≫ (baseChange A p).hom.app (op (SimplexCategory.mk (n + 1))) =
      (baseChange A p).hom.app (op (SimplexCategory.mk n)) := by
  have h := (baseChange A p).hom.naturality (SimplexCategory.σ i).op
  exact h.trans (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
/-- The whole original fixed-base pullback has the actual induced extra degeneracy. -/
def baseChangeExtraDegeneracy : (baseChange A p).ExtraDegeneracy where
  s' := baseChangeSection (ed := ed) (p := p)
  s n := baseChangeExtraMap (ed := ed) (p := p) n
  s'_comp_ε := baseChangeSection_snd (ed := ed) (p := p)
  s₀_comp_δ₁ := by
    apply baseChange_hom_ext (A := A) p 0
    · rw [Category.assoc, baseChange_delta_fst, ← Category.assoc,
        baseChangeExtraMap_fst, Category.assoc, ed.s₀_comp_δ₁, ← Category.assoc]
      have hc := congrArg (fun h => h.app (op (SimplexCategory.mk 0)))
        (pullback.condition (f := A.hom) (g := (SimplicialObject.const C).map p))
      change (baseChangeToOriginal A p).app (op (SimplexCategory.mk 0)) ≫
          A.hom.app (op (SimplexCategory.mk 0)) =
        (baseChange A p).hom.app (op (SimplexCategory.mk 0)) ≫ p at hc
      rw [hc]
      simp only [Category.assoc]
      rw [baseChangeSection_fst]
    · rw [Category.assoc, baseChange_delta_snd, baseChangeExtraMap_snd,
        Category.assoc, baseChangeSection_snd, Category.comp_id]
  s_comp_δ₀ n := by
    apply baseChange_hom_ext (A := A) p n
    · rw [Category.assoc, baseChange_delta_fst, ← Category.assoc,
        baseChangeExtraMap_fst, Category.assoc, ed.s_comp_δ₀, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, baseChange_delta_snd, baseChangeExtraMap_snd, Category.id_comp]
  s_comp_δ n i := by
    apply baseChange_hom_ext (A := A) p (n + 1)
    · rw [Category.assoc, baseChange_delta_fst, ← Category.assoc,
        baseChangeExtraMap_fst, Category.assoc, ed.s_comp_δ,
        ← Category.assoc, ← baseChange_delta_fst]
      simp only [Category.assoc]
      rw [baseChangeExtraMap_fst]
    · rw [Category.assoc, baseChange_delta_snd, baseChangeExtraMap_snd,
        Category.assoc, baseChangeExtraMap_snd, baseChange_delta_snd]
  s_comp_σ n i := by
    apply baseChange_hom_ext (A := A) p (n + 2)
    · rw [Category.assoc, baseChange_sigma_fst, ← Category.assoc,
        baseChangeExtraMap_fst, Category.assoc, ed.s_comp_σ,
        ← Category.assoc, ← baseChange_sigma_fst]
      simp only [Category.assoc]
      rw [baseChangeExtraMap_fst]
    · rw [Category.assoc, baseChange_sigma_snd, baseChangeExtraMap_snd,
        Category.assoc, baseChangeExtraMap_snd, baseChange_sigma_snd]

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy
