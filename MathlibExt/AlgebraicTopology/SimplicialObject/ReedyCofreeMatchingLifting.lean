/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyCofreeMatchingLabels
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.LiftingProperties.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Actual original cofree relative-matching lifting

Every nonsurjective original ordinal coordinate is prescribed by the
same proper-face matching data and its actual original image. The
remaining coordinates lift individually against the same coefficient
trivial fibration. Full product, matching and pullback equations retain
all original maps; no component-class certificate is an input.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.CofreeMatching

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- Hom-sets of `SimplexCategoryᵒᵖ` are finite, so the products defining the cofree simplicial
objects exist in a category with finite limits. -/
local instance : ∀ a b : SimplexCategoryᵒᵖ, HasProductsOfShape (a ⟶ b) C :=
  fun a b => by
    let _ : Finite (a ⟶ b) :=
      Finite.of_equiv (b.unop ⟶ a.unop) (CategoryTheory.opEquiv a b).symm
    infer_instance

/-- The actual original evaluation right adjoint at the supplied scalar degree. -/
abbrev cofree (n : ℕ) : C ⥤ SimplicialObject C := evaluationRightAdjoint C (op ⦋n⦌)

private def projection (n : ℕ) (A : C) (a : SimplexCategoryᵒᵖ) (θ : a ⟶ op ⦋n⦌) :
    ((cofree n).obj A).obj a ⟶ A := Pi.π (fun _ : a ⟶ op ⦋n⦌ => A) θ

private def liftCoefficients (n : ℕ) (A : C) (a : SimplexCategoryᵒᵖ) {V : C}
    (f : (θ : a ⟶ op ⦋n⦌) → (V ⟶ A)) : V ⟶ ((cofree n).obj A).obj a := Pi.lift f

private theorem liftCoefficients_projection (n : ℕ) (A : C) (a : SimplexCategoryᵒᵖ) {V : C}
    (f : (θ : a ⟶ op ⦋n⦌) → (V ⟶ A)) (θ : a ⟶ op ⦋n⦌) :
    liftCoefficients n A a f ≫ projection n A a θ = f θ := limit.lift_π _ _

private theorem projection_hom_ext (n : ℕ) (A : C) (a : SimplexCategoryᵒᵖ) {V : C}
    {f g : V ⟶ ((cofree n).obj A).obj a}
    (h : ∀ θ, f ≫ projection n A a θ = g ≫ projection n A a θ) : f = g :=
  Pi.hom_ext f g h

private theorem cofree_structure_π (n : ℕ) (A : C)
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) (θ : b ⟶ op ⦋n⦌) :
    ((cofree n).obj A).map f ≫ projection n A (b) θ =
      projection n A (a) (f ≫ θ) :=
  limit.lift_π _ _

private theorem cofree_coefficient_π (n : ℕ) {A B : C} (p : A ⟶ B)
    (a : SimplexCategoryᵒᵖ) (θ : a ⟶ op ⦋n⦌) :
    ((cofree n).map p).app a ≫ projection n B (a) θ =
      projection n A (a) θ ≫ p :=
  limit.lift_π _ _

private theorem cofree_matching_projection (n m : ℕ) (A : C) (a : matchingIndex m)
    (r : a.obj.right ⟶ op ⦋n⦌) :
    matchingMap ((cofree n).obj A) m ≫ matchingπ ((cofree n).obj A) m a ≫
      projection n A a.obj.right r = projection n A (op ⦋m⦌) (a.obj.hom ≫ r) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ projection n A a.obj.right r)
      (matchingMap_π ((cofree n).obj A) m a)).trans (cofree_structure_π n A a.obj.hom r))

private def matchingCoordinate {n m : ℕ} {A : C}
    (b : C) (d : b ⟶ matchingObject ((cofree (C := C) n).obj A) m)
    (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : ¬ Epi θ) : b ⟶ A :=
  d ≫ matchingπ ((cofree n).obj A) m (imageMatchingIndex θ hθ) ≫
    projection n A (imageMatchingIndex θ hθ).obj.right (factorThruImage θ).op

private theorem matchingCoordinate_factor {n m : ℕ} {A : C}
    (b : C) (d : b ⟶ matchingObject ((cofree (C := C) n).obj A) m)
    (a : matchingIndex m) (r : ⦋n⦌ ⟶ a.obj.right.unop) :
    matchingCoordinate b d (r ≫ a.obj.hom.unop) (by
      intro he
      let _ : Epi (r ≫ a.obj.hom.unop) := he
      let _ : Epi a.obj.hom.unop := epi_of_epi r a.obj.hom.unop
      have hl := SimplexCategory.len_le_of_epi a.obj.hom.unop
      exact (Nat.not_le_of_lt a.property.2) hl) =
        d ≫ matchingπ ((cofree n).obj A) m a ≫
          projection n A (a.obj.right) r.op := by
  let θ := r ≫ a.obj.hom.unop
  have hθ : ¬ Epi θ := by
    intro he
    let _ : Epi θ := he
    let _ : Epi a.obj.hom.unop := epi_of_epi r a.obj.hom.unop
    exact (Nat.not_le_of_lt a.property.2) (SimplexCategory.len_le_of_epi a.obj.hom.unop)
  let g := imageToFactor θ hθ a r rfl
  have hd := congrArg (fun f => d ≫ f) (limit.w (matchingDiagram ((cofree n).obj A) m) g)
  have hr : factorThruImage θ ≫ g.hom.right.unop = r := image.fac_lift _
  have hπ := congrArg (fun f => f ≫ projection n A (op (image θ)) (factorThruImage θ).op) hd
  change (d ≫ matchingπ ((cofree n).obj A) m a ≫ ((cofree n).obj A).map g.hom.right) ≫
    projection n A (imageMatchingIndex θ hθ).obj.right (factorThruImage θ).op =
      (d ≫ matchingπ ((cofree n).obj A) m (imageMatchingIndex θ hθ)) ≫
        projection n A (imageMatchingIndex θ hθ).obj.right (factorThruImage θ).op at hπ
  simp only [Category.assoc, cofree_structure_π] at hπ
  have hro : g.hom.right ≫ (factorThruImage θ).op = r.op := by
    apply Quiver.Hom.unop_inj
    exact hr
  rw [hro] at hπ
  exact hπ.symm

variable [ModelCategory C]

/-- Every original coefficient trivial fibration gives the actual full Reedy cofree relative
matching right class. -/
theorem cofreeMap_reedy_trivialFibration {A B : C} (p : A ⟶ B)
    (hp : trivialFibrations C p) (n : ℕ) :
    reedyRight (trivialFibrations C) ((cofree n).map p) := by
  classical
  intro m
  rw [← cofibrations_rlp]
  intro U V i hi
  let f := (cofree (C := C) n).map p
  let X := (cofree (C := C) n).obj A
  let Y := (cofree (C := C) n).obj B
  refine ⟨fun {top bottom} sq => ?_⟩
  let b0 := bottom ≫ pullback.fst (matchingMap Y m) ((matchingObjectFunctor m).map f)
  let b1 := bottom ≫ pullback.snd (matchingMap Y m) ((matchingObjectFunctor m).map f)
  have coordinateSquare (θ : ⦋n⦌ ⟶ ⦋m⦌) :
      CommSq (top ≫ projection n A (op ⦋m⦌) θ.op) i p
        (b0 ≫ projection n B (op ⦋m⦌) θ.op) := by
    have h := congrArg
      (fun t => t ≫ pullback.fst (matchingMap Y m) ((matchingObjectFunctor m).map f)) sq.w
    rw [Category.assoc, relativeMatchingMap_fst] at h
    have hπ := congrArg (fun t => t ≫ projection n B (op ⦋m⦌) θ.op) h
    simp only [Category.assoc, cofree_coefficient_π] at hπ
    constructor
    simpa only [Category.assoc, b0] using hπ
  let _ : HasLiftingProperty i p := hasLiftingProperty_of_wfs i p hi hp
  let coordinate (θ : ⦋n⦌ ⟶ ⦋m⦌) : V ⟶ A :=
    if hθ : Epi θ then (coordinateSquare θ).lift else matchingCoordinate V b1 θ hθ
  let lift : V ⟶ X.obj (op ⦋m⦌) := liftCoefficients n A (op ⦋m⦌) (fun θ => coordinate θ.unop)
  have lift_projection (θ : op ⦋m⦌ ⟶ op ⦋n⦌) :
      lift ≫ projection n A (op ⦋m⦌) θ = coordinate θ.unop :=
    liftCoefficients_projection n A (op ⦋m⦌) _ θ
  apply CommSq.HasLift.mk'
  refine ⟨lift, ?_, ?_⟩
  · apply projection_hom_ext n A (op ⦋m⦌)
    intro θ
    rw [Category.assoc, lift_projection]
    by_cases hθ : Epi θ.unop
    · dsimp only [coordinate]
      rw [dite_eq_left hθ]
      exact (coordinateSquare θ.unop).fac_left
    · dsimp only [coordinate]
      rw [dite_eq_right hθ]
      have hb := congrArg
        (fun t => t ≫ pullback.snd (matchingMap Y m) ((matchingObjectFunctor m).map f)) sq.w
      rw [Category.assoc, relativeMatchingMap_snd] at hb
      have hπ := congrArg
        (fun t => t ≫ matchingπ ((cofree n).obj A) m (imageMatchingIndex θ.unop hθ) ≫
          projection n A (imageMatchingIndex θ.unop hθ).obj.right (factorThruImage θ.unop).op) hb
      have he := cofree_matching_projection n m A (imageMatchingIndex θ.unop hθ)
        (factorThruImage θ.unop).op
      have hf : (image.ι θ.unop).op ≫ (factorThruImage θ.unop).op = θ := by
        apply Quiver.Hom.unop_inj
        exact image.fac θ.unop
      have he' : top ≫ matchingMap ((cofree n).obj A) m ≫
          matchingπ ((cofree n).obj A) m (imageMatchingIndex θ.unop hθ) ≫
            projection n A (imageMatchingIndex θ.unop hθ).obj.right (factorThruImage θ.unop).op =
              top ≫ projection n A (op ⦋m⦌) θ := by
        exact congrArg (fun f => top ≫ f)
          (he.trans (congrArg (projection n A (op ⦋m⦌)) hf))
      have hπ' : top ≫ projection n A (op ⦋m⦌) θ = i ≫ matchingCoordinate V b1 θ.unop hθ := by
        have hnorm : top ≫ matchingMap ((cofree n).obj A) m ≫
            matchingπ ((cofree n).obj A) m (imageMatchingIndex θ.unop hθ) ≫
              projection n A (imageMatchingIndex θ.unop hθ).obj.right (factorThruImage θ.unop).op =
                i ≫ matchingCoordinate V b1 θ.unop hθ := by
          simpa only [Category.assoc, matchingCoordinate, b1] using hπ
        exact he'.symm.trans hnorm
      exact hπ'.symm
  · apply pullback.hom_ext
    · apply projection_hom_ext n B (op ⦋m⦌)
      intro θ
      have hleft : ((lift ≫ relativeMatchingMap f m) ≫
          pullback.fst (matchingMap Y m) ((matchingObjectFunctor m).map f)) ≫
            projection n B (op ⦋m⦌) θ =
              coordinate θ.unop ≫ p := by
        have he := congrArg (fun t => lift ≫ t ≫ projection n B (op ⦋m⦌) θ)
          (relativeMatchingMap_fst f m)
        have hp' := congrArg (fun t => lift ≫ t) (cofree_coefficient_π n p (op ⦋m⦌) θ)
        have hl' := congrArg (fun t => t ≫ p) (lift_projection θ)
        have he' : ((lift ≫ relativeMatchingMap f m) ≫
            pullback.fst (matchingMap Y m) ((matchingObjectFunctor m).map f)) ≫
              projection n B (op ⦋m⦌) θ =
                lift ≫ f.app (op ⦋m⦌) ≫ projection n B (op ⦋m⦌) θ := by
          simpa only [Category.assoc] using he
        have hp'' : lift ≫ f.app (op ⦋m⦌) ≫ projection n B (op ⦋m⦌) θ =
            (lift ≫ projection n A (op ⦋m⦌) θ) ≫ p := by
          simpa only [Category.assoc, f] using hp'
        exact he'.trans (hp''.trans hl')
      apply hleft.trans
      change coordinate θ.unop ≫ p = b0 ≫ projection n B (op ⦋m⦌) θ
      by_cases hθ : Epi θ.unop
      · dsimp only [coordinate]
        rw [dite_eq_left hθ]
        exact (coordinateSquare θ.unop).fac_right
      · dsimp only [coordinate]
        rw [dite_eq_right hθ]
        have hb := congrArg (fun t => bottom ≫ t) (pullback.condition
          (f := matchingMap Y m) (g := (matchingObjectFunctor m).map f))
        let a := imageMatchingIndex θ.unop hθ
        let r := (factorThruImage θ.unop).op
        have he := cofree_matching_projection n m B a r
        have hf : a.obj.hom ≫ r = θ := by
          apply Quiver.Hom.unop_inj
          exact image.fac θ.unop
        have hπ := congrArg
          (fun t => t ≫ matchingπ ((cofree n).obj B) m a ≫ projection n B a.obj.right r) hb
        have hL : b0 ≫ matchingMap ((cofree n).obj B) m ≫ matchingπ ((cofree n).obj B) m a ≫
            projection n B a.obj.right r = b0 ≫ projection n B (op ⦋m⦌) θ :=
          congrArg (fun t => b0 ≫ t) (he.trans (congrArg (projection n B (op ⦋m⦌)) hf))
        have hR : b1 ≫ (matchingObjectFunctor m).map f ≫ matchingπ ((cofree n).obj B) m a ≫
            projection n B a.obj.right r = matchingCoordinate V b1 θ.unop hθ ≫ p := by
          have hm' := matchingObjectFunctor_map_π m f a
          have hp' := cofree_coefficient_π n p a.obj.right r
          have he' : (matchingObjectFunctor m).map f ≫ matchingπ ((cofree n).obj B) m a ≫
              projection n B a.obj.right r =
                matchingπ ((cofree n).obj A) m a ≫ projection n A a.obj.right r ≫ p :=
            (Category.assoc _ _ _).symm.trans
              ((congrArg (fun t => t ≫ projection n B a.obj.right r) hm').trans
                ((Category.assoc _ _ _).trans
                  (congrArg (fun t => matchingπ ((cofree n).obj A) m a ≫ t) hp')))
          simpa only [Category.assoc, matchingCoordinate, a, r] using congrArg (fun t => b1 ≫ t) he'
        have heq : b0 ≫ matchingMap ((cofree n).obj B) m ≫ matchingπ ((cofree n).obj B) m a ≫
            projection n B a.obj.right r = b1 ≫ (matchingObjectFunctor m).map f ≫
              matchingπ ((cofree n).obj B) m a ≫ projection n B a.obj.right r := by
          simpa only [Category.assoc, b0, b1, Y] using hπ
        exact (hR.symm.trans (heq.symm.trans hL))
    · apply limit.hom_ext
      intro a
      apply projection_hom_ext n A a.obj.right
      intro r
      have hleft : (((lift ≫ relativeMatchingMap f m) ≫
          pullback.snd (matchingMap Y m) ((matchingObjectFunctor m).map f)) ≫
            matchingπ ((cofree n).obj A) m a) ≫ projection n A a.obj.right r =
              coordinate (a.obj.hom ≫ r).unop := by
        have he := congrArg
          (fun t => lift ≫ t ≫ matchingπ ((cofree n).obj A) m a ≫ projection n A a.obj.right r)
          (relativeMatchingMap_snd f m)
        have hm' := congrArg (fun t => lift ≫ t) (cofree_matching_projection n m A a r)
        have he' : (((lift ≫ relativeMatchingMap f m) ≫
            pullback.snd (matchingMap Y m) ((matchingObjectFunctor m).map f)) ≫
              matchingπ ((cofree n).obj A) m a) ≫ projection n A a.obj.right r =
                lift ≫ matchingMap ((cofree n).obj A) m ≫ matchingπ ((cofree n).obj A) m a ≫
                  projection n A a.obj.right r := by
          simpa only [Category.assoc] using he
        exact he'.trans (hm'.trans (lift_projection (a.obj.hom ≫ r)))
      apply hleft.trans
      have hn : ¬ Epi (r.unop ≫ a.obj.hom.unop) := by
        intro h
        let _ : Epi (r.unop ≫ a.obj.hom.unop) := h
        let _ : Epi a.obj.hom.unop := epi_of_epi r.unop a.obj.hom.unop
        exact (Nat.not_le_of_lt a.property.2) (SimplexCategory.len_le_of_epi a.obj.hom.unop)
      dsimp only [coordinate]
      have hn' : ¬ Epi (a.obj.hom ≫ r).unop := by
        simpa only [unop_comp] using hn
      rw [dite_eq_right hn']
      have hfac : matchingCoordinate V b1 (a.obj.hom ≫ r).unop hn' =
          b1 ≫ matchingπ ((cofree n).obj A) m a ≫ projection n A a.obj.right r := by
        simpa only [unop_comp, Quiver.Hom.op_unop] using matchingCoordinate_factor V b1 a r.unop
      have hnorm : b1 ≫ matchingπ ((cofree n).obj A) m a ≫ projection n A a.obj.right r =
          (b1 ≫ matchingπ ((cofree n).obj A) m a) ≫ projection n A a.obj.right r :=
        (Category.assoc _ _ _).symm
      exact hfac.trans hnorm

end CategoryTheory.SimplicialObject.CofreeMatching
