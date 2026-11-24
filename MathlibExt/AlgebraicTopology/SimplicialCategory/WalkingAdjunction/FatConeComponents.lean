/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeFunctoriality
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Actual component normal forms of the fat cone

In each original simplicial degree, collapsing the entire final
cylinder row leaves the original coefficient paired with a
nonfinal interval simplex, or the original apex simplex. The native
Type pushout universal property proves this component isomorphism.
This is a description of actual components, not a simplicial nerve
identification or a replacement of the original cylinder maps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- An original interval simplex not entirely in the collapsed final row. -/
abbrev NonTopTime (n : ℕ) : Type u :=
  {t : (Δ[1] : SSet.{u}) _⦋n⦌ // t ≠ SSet.stdSimplex.const 1 1 _}

/-- The complete coefficient and nonfinal time, or the original apex simplex. -/
abbrev Component (X : SSet.{u}) (n : ℕ) : Type u :=
  (X _⦋n⦌ × NonTopTime.{u} n) ⊕ (Δ[0] : SSet.{u}) _⦋n⦌

/-- Classify the entire original cylinder simplex, collapsing exactly the final-row simplices. -/
def classifyCylinder (X : SSet.{u}) (n : ℕ) (s : (X ⊗ (Δ[1] : SSet.{u})) _⦋n⦌) : Component X n :=
  if h : s.2 = SSet.stdSimplex.const 1 1 _ then
    Sum.inr ((SSet.stdSimplex.isTerminalObj₀.from X).app _ s.1)
  else Sum.inl (s.1, ⟨s.2, h⟩)

/-- The full original one endpoint has precisely the final-row time simplex. -/
theorem one_time (X : SSet.{u}) (n : ℕ) (x : X _⦋n⦌) :
    ((one X).app _ x).2 = SSet.stdSimplex.const 1 1 _ := by
  apply SSet.stdSimplex.ext
  intro i
  rfl

/-- The original final-row classification is the original terminal map followed by apex inclusion. -/
theorem classifyCylinder_one (X : SSet.{u}) (n : ℕ) (x : X _⦋n⦌) :
    classifyCylinder X n ((one X).app _ x) = Sum.inr ((SSet.stdSimplex.isTerminalObj₀.from X).app _ x) := by
  have he : (one X).app _ x = (x, SSet.stdSimplex.const 1 1 _) :=
    Prod.ext rfl (one_time X n x)
  rw [he]
  change (if h : SSet.stdSimplex.const 1 1 (op ⦋n⦌) = SSet.stdSimplex.const 1 1 (op ⦋n⦌) then
    Sum.inr ((SSet.stdSimplex.isTerminalObj₀.from X).app _ x) else _) = _
  exact dite_eq_left rfl

/-- The actual component pushout cocone with the complete nonfinal coefficient and original apex. -/
abbrev componentCocone (X : SSet.{u}) (n : ℕ) :
    PushoutCocone ((one X).app (op ⦋n⦌)) ((SSet.stdSimplex.isTerminalObj₀.from X).app (op ⦋n⦌)) :=
  PushoutCocone.mk (↾(classifyCylinder X n)) (↾(Sum.inr : (Δ[0] : SSet.{u}) _⦋n⦌ → Component X n))
    (by
      apply ConcreteCategory.hom_ext
      intro x
      exact classifyCylinder_one X n x)

/-- The component classification has its genuine full Type pushout universal property. -/
def componentIsColimit (X : SSet.{u}) (n : ℕ) : IsColimit (componentCocone X n) := by
  classical
  apply PushoutCocone.isColimitAux'
  intro s
  let d : Component X n ⟶ s.pt := ↾fun a =>
    match a with
    | Sum.inl (x, t) => s.inl (x, t.1)
    | Sum.inr z => s.inr z
  have hl : (componentCocone X n).inl ≫ d = s.inl := by
    apply ConcreteCategory.hom_ext
    intro a
    rcases a with ⟨x, t⟩
    change d (if h : t = SSet.stdSimplex.const 1 1 (op ⦋n⦌) then
      Sum.inr ((SSet.stdSimplex.isTerminalObj₀.from X).app _ x) else Sum.inl (x, ⟨t, h⟩)) = s.inl (x, t)
    by_cases ha : t = SSet.stdSimplex.const 1 1 (op ⦋n⦌)
    · rw [dite_eq_left ha]
      have he : (x, t) = (one X).app _ x := by
        apply Prod.ext
        · rfl
        · exact ha.trans (one_time X n x).symm
      have h := ConcreteCategory.congr_hom s.condition x
      exact h.symm.trans (congrArg (fun b => s.inl b) he.symm)
    · rw [dite_eq_right ha]
      rfl
  have hr : (componentCocone X n).inr ≫ d = s.inr := by
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  refine ⟨d, hl, hr, ?_⟩
  intro m hm₁ hm₂
  apply ConcreteCategory.hom_ext
  intro a
  cases a with
  | inl a =>
      rcases a with ⟨x, t⟩
      have h := ConcreteCategory.congr_hom hm₁ (show (X ⊗ (Δ[1] : SSet.{u})) _⦋n⦌ from (x, t.1))
      change m (if ht : t.1 = SSet.stdSimplex.const 1 1 (op ⦋n⦌) then
        Sum.inr ((SSet.stdSimplex.isTerminalObj₀.from X).app _ x) else Sum.inl (x, ⟨t.1, ht⟩)) =
          s.inl (x, t.1) at h
      rw [dite_eq_right t.2] at h
      exact h
  | inr z => exact ConcreteCategory.congr_hom hm₂ z

/-- Evaluation of the actual fat-cone pushout is the original component pushout. -/
theorem componentPushout (X : SSet.{u}) (n : ℕ) :
    IsPushout ((one X).app (op ⦋n⦌)) ((SSet.stdSimplex.isTerminalObj₀.from X).app (op ⦋n⦌))
      ((cylinder X).app (op ⦋n⦌)) ((apex X).app (op ⦋n⦌)) :=
  (IsPushout.of_hasPushout (one X) (SSet.stdSimplex.isTerminalObj₀.from X)).map
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌))

/-- The derived actual isomorphism of each full fat-cone component with its coefficient/apex normal forms. -/
def componentIso (X : SSet.{u}) (n : ℕ) : (obj X) _⦋n⦌ ≅ Component X n :=
  (componentPushout X n).isoIsPushout _ _ (IsPushout.of_isColimit (componentIsColimit X n))

/-- Reading the whole cylinder through the component isomorphism is its identical original classification. -/
theorem cylinder_componentIso (X : SSet.{u}) (n : ℕ) :
    (cylinder X).app (op ⦋n⦌) ≫ (componentIso X n).hom = ↾(classifyCylinder X n) :=
  (componentPushout X n).inl_isoIsPushout_hom _ _ (IsPushout.of_isColimit (componentIsColimit X n))

/-- Reading the original apex through the component isomorphism is its identical apex simplex. -/
theorem apex_componentIso (X : SSet.{u}) (n : ℕ) :
    (apex X).app (op ⦋n⦌) ≫ (componentIso X n).hom =
      ↾(Sum.inr : (Δ[0] : SSet.{u}) _⦋n⦌ → Component X n) :=
  (componentPushout X n).inr_isoIsPushout_hom _ _ (IsPushout.of_isColimit (componentIsColimit X n))

end SSet.WalkingAdjunction.FatCone
