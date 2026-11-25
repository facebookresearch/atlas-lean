/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Actual pushouts and coproducts of Arrow retracts

The constructors preserve each original Arrow component and its splitting.
They give cobase-change and coproduct closure of retracts for any morphism
property with the corresponding original closure, without small-object data.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w u v

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type u} [Category.{v} C]

/-- Retracts of retracts retain the same final representative and compose their actual maps. -/
instance retractsIsStableUnderRetracts (P : MorphismProperty C) :
    P.retracts.IsStableUnderRetracts where
  of_retract R hf := by
    obtain ⟨A, B, g, S, hg⟩ := hf
    exact ⟨A, B, g, R.trans S, hg⟩

/-- The actual coproduct of a family of original Arrow retracts. -/
def coproductRetract {I : Type w} [HasColimitsOfShape (Discrete I) C]
    {A B U V : I → C} {f : ∀ i, A i ⟶ B i} {g : ∀ i, U i ⟶ V i}
    (R : ∀ i, RetractArrow (f i) (g i)) :
    RetractArrow (Limits.Sigma.map f) (Limits.Sigma.map g) where
  i := Arrow.homMk (Limits.Sigma.map (fun i => (R i).i.left))
    (Limits.Sigma.map (fun i => (R i).i.right)) (by
      change Limits.Sigma.map (fun i => (R i).i.left) ≫ Limits.Sigma.map g =
        Limits.Sigma.map f ≫ Limits.Sigma.map (fun i => (R i).i.right)
      rw [Limits.Sigma.map_comp_map, Limits.Sigma.map_comp_map]
      congr 1
      funext i
      exact (R i).i_w)
  r := Arrow.homMk (Limits.Sigma.map (fun i => (R i).r.left))
    (Limits.Sigma.map (fun i => (R i).r.right)) (by
      change Limits.Sigma.map (fun i => (R i).r.left) ≫ Limits.Sigma.map f =
        Limits.Sigma.map g ≫ Limits.Sigma.map (fun i => (R i).r.right)
      rw [Limits.Sigma.map_comp_map, Limits.Sigma.map_comp_map]
      congr 1
      funext i
      exact (R i).r_w)
  retract := by
    ext
    · change Limits.Sigma.map (fun i => (R i).i.left) ≫
        Limits.Sigma.map (fun i => (R i).r.left) = 𝟙 _
      rw [Limits.Sigma.map_comp_map]
      simp only [RetractArrow.retract_left]
      exact Limits.Sigma.map_id (f := A)
    · change Limits.Sigma.map (fun i => (R i).i.right) ≫
        Limits.Sigma.map (fun i => (R i).r.right) = 𝟙 _
      rw [Limits.Sigma.map_comp_map]
      simp only [RetractArrow.retract_right]
      exact Limits.Sigma.map_id (f := B)

/-- Pushout of an original Arrow retract, with both new source maps equal to the identity. -/
def pushoutRetract {A B U V X : C} {f : A ⟶ B} {g : U ⟶ V}
    (R : RetractArrow f g) (a : A ⟶ X)
    [HasPushout f a] [HasPushout g (R.r.left ≫ a)] :
    RetractArrow (pushout.inr f a) (pushout.inr g (R.r.left ≫ a)) := by
  let i : pushout f a ⟶ pushout g (R.r.left ≫ a) :=
    pushout.desc ((R.i.right) ≫ pushout.inl g (R.r.left ≫ a))
      (pushout.inr g (R.r.left ≫ a)) (by
        rw [← R.i_w_assoc, pushout.condition, ← Category.assoc,
          R.retract_left_assoc]
        exact congrArg (fun h : A ⟶ X => h ≫ pushout.inr g (R.r.left ≫ a))
          (Category.id_comp a))
  let r : pushout g (R.r.left ≫ a) ⟶ pushout f a :=
    pushout.desc ((R.r.right) ≫ pushout.inl f a) (pushout.inr f a) (by
      rw [← R.r_w_assoc, Category.assoc, pushout.condition])
  exact
    { i := Arrow.homMk (𝟙 X) i (by simp [i])
      r := Arrow.homMk (𝟙 X) r (by simp [r])
      retract := by
        ext
        · simp
        · apply pushout.hom_ext
          · simp [i, r, Category.assoc]
          · simp [i, r] }

/-- Actual pushout maps of representatives prove cobase stability of the retract class. -/
theorem retractsIsStableUnderCobaseChange (P : MorphismProperty C)
    [P.IsStableUnderCobaseChange] [HasPushouts C] :
    P.retracts.IsStableUnderCobaseChange :=
  .mk' (fun _ _ _ f a _ hf => by
    obtain ⟨U, V, g, R, hg⟩ := hf
    exact ⟨_, _, _, pushoutRetract R a, P.pushout_inr g (R.r.left ≫ a) hg⟩)

/-- Actual coproduct maps of representatives prove coproduct stability of retracts. -/
theorem retractsIsStableUnderCoproducts (P : MorphismProperty C)
    [P.IsStableUnderCoproducts.{w}] [HasCoproducts.{w} C] :
    P.retracts.IsStableUnderCoproducts.{w} := by
  refine ⟨fun I => ?_⟩
  exact .mk P.retracts I (fun A B _ _ f hf => by
    classical
    choose U V g R hg using hf
    have hgSum : P (Limits.Sigma.map g) := by
      let τ : Discrete.functor U ⟶ Discrete.functor V :=
        Discrete.natTrans (fun i => g i.as)
      change P (colimMap τ)
      exact MorphismProperty.colimMap (W := P) τ (fun i => hg i.as)
    exact ⟨_, _, Limits.Sigma.map g, coproductRetract R, hgSum⟩)

end CategoryTheory.MorphismProperty
