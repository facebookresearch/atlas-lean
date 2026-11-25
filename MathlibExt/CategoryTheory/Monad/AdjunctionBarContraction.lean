/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monad.BarAdjunction
public import MathlibExt.CategoryTheory.Monad.BarRegularContraction

/-!
# The actual forgetful extra degeneracy of an adjunction bar

For an arbitrary adjunction, applying the original right adjoint to its
augmented bar gives the regular-right bar of the induced monad. The actual
regular contraction therefore supplies every extra-degeneracy equation for
that same forgotten bar. No monadicity or homotopical outcome is supplied.
-/

@[expose] public section

noncomputable section

universe vC vD uC uD
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.Monad.AdjunctionBarContraction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) (Y : D)

/-- Evaluate the actual adjunction bar at the supplied original target and then forget. -/
def forgotten : SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj (D ⥤ D) C
    ((evaluation D D).obj Y ⋙ U)).obj (adjAugmented adj)

private def regular : SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj (D ⥤ C) C
    ((evaluation D C).obj Y)).obj
      (BalancedPairing.toSimplicialAugmented
        (BarRegularContraction.regularBalancedPairing (adjLeftModule adj)))

private def regularExtra : (regular adj Y).ExtraDegeneracy :=
  (BarRegularContraction.extraDegeneracySimplicial (adjLeftModule adj)).map
    ((evaluation D C).obj Y)

/-- The original augmentation target is literally the forgotten original object. -/
theorem forgotten_point : (forgotten adj Y).right = U.obj Y := rfl

/-- Degree n retains the actual whole free/forget iterated object. -/
theorem forgotten_obj (n : ℕ) : (forgotten adj Y).left.obj (op ⦋n⦌) =
    U.obj (F.obj ((monadPow adj.toMonad n).obj (U.obj Y))) := rfl

/-- The zero-degree augmentation is the original right-adjoint image of the whole counit. -/
theorem forgotten_augmentation : (forgotten adj Y).hom.app (op ⦋0⦌) =
    U.map (adj.counit.app Y) := by
  unfold forgotten
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    adjAugmented_hom_zero]
  rfl

private theorem action_forget (n : ℕ) (X : C) :
    U.map (rightActionPow adj.toMonad (adjRightModule adj) n X) =
      rightActionPow adj.toMonad (RightModule.regular adj.toMonad) n X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih (adj.toMonad.obj X)

private theorem face_agreement {n : ℕ} (i : Fin (n + 2)) :
    (forgotten adj Y).left.δ i = (regular adj Y).left.δ i := by
  change U.map (((adjBar adj).map (SimplexCategory.δ i).op).app Y) =
    ((twoSidedBar adj.toMonad (RightModule.regular adj.toMonad) (adjLeftModule adj)).map
      (SimplexCategory.δ i).op).app Y
  rw [adjBar_map_δ_op_app, twoSidedBar_map_δ_op]
  change U.map (barFaceApp (T := adj.toMonad) (R := adjRightModule adj)
    (L := adjLeftModule adj) n i Y) =
      barFaceApp (T := adj.toMonad) (R := RightModule.regular adj.toMonad)
        (L := adjLeftModule adj) n i Y
  unfold barFaceApp
  split
  · exact action_forget adj n (U.obj Y)
  · split <;> rfl

private theorem degeneracy_agreement {n : ℕ} (i : Fin (n + 1)) :
    (forgotten adj Y).left.σ i = (regular adj Y).left.σ i := by
  change U.map (((adjBar adj).map (SimplexCategory.σ i).op).app Y) =
    ((twoSidedBar adj.toMonad (RightModule.regular adj.toMonad) (adjLeftModule adj)).map
      (SimplexCategory.σ i).op).app Y
  rw [adjBar_map_σ_op_app, twoSidedBar_map_σ_op]
  rfl

private theorem augmentation_agreement :
    (forgotten adj Y).hom.app (op ⦋0⦌) = (regular adj Y).hom.app (op ⦋0⦌) := by
  rw [forgotten_augmentation]
  unfold regular
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    BalancedPairing.toSimplicialAugmented_hom_app_mk]
  rfl

/-- The full genuine extra degeneracy on the actual forgotten adjunction bar. -/
def extra : (forgotten adj Y).ExtraDegeneracy where
  s' := adj.unit.app (U.obj Y)
  s n := (BarRegularContraction.extraDegeneracySimplicial (adjLeftModule adj)).s n |>.app Y
  s'_comp_ε := by
    rw [augmentation_agreement]
    exact (regularExtra adj Y).s'_comp_ε
  s₀_comp_δ₁ := by
    rw [face_agreement, augmentation_agreement]
    exact (regularExtra adj Y).s₀_comp_δ₁
  s_comp_δ₀ n := by
    rw [face_agreement]
    exact (regularExtra adj Y).s_comp_δ₀ n
  s_comp_δ n i := by
    rw [face_agreement, face_agreement]
    exact (regularExtra adj Y).s_comp_δ n i
  s_comp_σ n i := by
    rw [degeneracy_agreement, degeneracy_agreement]
    exact (regularExtra adj Y).s_comp_σ n i

/-- The augmentation section is the original adjunction unit, not a supplied inverse. -/
theorem extra_section : (extra adj Y).s' = adj.unit.app (U.obj Y) := rfl

/-- The actual original whole unit followed by the forgotten counit is identity. -/
theorem extra_section_augmentation :
    adj.unit.app (U.obj Y) ≫ (forgotten adj Y).hom.app (op ⦋0⦌) = 𝟙 (U.obj Y) :=
  (extra adj Y).s'_comp_ε

end CategoryTheory.Monad.AdjunctionBarContraction
