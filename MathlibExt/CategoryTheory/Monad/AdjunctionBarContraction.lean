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
# Extra degeneracy after applying the right adjoint to a bar construction

Let F : C → D and U : D → C be an adjunction F ⊣ U, with monad T=UF, and let Y ∈ D. Applying U
to its augmented adjunction bar gives an augmented simplicial object of C with term
U(F(T^n(UY))) in degree n and augmentation U(ε_Y) to UY.

This object has a left extra degeneracy. Its augmentation section is η_{UY}, and the higher
maps insert the outer monad unit, with the canonical successor-iterate identification. The
unit followed by the forgotten counit is the identity by the adjunction triangle equation. No
monadicity or additive-category hypothesis is required.
-/

@[expose] public section

noncomputable section

universe vC vD uC uD
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.Monad.AdjunctionBarContraction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) (Y : D)

/-- Let F : C ⥤ D, U : D ⥤ C, adj : F ⊣ U, and Y ∈ D, with arbitrary independent category
universes. Evaluate the augmented adjunction bar at Y and apply U to obtain an augmented
simplicial object of C. For T=adj.toMonad=UF, its degree-n term is U(F(T^n(UY))) and its
augmentation target is UY. Its degree-zero augmentation is U(ε_Y). -/
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

/-- For an adjunction F : C ⥤ D, U : D ⥤ C with F ⊣ U and Y ∈ D, the augmentation target of the
bar evaluated at Y and then acted on by U is exactly U(Y). This is the right object of the
resulting augmented simplicial object of C. -/
theorem forgotten_point : (forgotten adj Y).right = U.obj Y := rfl

/-- Let F ⊣ U be an adjunction between categories C and D, T=UF its monad, Y ∈ D, and n ∈ ℕ. The
degree-n simplicial term of the evaluated bar after applying U equals U(F(T^n(UY))). Here T^n
is monadPow(adj.toMonad,n), with the zero power equal to the identity functor. -/
theorem forgotten_obj (n : ℕ) : (forgotten adj Y).left.obj (op ⦋n⦌) =
    U.obj (F.obj ((monadPow adj.toMonad n).obj (U.obj Y))) := rfl

/-- For an adjunction F : C ⥤ D, U : D ⥤ C and Y ∈ D, the degree-zero augmentation of the
forgotten bar is U(ε_Y) : U(F(UY)) → UY. The counit ε_Y is that of the given adjunction, and
the simplicial degree is zero. -/
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

/-- Let F ⊣ U be an adjunction, T=UF its monad, Y ∈ D, and B the evaluated adjunction bar after
applying U. There is a left extra degeneracy on B. Its augmentation section B_{−1}=UY → B_0 is
η_{UY}; its map B_n → B_{n+1} is η_{B_n} followed by the canonical identification
T(B_n)≅B_{n+1}. These maps satisfy the extra-degeneracy augmentation, face, and degeneracy
equations, with distinguished face d_0. -/
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

/-- For an adjunction F ⊣ U and Y ∈ D, the section of the forgotten augmented bar supplied by its
outer-unit extra degeneracy is exactly η_{UY} : UY → U(F(UY)). The target is its degree-zero
term and the source is its augmentation target. -/
theorem extra_section : (extra adj Y).s' = adj.unit.app (U.obj Y) := rfl

/-- Let F ⊣ U be an adjunction and Y ∈ D. The unit at UY followed by the degree-zero forgotten bar
augmentation satisfies η_{UY} ≫ U(ε_Y) = 𝟙_{UY}. Thus the augmentation U(F(UY)) → UY is split
by the unit, as prescribed by the adjunction triangle identity. -/
theorem extra_section_augmentation :
    adj.unit.app (U.obj Y) ≫ (forgotten adj Y).hom.app (op ⦋0⦌) = 𝟙 (U.obj Y) :=
  (extra adj Y).s'_comp_ε

end CategoryTheory.Monad.AdjunctionBarContraction
