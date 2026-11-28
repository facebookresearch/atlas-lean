/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.Limits.Shapes.DiscreteCofree
import MathlibExt.CategoryTheory.Limits.Shapes.SequentialCofree
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Cofree diagram coordinates and limit comparisons

These clients retain distinct parallel arrows in the outgoing product index
and evaluate unit and transition coordinates on nonconstant diagrams. They
also check cancellation by the monic unit, the separate global limit
comparison, and the finite-products hypothesis for inverse sequences.
-/

noncomputable section

open CategoryTheory Limits Opposite

universe v₁ v₂ u₁ u₂

namespace DiscreteCofreeTests

/-- Distinct parallel arrows remain distinct points of the outgoing slice. -/
example :
    (discreteCofreeIndexEquivalence WalkingParallelPair.zero).functor.obj
        (Discrete.mk (⟨WalkingParallelPair.one, WalkingParallelPairHom.left⟩ :
          discreteCofreeIndex WalkingParallelPair.zero)) ≠
      (discreteCofreeIndexEquivalence WalkingParallelPair.zero).functor.obj
        (Discrete.mk (⟨WalkingParallelPair.one, WalkingParallelPairHom.right⟩ :
          discreteCofreeIndex WalkingParallelPair.zero)) := by
  have hd : (⟨WalkingParallelPair.one, WalkingParallelPairHom.left⟩ :
      discreteCofreeIndex WalkingParallelPair.zero) ≠
      ⟨WalkingParallelPair.one, WalkingParallelPairHom.right⟩ := by
    intro h
    have hf : (WalkingParallelPairHom.left :
        WalkingParallelPair.zero ⟶ WalkingParallelPair.one) =
        WalkingParallelPairHom.right := eq_of_heq (Sigma.mk.inj h).2
    cases hf
  intro h
  have hi := congrArg
    (fun x : StructuredArrow WalkingParallelPair.zero
        (discreteCofreeInclusion WalkingParallelPair) ↦
      (discreteCofreeArrowToIndex WalkingParallelPair.zero).obj x) h
  exact hd (congrArg Discrete.as hi)

section SizedProducts

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [HasProducts.{max u₁ v₁} A]

/-- A coordinate of the actual unit is a nonconstant diagram's actual structure map. -/
example (M : I ⥤ A) {i j : I} (f : i ⟶ j) :
    ((discreteCofreeUnit (I := I) A).app M).app i ≫
        (discreteCofreeObjIso A (discreteCofreeInclusion I ⋙ M) i).hom ≫
          Pi.π _ (⟨j, f⟩ : discreteCofreeIndex i) = M.map f := by
  fail_if_success
    have : HasZeroMorphisms A := inferInstance
  rw [discreteCofreeObjIso_hom_π, discreteCofreeUnit_app_π]

/-- Actual transition maps precompose the retained outgoing coordinate. -/
example (V : Discrete I ⥤ A) {i i' j : I} (g : i ⟶ i') (f : i' ⟶ j) :
    ((discreteCofreeFunctor (I := I) A).obj V).map g ≫
        (discreteCofreeObjIso A V i').hom ≫ Pi.π _ (⟨j, f⟩ : discreteCofreeIndex i') =
      (discreteCofreeObjIso A V i).hom ≫
        Pi.π _ (⟨j, g ≫ f⟩ : discreteCofreeIndex i) := by
  simpa only [discreteCofreeObjIso_hom_π] using
    discreteCofree_transition_π A V g (⟨j, f⟩ : discreteCofreeIndex i')

/-- The native faithful-left-adjoint theorem permits cancellation of the actual unit. -/
example {M N : I ⥤ A} (u v : M ⟶ N)
    (h : u ≫ (discreteCofreeUnit (I := I) A).app N =
      v ≫ (discreteCofreeUnit (I := I) A).app N) : u = v :=
  (cancel_mono ((discreteCofreeUnit (I := I) A).app N)).1 h

end SizedProducts

section GlobalLimit

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A]
  [∀ V : Discrete I ⥤ A,
    Functor.HasRightKanExtension (discreteCofreeInclusion I) V]
  [HasLimitsOfShape I A] [HasProductsOfShape I A]

/-- The separate global comparison has the actual native limit/counit projection. -/
example (V : Discrete I ⥤ A) (j : I) :
    (discreteCofreeLimitIso A V).hom ≫ Pi.π _ j =
      limit.π ((discreteCofreeFunctor (I := I) A).obj V) j ≫
        ((discreteCofreeInclusion I).ranCounit.app V).app (Discrete.mk j) :=
  discreteCofreeLimitIso_hom_π A V j

end GlobalLimit

section SequentialBoundary

variable {A : Type u₂} [Category.{v₂} A] [HasFiniteProducts A]

/-- Finite products provide right Kan extensions along the discrete inclusion of ℕᵒᵖ, as required
by the general cofree formulas. -/
local instance sequentialRightKanExtensionsForClient :
    ∀ V : Discrete ℕᵒᵖ ⥤ A,
      Functor.HasRightKanExtension (discreteCofreeInclusion ℕᵒᵖ) V := by
  intro V
  have : Functor.HasPointwiseRightKanExtension sequentialDiscreteInclusion V :=
    sequentialDiscreteHasPointwiseRightKanExtension A V
  change Functor.HasRightKanExtension sequentialDiscreteInclusion V
  infer_instance

/-- The existing sequential availability needs only finite products in this general formula. -/
example (M : ℕᵒᵖ ⥤ A) (n m : ℕ) (hm : m ≤ n) :
    ((discreteCofreeUnit (I := ℕᵒᵖ) A).app M).app (op n) ≫
        discreteCofreeπ A (discreteCofreeInclusion ℕᵒᵖ ⋙ M) (op n)
          ⟨op m, (homOfLE hm).op⟩ = M.map ((homOfLE hm).op) :=
  discreteCofreeUnit_app_π A M (op n) ⟨op m, (homOfLE hm).op⟩

end SequentialBoundary

end DiscreteCofreeTests

end
