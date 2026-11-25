/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.SharpPullbackComparison
import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# Full base change of weak maps between original sharp objects

Both original projections are sharp. Replace only the supplied base
map by its actual original CM5 weak/fibration factorization. Sharpness
makes both original comparison maps weak; right properness makes the
same native intermediate map weak. The full original natural square
and cancellation detect the SAME unreplaced native pullback map.
-/

noncomputable section
universe u v
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.SharpOverWeakBaseChange

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The SAME whole original base-change comparison in the native over-pullback order. -/
def comparison {A B E : C} (b : A ⟶ B) (p : E ⟶ B)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) b) :
    pullback p b ⟶ pullback p h.p :=
  weakFibrationPullbackComparison (IsPullback.of_hasPullback p b).flip.toCommSq h ≫
    (pullbackSymmetry h.p p).hom

/-- Its full first projection is the original unreplaced total-space projection. -/
@[reassoc]
lemma comparison_fst {A B E : C} (b : A ⟶ B) (p : E ⟶ B)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) b) :
    comparison b p h ≫ pullback.fst p h.p = pullback.fst p b := by
  rw [comparison, Category.assoc, pullbackSymmetry_hom_comp_fst,
    weakFibrationPullbackComparison_snd]

/-- Its full second projection is the SAME original base projection followed by the actual CM5 unit.
-/
@[reassoc]
lemma comparison_snd {A B E : C} (b : A ⟶ B) (p : E ⟶ B)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) b) :
    comparison b p h ≫ pullback.snd p h.p = pullback.snd p b ≫ h.i := by
  rw [comparison, Category.assoc, pullbackSymmetry_hom_comp_snd,
    weakFibrationPullbackComparison_fst]

/-- Genuine original sharpness makes this SAME full comparison weak. -/
theorem comparison_weak {A B E : C} (b : A ⟶ B) (p : E ⟶ B)
    (hp : sharpMaps (weakEquivalences C) p)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) b) :
    weakEquivalences C (comparison b p h) :=
  (weakEquivalences C).comp_mem _ _
    (sharpMaps_weakFibrationPullbackComparison hp (IsPullback.of_hasPullback p b).flip h)
    (mem_weakEquivalences _)

/-- The actual native base-change square retains the SAME entire
original over-map and both original projections. -/
theorem comparison_natural {A B : C} (b : A ⟶ B) {X Y : Over B} (f : X ⟶ Y)
    (h : MapFactorizationData (weakEquivalences C) (fibrations C) b) :
    ((Over.pullback b).map f).left ≫ comparison b Y.hom h =
      comparison b X.hom h ≫ ((Over.pullback h.p).map f).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, comparison_fst, Over.pullback_map_left,
      pullback.lift_fst, comparison_fst_assoc]
  · simp only [Category.assoc, comparison_snd, Over.pullback_map_left,
      pullback.lift_snd, pullback.lift_snd_assoc]

/-- EVERY original base map preserves weak arrows between original
sharp objects through the SAME full native over-pullback functor. -/
theorem pullback_map_weak [IsRightProper C] {A B : C} (b : A ⟶ B)
    {X Y : Over B} (f : X ⟶ Y) (hf : weakEquivalences C f.left)
    (hX : sharpMaps (weakEquivalences C) X.hom)
    (hY : sharpMaps (weakEquivalences C) Y.hom) :
    weakEquivalences C ((Over.pullback b).map f).left := by
  let h := weakFibrationFactorization b
  let _ : Fibration h.p := (fibration_iff _).mpr h.hp
  let _ : Fibration (pullback.fst Y.hom h.p) := inferInstance
  let _ : WeakEquivalence f.left := (weakEquivalence_iff _).mpr hf
  have hm : weakEquivalences C ((Over.pullback h.p).map f).left :=
    (weakEquivalence_iff _).mp (IsRightProper.weakEquivalence_of_isPullback
      (MorphismProperty.overPullbackMap_isPullback h.p f).flip)
  apply (weakEquivalences C).of_postcomp _ _ (comparison_weak b Y.hom hY h)
  rw [comparison_natural]
  exact (weakEquivalences C).comp_mem _ _ (comparison_weak b X.hom hX h) hm

end HomotopicalAlgebra.SharpOverWeakBaseChange
