/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedZeroFiberNerveEquivalence
public import MathlibExt.KTheory.Exact.Extension.LocalizedFiberLeftCommaWeakEquivalence
public import MathlibExt.KTheory.Exact.Extension.ProjectiveAuxiliaryRealizationConull
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaQuillenB

/-!
# The original completed core and the full zero homotopy fiber

The actual zero-row equivalence maps the completed core into the strict fiber
of the original localized target. Its Cartesian inclusion maps into the
left comma, and the original opposite-path Quillen-B comparison maps into
the full compact-open homotopy fiber. Original auxiliary terminal weakness
supplies every Q-span transition. The ring theorem derives those antecedents.

Every original core pair, denominator, Q arrow and carried path is retained.
The selected unit has its literal total-space coordinate. This weak comparison
does not assert a homotopy inverse or replace the original K0 components.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

universe u v uRing vModule

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- The original zero-fiber equivalence followed by its actual Cartesian comma inclusion. -/
def completedCoreToZeroLeftCommaNerveMap :
    (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}) ⟶
      (nerve (StructuredArrow (⟨0⟩ : QuillenQ C)
        (ExtensionCategory.localizedTarget (C := C))) : SSet.{max u v}) :=
  nerveMapCommonHomUp.{u, max u v, 0}
      (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)) ≫
    nerveMap (Functor.fiberToStructuredArrow
      (p := ExtensionCategory.localizedTarget (C := C)) (⟨0⟩ : QuillenQ C))

/-- Projection retains the original zero-row functor on every full chain and denominator. -/
theorem completedCoreToZeroLeftCommaNerveMap_proj :
    completedCoreToZeroLeftCommaNerveMap (C := C) ≫
        nerveMap (StructuredArrow.proj (⟨0⟩ : QuillenQ C)
          (ExtensionCategory.localizedTarget (C := C))) =
      nerveMapCommonHomUp.{u, max u v, 0}
        (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedForget (C := C) (0 : C)) := by
  unfold completedCoreToZeroLeftCommaNerveMap
  rw [Category.assoc, nerveMap_comp, nerveMapCommonHomUp_nerveMap_comp.{u, max u v, 0}]
  rfl

/-- The zero equivalence and the actual Cartesian adjunction derive this route's weakness. -/
theorem completedCoreToZeroLeftCommaNerveMap_mem :
    SSet.realizationWeakEquivalences (completedCoreToZeroLeftCommaNerveMap (C := C)) := by
  have hZero :=
    FixedTargetExtension.completedCoreToZeroFiberNerveMap_mem_realizationWeakEquivalences
      (C := C)
  have hComma : SSet.realizationWeakEquivalences
      (nerveMap (Functor.fiberToStructuredArrow
        (p := ExtensionCategory.localizedTarget (C := C)) (⟨0⟩ : QuillenQ C))) :=
    Functor.IsPreFibered.fiberToStructuredArrow_mem_realizationWeakEquivalences.{
      u, max u v} (p := ExtensionCategory.localizedTarget (C := C)) (⟨0⟩ : QuillenQ C)
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hZero hComma

/-- The actual completed-core route carries the original left-comma full path into the fiber. -/
def completedCoreToOriginalHomotopyFiber :
    SSet.toTop.obj (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}) ⟶
      TopCat.homotopyFiber
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C))) :=
  SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C)) ≫
    SSet.leftCommaHomotopyFiberComparison.{u, 0, max u v}
      (ExtensionCategory.localizedTarget (C := C)) (⟨0⟩ : QuillenQ C)

/-- Only original auxiliary terminal weakness is needed for the actual K-to-fiber comparison. -/
theorem completedCoreToOriginalHomotopyFiber_mem_of_originalBases_conull
    (hBase : ∀ X : C, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) :
    TopCat.weakHomotopyEquivalences (completedCoreToOriginalHomotopyFiber (C := C)) := by
  have hTransitions : ∀ (R S : QuillenQ C) (f : R ⟶ S),
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (nerveMap (StructuredArrow.map
          (T := ExtensionCategory.localizedTarget (C := C)) f))) := by
    intro R S f
    exact LocalizedBaseChange.leftCommaTransitionNerveMap_mem_of_originalBases_conull hBase f
  have hComparison := SSet.leftCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences.{
    u, 0, max u v} (ExtensionCategory.localizedTarget (C := C)) hTransitions
      (⟨0⟩ : QuillenQ C)
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _
    (completedCoreToZeroLeftCommaNerveMap_mem (C := C)) hComparison

/-- Every associative unital ring derives the antecedents from its original auxiliary bases. -/
theorem projectiveCompletedCoreToOriginalHomotopyFiber_mem {R : Type uRing} [Ring R] :
    TopCat.weakHomotopyEquivalences
      (completedCoreToOriginalHomotopyFiber (C := FGProjectiveCat.{vModule} R)) := by
  have hBase : ∀ X : FGProjectiveCat.{vModule} R, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core (FGProjectiveCat.{vModule} R))
          (FixedTargetExtension (FGProjectiveCat.{vModule} R) X)) :
            SSet.{max uRing (vModule + 1)}))) := by
    intro X
    exact AuxiliaryExtension.projectiveAuxiliary_realization_conull X
  exact completedCoreToOriginalHomotopyFiber_mem_of_originalBases_conull
    (C := FGProjectiveCat.{vModule} R) hBase

/-- The entire total coordinate is the original zero-row inclusion, without changing any pair. -/
theorem completedCoreToOriginalHomotopyFiber_toTotal :
    completedCoreToOriginalHomotopyFiber (C := C) ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map
            (nerveMapCommonHom.{u, max u v, 0}
              (ExtensionCategory.localizedTarget (C := C))))
          (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
            (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C))) =
      SSet.toTop.map (nerveMapCommonHomUp.{u, max u v, 0}
        (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedForget (C := C) (0 : C))) := by
  unfold completedCoreToOriginalHomotopyFiber
  rw [Category.assoc, SSet.leftCommaHomotopyFiberComparison_toTotal.{u, 0, max u v}]
  rw [nerveMapCommonHom_eq_nerveMap.{max u v, 0, max u v}]
  rw [← SSet.toTop.map_comp, completedCoreToZeroLeftCommaNerveMap_proj]

/-- At every original core pair, the total point is the actual zero-row image of that pair. -/
theorem completedCoreToOriginalHomotopyFiber_toTotal_vertex
    (a : SInverse (Core C) (Core C)) :
    TopCat.homotopyFiberToTotal
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)))
        (completedCoreToOriginalHomotopyFiber (C := C)
          (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀ a))) =
      SSet.realizedVertex
        (ComposableArrows.mk₀ ((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedForget (C := C) (0 : C)).obj a)) := by
  have hTotal := ConcreteCategory.congr_hom
    (completedCoreToOriginalHomotopyFiber_toTotal (C := C))
    (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
      (ComposableArrows.mk₀ a))
  have hVertex := (SSet.realizedVertex_naturality
    (nerveMapCommonHomUp.{u, max u v, 0}
      (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedForget (C := C) (0 : C)))
    (ComposableArrows.mk₀ a)).symm
  rw [nerveMapCommonHomUp_app_mk₀] at hVertex
  exact hTotal.trans hVertex

/-- The original completed tensor unit retains its original realized total-unit coordinate. -/
theorem completedCoreToOriginalHomotopyFiber_unit_toTotal :
    TopCat.homotopyFiberToTotal
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)))
        (completedCoreToOriginalHomotopyFiber (C := C)
          (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀ ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))))) =
      SSet.realizedVertex
        (ComposableArrows.mk₀ ((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedForget (C := C) (0 : C)).obj
            ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))) :=
  completedCoreToOriginalHomotopyFiber_toTotal_vertex
    ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))

/-- Every time of the carried path is the actual opposite right-comma path transported back. -/
theorem completedCoreToOriginalHomotopyFiber_path_apply
    (z : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
    (t : TopCat.I.{max u v}) :
    TopCat.homotopyFiberPath
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)))
        (completedCoreToOriginalHomotopyFiber (C := C) z) t =
      (SSet.nerveRealizationOppositeIso (QuillenQ C)).hom
        (TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C)).op))
          (SSet.realizedVertex (X := (nerve (QuillenQ C)ᵒᵖ : SSet.{max u v}))
            (ComposableArrows.mk₀ (op (⟨0⟩ : QuillenQ C))))
          (SSet.rightCommaHomotopyFiberComparison.{u, 0, max u v}
            (ExtensionCategory.localizedTarget (C := C)).op (op (⟨0⟩ : QuillenQ C))
            ((SSet.leftCommaRealizationIso.{u, 0, max u v}
              (ExtensionCategory.localizedTarget (C := C)) (op (⟨0⟩ : QuillenQ C))).hom
              (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C)) z))) t) := by
  exact SSet.leftCommaHomotopyFiberComparison_path_apply.{u, 0, max u v}
    (ExtensionCategory.localizedTarget (C := C)) (⟨0⟩ : QuillenQ C)
    (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C)) z) t

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# Whole original comma and full-path fiber recipes

Proper owned values retain both full original forward maps. The original
carried homotopy-fiber path and root are not reconstructed from projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] AlgebraicKTheory.ExtensionCategory.localizedTarget_isFibered

universe uZeroRecipe vZeroRecipe

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type uZeroRecipe} [Category.{vZeroRecipe} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem originalCompletedCoreZeroCommaWholeRecipe :
    completedCoreToZeroLeftCommaNerveMap (C := C) =
      nerveMapCommonHomUp.{uZeroRecipe, max uZeroRecipe vZeroRecipe, 0}
          (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
            FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)) ≫
        nerveMap (Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) := rfl

/-- The SAME whole original zero-comma map retains both of its actual original functor legs. -/
public theorem completedCoreToZeroLeftCommaNerveMap_value :
    completedCoreToZeroLeftCommaNerveMap (C := C) =
      nerveMapCommonHomUp.{uZeroRecipe, max uZeroRecipe vZeroRecipe, 0}
          (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
            FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)) ≫
        nerveMap (Functor.fiberToStructuredArrow
          (p := ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C)) :=
  originalCompletedCoreZeroCommaWholeRecipe (C := C)

private theorem originalCompletedCoreFullFiberWholeRecipe :
    completedCoreToOriginalHomotopyFiber (C := C) =
      SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C)) ≫
        SSet.leftCommaHomotopyFiberComparison.{uZeroRecipe, 0, max uZeroRecipe vZeroRecipe}
          (ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C) := rfl

/-- The SAME full original homotopy-fiber map retains the whole comparison and carried path. -/
public theorem completedCoreToOriginalHomotopyFiber_value :
    completedCoreToOriginalHomotopyFiber (C := C) =
      SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C)) ≫
        SSet.leftCommaHomotopyFiberComparison.{uZeroRecipe, 0, max uZeroRecipe vZeroRecipe}
          (ExtensionCategory.localizedTarget (C := C)) (⟨(0 : C)⟩ : QuillenQ C) :=
  originalCompletedCoreFullFiberWholeRecipe (C := C)

end AlgebraicKTheory.OriginalQZeroComparison

end
